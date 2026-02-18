use {
    crate::io::{ReadResult, Reader, read_size_limit, slice::SliceUnchecked},
    std::{
        io::{BufRead, BufReader, ErrorKind, Read},
        mem::{MaybeUninit, transmute},
        num::NonZeroUsize,
    },
};

/// [`Reader`] implementation over any [`BufRead`] source.
///
/// Wraps any `R: std::io::BufRead` and exposes it as a wincode [`Reader`], enabling
/// deserialization from files, network streams, or other buffered I/O sources. For
/// unbuffered [`std::io::Read`] sources use [`BufReadAdapter::from_read`], which
/// wraps the source in a [`std::io::BufReader`] automatically.
///
/// # Examples
///
/// Deserialize a tuple from a byte slice using `BufReadAdapter`:
///
/// ```
/// use wincode::{DeserializeOwned, io::std_read::BufReadAdapter};
///
/// let bytes = wincode::serialize(&(42u32, true, 1234567890i64)).unwrap();
/// let mut reader = BufReadAdapter::new(bytes.as_slice());
/// let result: (u32, bool, i64) = <(u32, bool, i64)>::deserialize_from(reader).unwrap();
/// assert_eq!(result, (42u32, true, 1234567890i64));
/// ```
pub struct BufReadAdapter<R> {
    reader: R,
    consume_state: ConsumeState,
    /// Helper buffer used by the `take_scoped` fallback path when the slice returned by
    /// internal `fill_buf` is smaller than the requested length.
    aux_buf: Vec<u8>,
}

impl<R: BufRead> BufReadAdapter<R> {
    pub fn new(reader: R) -> Self {
        Self {
            reader,
            consume_state: ConsumeState::Direct,
            aux_buf: vec![],
        }
    }

    /// Flush any pending consume and return the next available data slice.
    fn flush_consume_and_fill_buf(&mut self) -> std::io::Result<&[u8]> {
        match &self.consume_state {
            ConsumeState::Direct => self.reader.fill_buf(),
            ConsumeState::PendingConsumed(n) => {
                self.reader.consume(n.get());
                self.consume_state = ConsumeState::Direct;
                self.reader.fill_buf()
            }
        }
    }

    /// Flush any pending consume and determine whether getting contiguous data of `len` bytes
    /// should use the aux buffer.
    ///
    /// - `None` — can use reader's internal buffer that holds at least `len` bytes
    /// - `Some(range)` — aux path needed;
    ///   - `range` is the already-filled portion of `aux_buf` (`UnconsumedAux` state), or
    ///   - `0..0` if `aux_buf` is empty, but the reader buffer has less than `len` bytes
    fn flush_consume_and_check_aux_needed(&mut self, len: NonZeroUsize) -> std::io::Result<bool> {
        match &self.consume_state {
            ConsumeState::Direct => Ok(self.reader.fill_buf()?.len() < len.get()),
            ConsumeState::PendingConsumed(n) => {
                self.reader.consume(n.get());
                self.consume_state = ConsumeState::Direct;
                Ok(self.reader.fill_buf()?.len() < len.get())
            }
        }
    }

    /// Return a contiguous slice of exactly `len` bytes, reading ahead into `aux_buf` if needed.
    ///
    /// If `consume` is true the returned bytes are logically consumed and subsequent reads will
    /// start after them. If false, the bytes remain available so the caller can inspect them
    /// before deciding whether to consume.
    fn obtain_contiguous(&mut self, len: NonZeroUsize) -> ReadResult<&[u8]> {
        if !self.flush_consume_and_check_aux_needed(len)? {
            // `filled_aux_range=None` indicates that fill_buf returns large enough slice
            self.consume_state = ConsumeState::PendingConsumed(len);
            return Ok(&self.reader.fill_buf()?[..len.get()]);
        };
        let use_aux_range = 0..len.get();
        self.aux_buf.resize(use_aux_range.end, 0);
        match self
            .reader
            .read_exact(&mut self.aux_buf[0..use_aux_range.end])
        {
            Ok(()) => {
                self.consume_state = ConsumeState::Direct;
                Ok(&self.aux_buf[use_aux_range])
            }
            Err(err) if err.kind() == ErrorKind::UnexpectedEof => Err(read_size_limit(len.get())),
            Err(err) => Err(err.into()),
        }
    }

    fn consume(&mut self, amt: usize) {
        if let Some(n) = self.consume_state.advance_get_reader_consume(amt) {
            self.reader.consume(n.get());
        }
    }
}

impl<R: Read> BufReadAdapter<BufReader<R>> {
    pub fn from_read_with_capacity(r: R, capacity: usize) -> Self {
        Self::new(BufReader::with_capacity(capacity, r))
    }

    pub fn from_read(r: R) -> Self {
        Self::new(BufReader::new(r))
    }
}

impl<'a, R: BufRead> Reader<'a> for BufReadAdapter<R> {
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        // SAFETY: we only do writes to `dst` and never read uninitialized bytes.
        // `MaybeUninit<u8>` and `u8` have identical layout.
        let mut dst: &mut [u8] = unsafe { transmute(dst) };

        if !self.consume_state.is_direct() {
            let buf = self.flush_consume_and_fill_buf()?;
            let to_copy = buf.len().min(dst.len());
            let (copy_dst, rest_dst) = dst.split_at_mut(to_copy);
            copy_dst.copy_from_slice(&buf[..to_copy]);
            self.consume(to_copy);
            if rest_dst.is_empty() {
                return Ok(());
            }
            dst = rest_dst;
        }

        // If above didn't write enough then consume state is `Direct`, use `read_exact` such that
        // reader can do a direct copy into `dst` possibly skipping intermediate buffering.
        match self.reader.read_exact(dst) {
            Ok(()) => Ok(()),
            Err(err) if err.kind() == ErrorKind::UnexpectedEof => Err(read_size_limit(dst.len())),
            Err(err) => Err(err.into()),
        }
    }

    fn take_byte(&mut self) -> ReadResult<u8> {
        let buf = self.flush_consume_and_fill_buf()?;
        if let Some(&byte) = buf.first() {
            self.consume(1);
            Ok(byte)
        } else {
            Err(read_size_limit(1))
        }
    }

    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        let Some(len) = NonZeroUsize::new(len) else {
            return Ok(&[]);
        };
        self.obtain_contiguous(len)
    }

    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        let Some(n_bytes) = NonZeroUsize::new(n_bytes) else {
            return Ok(TrustedBufReader::Slice(unsafe { SliceUnchecked::new(&[]) }));
        };
        // Turn reader's buf into unchecked slice opportunistically. Trusted reader doesn't
        // strictly require contiguous memory - allocating and copying into aux would yield
        // unnecessary cost.
        let use_reader_buf = !self.flush_consume_and_check_aux_needed(n_bytes)?;
        let trusted = if use_reader_buf {
            // actual consume from `R` needs to happen *after* we no longer use `buf`
            self.consume_state = ConsumeState::PendingConsumed(n_bytes);
            let buf = self.reader.fill_buf()?;
            let slice_reader = unsafe { SliceUnchecked::new(&buf[..n_bytes.get()]) };
            TrustedBufReader::Slice(slice_reader)
        } else {
            // Fallback to self forwarding
            TrustedBufReader::Reader(self)
        };
        Ok(trusted)
    }
}

/// Tracks deferred consume of bytes and source buffer for next fill_buf
enum ConsumeState {
    /// No pending state, data should be obtained from `reader` directly.
    Direct,
    /// `n` bytes sit in the reader's internal buffer and have been
    /// logically consumed but not yet physically consumed via [`BufRead::consume`].
    /// Flushed at the start of the next operation.
    PendingConsumed(NonZeroUsize),
}

impl ConsumeState {
    fn is_direct(&self) -> bool {
        matches!(self, Self::Direct)
    }

    /// Advance the state by `amt` bytes, returning any amount that must still
    /// be forwarded to the underlying reader via [`BufRead::consume`].
    #[must_use]
    fn advance_get_reader_consume(&mut self, amt: usize) -> Option<NonZeroUsize> {
        match self {
            Self::PendingConsumed(n) => {
                let total = n.saturating_add(amt);
                *self = Self::Direct;
                Some(total)
            }
            Self::Direct => NonZeroUsize::new(amt),
        }
    }
}

/// Return type of [`BufReadAdapter::as_trusted_for`]: either a zero-copy slice into the reader's
/// internal buffer, or a forwarding reference to the reader itself when the buffer is too small.
enum TrustedBufReader<'s, R> {
    Slice(SliceUnchecked<'s, u8>),
    Reader(&'s mut BufReadAdapter<R>),
}

impl<'a, 's, R: BufRead> Reader<'a> for TrustedBufReader<'s, R> {
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        match self {
            Self::Slice(slice) => slice.copy_into_slice(dst),
            Self::Reader(reader) => reader.copy_into_slice(dst),
        }
    }

    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        match self {
            Self::Slice(slice) => slice.take_array(),
            Self::Reader(reader) => reader.take_array(),
        }
    }

    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        match self {
            Self::Slice(slice) => slice.take_scoped(len),
            Self::Reader(reader) => reader.take_scoped(len),
        }
    }
}

#[expect(clippy::arithmetic_side_effects)]
#[cfg(test)]
mod tests {
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};

    #[test]
    fn copy_into_slice_copies_and_advances() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReadAdapter::new(bytes.as_slice());
            let mut dst = Box::<[u8]>::new_uninit_slice(bytes.len());
            reader.copy_into_slice(&mut dst).unwrap();
            let dst = unsafe { dst.assume_init() };
            prop_assert_eq!(&dst[..], bytes.as_slice());
            prop_assert!(reader.take_byte().is_err());
        });
    }

    #[test]
    fn copy_into_slice_errors_when_insufficient() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReadAdapter::new(bytes.as_slice());
            let mut dst = Box::<[u8]>::new_uninit_slice(bytes.len() + 1);
            let result = reader.copy_into_slice(&mut dst);
            prop_assert!(result.is_err());
        });
    }

    #[test]
    fn copy_into_slice_direct_read() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            // BufRead capacity is limited, so filling `dst` requires using `read` or multiple `fill_buf`s
            let mut reader = BufReadAdapter::from_read_with_capacity(bytes.as_slice(), bytes.len().div_ceil(2));
            let mut dst = Box::<[u8]>::new_uninit_slice(bytes.len());
            reader.copy_into_slice(&mut dst).unwrap();
            let dst = unsafe { dst.assume_init() };
            prop_assert_eq!(&dst[..], bytes.as_slice());
        });
    }

    #[test]
    fn take_byte_consumes_and_advances() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReadAdapter::new(bytes.as_slice());
            for &expected in &bytes {
                prop_assert_eq!(reader.take_byte().unwrap(), expected);
            }
            prop_assert!(reader.take_byte().is_err());
        });
    }

    #[test]
    fn take_array_at_capacity_boundary() {
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3][..], 2);
        let arr = reader.take_array().expect("should return requested array");
        assert_eq!(arr, [1u8, 2]);
        let arr = reader.take_array().expect("should return requested array");
        assert_eq!(arr, [3]);
    }

    #[test]
    fn take_array_across_capacity_boundary() {
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4][..], 2);
        let arr = reader.take_array().expect("should return requested array");
        assert_eq!(arr, [1u8, 2, 3]);
        let arr = reader.take_array().expect("should return requested array");
        assert_eq!(arr, [4]);
    }

    #[test]
    fn as_trusted_within_capacity_in_chunks() {
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 1..100))| {
            // Choose a capacity that is <= total length so we exercise multiple fills,
            let capacity = bytes.len().div_ceil(2);
            let mut reader = BufReadAdapter::from_read_with_capacity(bytes.as_slice(), capacity);
            let mut offset = 0usize;
            while offset < bytes.len() {
                let remaining = bytes.len() - offset;
                let request = capacity.min(remaining);
                // Always request at most `capacity`, so we never ask for more than the buffer can hold in one go.
                let mut trusted = unsafe { reader.as_trusted_for(request).unwrap() };
                let mut dst = Box::<[u8]>::new_uninit_slice(request);
                trusted.copy_into_slice(&mut dst).unwrap();
                let dst = unsafe { dst.assume_init() };
                prop_assert_eq!(&dst[..], &bytes[offset..offset + request]);
                offset += request;
            }
        });
    }

    #[test]
    fn as_trusted_for_falls_back_when_exceeds_capacity() {
        // When the request exceeds buffer capacity, as_trusted_for falls back to the
        // Reader variant rather than erroring; the returned reader reads correctly.
        let bytes: Vec<_> = (1..100).collect();
        let capacity = bytes.len() / 2;
        let mut reader = BufReadAdapter::from_read_with_capacity(bytes.as_slice(), capacity);
        let mut trusted = unsafe { reader.as_trusted_for(bytes.len()).unwrap() };
        let mut dst = Box::<[u8]>::new_uninit_slice(bytes.len());
        trusted.copy_into_slice(&mut dst).unwrap();
        let dst = unsafe { dst.assume_init() };
        assert_eq!(&dst[..], bytes.as_slice());
    }

    #[test]
    fn as_trusted_for_correctly_advances() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReadAdapter::new(bytes.as_slice());
            let half = bytes.len().div_ceil(2);
            {
                let mut trusted = unsafe { reader.as_trusted_for(half).unwrap() };
                let mut dst = Box::<[u8]>::new_uninit_slice(half);
                trusted.copy_into_slice(&mut dst).unwrap();
                let dst = unsafe { dst.assume_init() };
                prop_assert_eq!(&dst[..], &bytes[0..half]);
            }
            let tail = bytes.len() - half;
            let mut remaining = Box::<[u8]>::new_uninit_slice(tail);
            reader.copy_into_slice(&mut remaining).unwrap();
            let remaining = unsafe { remaining.assume_init() };
            prop_assert_eq!(&remaining[..], &bytes[half..]);
        });
    }

    #[test]
    fn as_trusted_for_reader_errors_on_read_when_insufficient() {
        // as_trusted_for itself now always succeeds (falling back to Reader when
        // the buffer is too small); the error surfaces on the subsequent read.
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReadAdapter::new(bytes.as_slice());
            let mut trusted = unsafe { reader.as_trusted_for(bytes.len() + 1).unwrap() };
            let mut dst = Box::<[u8]>::new_uninit_slice(bytes.len() + 1);
            let result = trusted.copy_into_slice(&mut dst);
            prop_assert!(result.is_err());
        });
    }

    #[test]
    fn take_byte_flushes_trusted_consume() {
        // After a Slice-path as_trusted_for (consumed_trusted=2), take_byte must
        // flush the deferred consume before reading the next byte.
        let mut reader = BufReadAdapter::new(&[1u8, 2, 3, 4][..]);
        {
            let mut trusted = unsafe { reader.as_trusted_for(2).unwrap() };
            let two: [u8; 2] = trusted.take_array().unwrap();
            assert_eq!(two, [1, 2]);
        }
        // as_trusted_for advances 2; take_byte reads and consumes byte 3.
        assert_eq!(reader.take_byte().unwrap(), 3);
        assert_eq!(reader.take_byte().unwrap(), 4);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn take_scoped_fast_path_within_capacity() {
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4][..], 4);
        let s = reader.take_scoped(3).unwrap();
        assert_eq!(s, &[1, 2, 3]);
        assert_eq!(reader.take_byte().unwrap(), 4);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn take_scoped_aux_path_errors_when_insufficient() {
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2][..], 1);
        assert!(reader.take_scoped(4).is_err());
    }

    #[test]
    fn take_scoped_aux_path_advances_correctly() {
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 3..50))| {
            let capacity = 1usize; // force aux path for len >= 2
            let half = bytes.len() / 2;
            let mut reader = BufReadAdapter::from_read_with_capacity(bytes.as_slice(), capacity);
            {
                let s = reader.take_scoped(half).unwrap();
                prop_assert_eq!(s, &bytes[..half]);
            }
            let mut rest = Box::<[u8]>::new_uninit_slice(bytes.len() - half);
            reader.copy_into_slice(&mut rest).unwrap();
            let rest = unsafe { rest.assume_init() };
            prop_assert_eq!(&rest[..], &bytes[half..]);
        });
    }
}
