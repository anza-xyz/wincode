use {
    crate::io::{ReadResult, Reader, read_size_limit, slice::SliceUnchecked},
    std::{
        cmp::Ordering,
        io::{BufRead, BufReader, ErrorKind, Read},
        mem::{MaybeUninit, transmute},
        num::NonZeroUsize,
        ops::Range,
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
    /// Helper buffer used by the `take_scoped` and `peek_array` fallback paths when
    /// the slice returned by internal `fill_buf` is smaller than the requested length.
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
            ConsumeState::UnconsumedAux(r) => Ok(&self.aux_buf[r.clone()]),
        }
    }

    /// Flush any pending consume and determine whether getting contiguous data of `len` bytes
    /// should use the aux buffer.
    ///
    /// - `None` — can use reader's internal buffer that holds at least `len` bytes
    /// - `Some(range)` — aux path needed;
    ///   - `range` is the already-filled portion of `aux_buf` (`UnconsumedAux` state), or
    ///   - `0..0` if `aux_buf` is empty, but the reader buffer has less than `len` bytes
    fn flush_consume_and_check_aux_needed(
        &mut self,
        len: NonZeroUsize,
    ) -> std::io::Result<Option<Range<usize>>> {
        match &self.consume_state {
            ConsumeState::Direct => Ok((self.reader.fill_buf()?.len() < len.get()).then_some(0..0)),
            ConsumeState::PendingConsumed(n) => {
                self.reader.consume(n.get());
                self.consume_state = ConsumeState::Direct;
                Ok((self.reader.fill_buf()?.len() < len.get()).then_some(0..0))
            }
            ConsumeState::UnconsumedAux(r) => Ok(Some(r.clone())),
        }
    }

    /// Return a contiguous slice of exactly `len` bytes, reading ahead into `aux_buf` if needed.
    ///
    /// If `consume` is true the returned bytes are logically consumed and subsequent reads will
    /// start after them. If false, the bytes remain available so the caller can inspect them
    /// before deciding whether to consume.
    fn obtain_contiguous(&mut self, len: NonZeroUsize, consume: bool) -> ReadResult<&[u8]> {
        let Some(filled_aux_range) = self.flush_consume_and_check_aux_needed(len)? else {
            // `filled_aux_range=None` indicates that fill_buf returns large enough slice
            if consume {
                self.consume_state = ConsumeState::PendingConsumed(len);
            }
            return Ok(&self.reader.fill_buf()?[..len.get()]);
        };
        #[expect(clippy::arithmetic_side_effects)]
        let use_aux_range = filled_aux_range.start..filled_aux_range.start + len.get();
        if filled_aux_range.len() >= len.get() {
            if consume {
                self.consume_state =
                    ConsumeState::unconsumed_aux_or_direct(use_aux_range.end..filled_aux_range.end);
            }
            return Ok(&self.aux_buf[use_aux_range]);
        }

        self.aux_buf.resize(use_aux_range.end, 0);
        match self
            .reader
            .read_exact(&mut self.aux_buf[filled_aux_range.end..use_aux_range.end])
        {
            Ok(()) => {
                self.consume_state = if consume {
                    ConsumeState::Direct
                } else {
                    ConsumeState::UnconsumedAux(use_aux_range.clone())
                };
                Ok(&self.aux_buf[use_aux_range])
            }
            Err(err) if err.kind() == ErrorKind::UnexpectedEof => Err(read_size_limit(len.get())),
            Err(err) => Err(err.into()),
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

    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        let Some(n) = NonZeroUsize::new(N) else {
            return Ok(&[0; N]);
        };
        let buf = self.obtain_contiguous(n, false)?;
        // SAFETY: buf has been filled with exactly N bytes above.
        Ok(unsafe { &*(buf.as_ptr() as *const [u8; N]) })
    }

    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        let Some(len) = NonZeroUsize::new(len) else {
            return Ok(&[]);
        };
        self.obtain_contiguous(len, true)
    }

    unsafe fn consume_unchecked(&mut self, amt: usize) {
        self.consume(amt);
    }

    fn consume(&mut self, amt: usize) {
        if let Some(n) = self.consume_state.advance_get_reader_consume(amt) {
            self.reader.consume(n.get());
        }
    }

    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        let Some(n_bytes) = NonZeroUsize::new(n_bytes) else {
            return Ok(TrustedBufReader::Slice(unsafe { SliceUnchecked::new(&[]) }));
        };
        // Turn reader's buf into unchecked slice opportunistically. Trusted reader doesn't
        // strictly require contiguous memory - allocating and copying into aux would yield
        // unnecessary cost. This also skips the (rare) case when aux buf already has appropriate
        // slice, which simplifies accounting consumed data.
        let use_reader_buf = self.flush_consume_and_check_aux_needed(n_bytes)?.is_none();
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
    /// Bytes in this range are available in `aux_buf` (they were consumed from the
    /// underlying `reader` to obtain a contiguous slice, but are not yet logically consumed
    /// by the caller - until that happens `aux_buf` is the source of data).
    UnconsumedAux(Range<usize>),
}

impl ConsumeState {
    fn unconsumed_aux_or_direct(r: Range<usize>) -> Self {
        if r.is_empty() {
            Self::Direct
        } else {
            Self::UnconsumedAux(r)
        }
    }

    fn is_direct(&self) -> bool {
        matches!(self, Self::Direct)
    }

    /// Advance the state by `amt` bytes, returning any amount that must still
    /// be forwarded to the underlying reader via [`BufRead::consume`].
    #[must_use]
    fn advance_get_reader_consume(&mut self, amt: usize) -> Option<NonZeroUsize> {
        match self {
            Self::UnconsumedAux(r) => {
                let avail = r.len();
                #[expect(clippy::arithmetic_side_effects, reason = "based on cmp")]
                match amt.cmp(&avail) {
                    Ordering::Less => *r = r.start + amt..r.end,
                    Ordering::Equal => *self = Self::Direct,
                    Ordering::Greater => {
                        *self = Self::Direct;
                        // Safety: amt > avail, forward remaining consume to the reader
                        return Some(unsafe { NonZeroUsize::new_unchecked(amt - avail) });
                    }
                }
                None
            }
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

    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        match self {
            Self::Slice(slice) => slice.peek_array(),
            Self::Reader(reader) => reader.peek_array(),
        }
    }

    unsafe fn consume_unchecked(&mut self, amt: usize) {
        match self {
            Self::Slice(slice) => unsafe { slice.consume_unchecked(amt) },
            Self::Reader(reader) => unsafe { reader.consume_unchecked(amt) },
        }
    }

    fn consume(&mut self, amt: usize) {
        match self {
            Self::Slice(slice) => slice.consume(amt),
            Self::Reader(reader) => reader.consume(amt),
        }
    }
}

#[expect(clippy::arithmetic_side_effects)]
#[cfg(all(test, feature = "std"))]
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
    fn peek_array_fast_path_within_capacity() {
        // Buffer holds all bytes; peek returns first N without consuming.
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4][..], 4);
        {
            let peeked: &[u8; 2] = reader.peek_array().unwrap();
            assert_eq!(peeked, &[1, 2]);
        }
        // Bytes are still present; consume them and read the rest.
        reader.consume(2);
        assert_eq!(reader.take_byte().unwrap(), 3);
        assert_eq!(reader.take_byte().unwrap(), 4);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn peek_array_aux_path_errors_when_insufficient() {
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2][..], 1);
        let result: ReadResult<&[u8; 4]> = reader.peek_array();
        assert!(result.is_err());
    }

    #[test]
    fn peek_array_aux_path_then_take_byte() {
        // After aux peek + consume, subsequent reads see remaining bytes correctly.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 3..50))| {
            let capacity = 1usize; // force aux path for peek of 2
            let mut reader = BufReadAdapter::from_read_with_capacity(bytes.as_slice(), capacity);
            {
                let peeked: &[u8; 2] = reader.peek_array().unwrap();
                prop_assert_eq!(peeked.as_slice(), &bytes[..2]);
            }
            unsafe { reader.consume_unchecked(2) };
            for &expected in &bytes[2..] {
                prop_assert_eq!(reader.take_byte().unwrap(), expected);
            }
            prop_assert!(reader.take_byte().is_err());
        });
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

    #[test]
    fn peek_aux_partial_consume_then_peek_from_remaining_aux() {
        // Capacity 2, peek 4 (aux path), consume 2, then peek 2 from remaining aux.
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4, 5][..], 2);
        {
            let peeked: &[u8; 4] = reader.peek_array().unwrap();
            assert_eq!(peeked, &[1, 2, 3, 4]);
        }
        reader.consume(2); // UnconsumedAux(2..4)
        {
            let peeked: &[u8; 2] = reader.peek_array().unwrap(); // serves from remaining aux
            assert_eq!(peeked, &[3, 4]);
        }
        reader.consume(2);
        assert_eq!(reader.take_byte().unwrap(), 5);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn peek_aux_partial_consume_then_take_scoped_from_remaining_aux() {
        // Capacity 2, peek 4 (aux path), consume 1, then take_scoped 3 from remaining aux.
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4, 5][..], 2);
        {
            let peeked: &[u8; 4] = reader.peek_array().unwrap();
            assert_eq!(peeked, &[1, 2, 3, 4]);
        }
        reader.consume(1); // UnconsumedAux(1..4)
        {
            let s = reader.take_scoped(3).unwrap(); // serves from remaining aux
            assert_eq!(s, &[2, 3, 4]);
        }
        assert_eq!(reader.take_byte().unwrap(), 5);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn peek_aux_no_consume_then_copy_into_slice_drains_aux_then_reader() {
        // Capacity 2, peek 3 (aux path), drop ref without consuming,
        // then copy_into_slice 5 - should drain aux [1,2,3] then read [4,5] from reader.
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4, 5][..], 2);
        {
            let peeked: &[u8; 3] = reader.peek_array().unwrap();
            assert_eq!(peeked, &[1, 2, 3]);
        }
        // State is still UnconsumedAux(0..3) - bytes not consumed
        let mut dst = [MaybeUninit::<u8>::uninit(); 5];
        reader.copy_into_slice(&mut dst[..]).unwrap();
        let dst: [u8; 5] = unsafe { transmute(dst) };
        assert_eq!(dst, [1u8, 2, 3, 4, 5]);
    }

    #[test]
    fn peek_aux_no_consume_then_take_scoped_larger_reads_more_from_reader() {
        // Capacity 2, peek 2 (aux), drop ref; then take_scoped 4 - has 2 in aux, reads 2 more.
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4, 5][..], 2);
        {
            let peeked: &[u8; 2] = reader.peek_array().unwrap();
            assert_eq!(peeked, &[1, 2]);
        }
        // UnconsumedAux(0..2); take_scoped(4) needs 4, only 2 in aux, reads 2 more from reader.
        {
            let s = reader.take_scoped(4).unwrap();
            assert_eq!(s, &[1, 2, 3, 4]);
        }
        assert_eq!(reader.take_byte().unwrap(), 5);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn peek_fast_then_take_scoped_fast() {
        // Both within capacity: peek 2, don't consume, take_scoped 4 (advances from fill_buf).
        let mut reader = BufReadAdapter::from_read_with_capacity(&[1u8, 2, 3, 4, 5][..], 5);
        {
            let peeked: &[u8; 2] = reader.peek_array().unwrap();
            assert_eq!(peeked, &[1, 2]);
        }
        // No consume - state is still Direct (fast path didn't set UnconsumedAux).
        {
            let s = reader.take_scoped(4).unwrap();
            assert_eq!(s, &[1, 2, 3, 4]);
        }
        assert_eq!(reader.take_byte().unwrap(), 5);
        assert!(reader.take_byte().is_err());
    }

    #[test]
    fn mixed_peek_take_scoped_copy_proptest() {
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 6..50))| {
            // Force aux path: capacity 1, so any multi-byte op goes through aux.
            let mut reader = BufReadAdapter::from_read_with_capacity(bytes.as_slice(), 1);
            // peek 3, consume 1, take_scoped 2 (remaining from aux), copy_into_slice rest.
            {
                let peeked: &[u8; 3] = reader.peek_array().unwrap();
                prop_assert_eq!(peeked.as_slice(), &bytes[..3]);
            }
            reader.consume(1);
            {
                let s = reader.take_scoped(2).unwrap();
                prop_assert_eq!(s, &bytes[1..3]);
            }
            let mut rest = Box::<[u8]>::new_uninit_slice(bytes.len() - 3);
            reader.copy_into_slice(&mut rest).unwrap();
            let rest = unsafe { rest.assume_init() };
            prop_assert_eq!(&rest[..], &bytes[3..]);
        });
    }
}
