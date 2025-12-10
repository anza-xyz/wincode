use {
    crate::io::{read_size_limit, ReadError, ReadResult, Reader, TrustedSliceReader},
    core::{
        mem::{transmute, MaybeUninit},
        ops::Range,
        ptr,
        slice::{from_raw_parts, from_raw_parts_mut},
    },
    std::io::{ErrorKind, Read},
};

/// Add buffered reading to any [`Read`] instance.
///
/// It can be excessively inefficient to work directly with a [`Read`] instance.
/// For example, every call to read on [`TcpStream`](std::net::TcpStream) results in a system call.
/// A [`BufReader<R>`] performs large, infrequent reads on the underlying [`Read`] and
/// maintains an in-memory buffer of the results.
///
/// [`BufReader<R>`] can improve the speed of programs that make small and repeated
/// read calls to the same file or network socket. It does not help when reading very
/// large amounts at once, or reading just one or a few times. It also provides no advantage
/// when reading from a source that is already in memory, like a [`Vec<u8>`].
pub struct BufReader<R: ?Sized> {
    buf: Box<[MaybeUninit<u8>]>,
    filled: Range<usize>,
    inner: R,
}

const DEFAULT_BUF_SIZE: usize = 8 * 1024;

impl<R> BufReader<R> {
    /// Create a new [`BufReader<R>`] with the default buffer capacity.
    ///
    /// The default buffer capacity is currently 8KiB.
    pub fn new(inner: R) -> Self {
        Self {
            buf: Box::new_uninit_slice(DEFAULT_BUF_SIZE),
            filled: 0..0,
            inner,
        }
    }

    /// Create a new [`BufReader<R>`] with the specified capacity.
    pub fn with_capacity(inner: R, capacity: usize) -> Self {
        Self {
            buf: Box::new_uninit_slice(capacity),
            filled: 0..0,
            inner,
        }
    }

    /// Consume the [`BufReader<R>`] and return the underlying reader.
    ///
    /// Note that any leftover data in the buffer will be lost.
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: ?Sized> BufReader<R> {
    /// Return a slice of the buffer that contains the currently filled bytes.
    ///
    /// Unlike `fill_buf`, this will not attempt to fill the buffer.
    #[inline]
    pub fn buffer(&self) -> &[u8] {
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        buffer(&self.buf, &self.filled)
    }
}

/// Return a slice of the buffer that contains the currently filled bytes.
#[inline]
fn buffer<'a>(buf: &'a [MaybeUninit<u8>], filled: &Range<usize>) -> &'a [u8] {
    // SAFETY: `filled` always points to an initialized portion of the buffer.
    unsafe { from_raw_parts(buf.as_ptr().cast::<u8>().add(filled.start), filled.len()) }
}

#[inline]
#[expect(clippy::arithmetic_side_effects)]
fn consume_unchecked(filled: &mut Range<usize>, amt: usize) {
    filled.start += amt;
    // Reset the range if we've consumed all the bytes.
    if (*filled).is_empty() {
        *filled = 0..0;
    }
}

#[inline]
fn consume(filled: &mut Range<usize>, amt: usize) -> ReadResult<()> {
    if filled.len() < amt {
        return Err(read_size_limit(amt));
    }
    // SAFETY: We just checked that `filled.len() >= amt`.
    consume_unchecked(filled, amt);
    Ok(())
}

/// Fill the buffer with up to `n_bytes` from the reader.
///
/// Note this implementation differs from the semantics of [`std::io::BufRead`]
/// in that wincode [`Reader`]s take an `n_bytes` argument.
/// Importantly, implementations should try to read at least `n_bytes`
/// bytes, retrying until either `n_bytes` are read or EOF is hit.
#[expect(clippy::arithmetic_side_effects)]
fn fill_buf<'a, R: ?Sized + Read>(
    r: &mut R,
    buf: &'a mut [MaybeUninit<u8>],
    filled: &mut Range<usize>,
    n_bytes: usize,
) -> ReadResult<&'a [u8]> {
    // Number of bytes already buffered.
    let buffered_len = filled.len();
    // We already have sufficient bytes in the buffer.
    if buffered_len >= n_bytes {
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        return Ok(unsafe { from_raw_parts(buf.as_ptr().cast::<u8>().add(filled.start), n_bytes) });
    }

    #[cold]
    fn out_of_memory() -> ReadError {
        ReadError::Io(ErrorKind::OutOfMemory.into())
    }
    if n_bytes > buf.len() {
        return Err(out_of_memory());
    }

    let needed = n_bytes - buffered_len;
    let capacity = buf.len();

    // User requested more bytes than we have space for relative to the filled
    // range in the buffer.
    //
    // In this case, we need to shift the existing bytes to the beginning of the buffer.
    if needed > capacity - filled.end {
        let base = buf.as_mut_ptr().cast::<u8>();
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        let src = unsafe { base.add(filled.start) };
        let dst = base;
        // Use `copy_nonoverlapping` if we can, otherwise use `copy`.
        if filled.start >= buffered_len {
            // SAFETY:
            // - `filled` always points to an initialized portion of the buffer.
            // - we checked that `filled.start >= len`, src and dst don't overlap.
            unsafe { ptr::copy_nonoverlapping(src, dst, buffered_len) };
        } else {
            // SAFETY:
            // - `filled` always points to an initialized portion of the buffer.
            // - we checked that `filled.start < len`, src and dst overlap.
            unsafe { ptr::copy(src, dst, buffered_len) };
        }

        *filled = 0..buffered_len;
    }

    let mut read = 0;
    // SAFETY:
    // - `filled.end` is always less than `capacity`.
    // - We've verified above that we have enough capacity for `needed` relative to `filled.end`.
    let mut dst =
        unsafe { from_raw_parts_mut(buf.as_mut_ptr().add(filled.end), capacity - filled.end) };
    while read < needed {
        // SAFETY: `read` only writes to uninitialized bytes.
        match r.read(unsafe { transmute::<&mut [MaybeUninit<u8>], &mut [u8]>(dst) }) {
            Ok(0) => break,
            Ok(n) => {
                read += n;
                // SAFETY: `n` bytes were written to `dst`, so `dst` is advanced by `n` bytes.
                dst = unsafe { dst.get_unchecked_mut(n..) };
            }
            Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) => return Err(e.into()),
        }
    }

    filled.end += read;

    // SAFETY: `filled` always points to an initialized portion of the buffer.
    let out = unsafe {
        from_raw_parts(
            buf.as_ptr().cast::<u8>().add(filled.start),
            filled.len().min(n_bytes),
        )
    };
    Ok(out)
}

fn copy_into_slice<R: ?Sized + Read>(
    r: &mut R,
    buf: &mut [MaybeUninit<u8>],
    filled: &mut Range<usize>,
    mut dst: &mut [MaybeUninit<u8>],
) -> ReadResult<()> {
    // The `Reader` trait provides a default implementation of `copy_into_slice`, but we provide
    // an optimization here that will avoid excessive copying and reallocation
    // when the required reads are large.

    let len_buffered = filled.len();
    let needed = dst.len();
    let capacity = buf.len();
    // Drain whatever we have in the buffer to dst.
    if len_buffered > 0 {
        let to_copy = needed.min(len_buffered);
        let src = buffer(buf, filled);
        // SAFETY:
        // - `src` is valid for `len_buffered`
        // - `dst` is valid for `needed`
        // - `to_copy` is min of both.
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), to_copy);
            consume_unchecked(filled, to_copy);
        }

        if to_copy == needed {
            return Ok(());
        }

        // Advance dst
        // SAFETY: `to_copy` < `dst.len()` checked above.
        dst = unsafe { dst.get_unchecked_mut(to_copy..) };
    }

    let needed = dst.len();
    // If the remaining requirement is large (>= capacity), read directly.
    // Note: buffer is guaranteed empty here because we drained it above and didn't return.
    if needed >= capacity {
        while !dst.is_empty() {
            // SAFETY: `read` only writes to uninitialized bytes.
            match r.read(unsafe { transmute::<&mut [MaybeUninit<u8>], &mut [u8]>(dst) }) {
                Ok(0) => break,
                Ok(n) => {
                    // SAFETY: `n` bytes were written to `dst`, so `dst` is advanced by `n` bytes.
                    dst = unsafe { dst.get_unchecked_mut(n..) };
                }
                Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e.into()),
            }
        }
        if !dst.is_empty() {
            return Err(ReadError::Io(ErrorKind::UnexpectedEof.into()));
        }
        return Ok(());
    }

    // Otherwise, the remaining requirement is small (< capacity).
    //
    // Refill the buffer and copy.
    let src = fill_buf(r, buf, filled, needed)?;
    if src.len() != needed {
        return Err(read_size_limit(needed));
    }
    // SAFETY:
    // - `src.len() == needed`
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), needed);
        consume_unchecked(filled, needed);
    }
    Ok(())
}

#[inline]
fn copy_into_slice_t<R: ?Sized + Read, T>(
    r: &mut R,
    buf: &mut [MaybeUninit<u8>],
    filled: &mut Range<usize>,
    dst: &mut [MaybeUninit<T>],
) -> ReadResult<()> {
    // Similar to `copy_into_slice`, the `Reader` trait provides a default implementation of `copy_into_slice_t`,
    // but we override here and pass through to `copy_into_slice` so we can perform direct writes to destinations if
    // requested read sizes are larger than the buffer capacity.
    let len = size_of_val(dst);
    // SAFETY:
    // - `dst` is plain old data, safe to treat as bytes.
    let slice = unsafe { from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), len) };
    copy_into_slice(r, buf, filled, slice)?;
    Ok(())
}

#[inline]
fn as_trusted_for<'a, 'b, R: ?Sized + Read>(
    r: &'b mut R,
    buf: &'b mut [MaybeUninit<u8>],
    filled: &'b mut Range<usize>,
    n_bytes: usize,
) -> ReadResult<TrustedBufReader<'a, 'b, R>> {
    if n_bytes <= filled.len() {
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        let window =
            unsafe { from_raw_parts(buf.as_ptr().cast::<u8>().add(filled.start), n_bytes) };
        consume_unchecked(filled, n_bytes);
        return Ok(TrustedBufReader::WithinCapacity(TrustedSliceReader::new(
            window,
        )));
    }

    if n_bytes > buf.len() {
        // Prefetch as much as we can (limited by buffer capacity).
        fill_buf(r, buf, filled, buf.len())?;
        return Ok(TrustedBufReader::ExceedsCapacity(BufReaderMut {
            buf,
            filled,
            inner: r,
        }));
    }
    let window = fill_buf(r, buf, filled, n_bytes)?;
    if window.len() != n_bytes {
        return Err(read_size_limit(n_bytes));
    }
    consume_unchecked(filled, n_bytes);
    Ok(TrustedBufReader::WithinCapacity(TrustedSliceReader::new(
        window,
    )))
}

impl<'a, R: ?Sized + Read> Reader<'a> for BufReader<R> {
    type Trusted<'b>
        = TrustedBufReader<'a, 'b, R>
    where
        Self: 'b;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        fill_buf(&mut self.inner, &mut self.buf, &mut self.filled, n_bytes)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        consume_unchecked(&mut self.filled, amt);
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        consume(&mut self.filled, amt)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        as_trusted_for(&mut self.inner, &mut self.buf, &mut self.filled, n_bytes)
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        copy_into_slice(&mut self.inner, &mut self.buf, &mut self.filled, dst)
    }

    #[inline]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        copy_into_slice_t(&mut self.inner, &mut self.buf, &mut self.filled, dst)
    }
}

pub struct BufReaderMut<'a, R: ?Sized> {
    buf: &'a mut [MaybeUninit<u8>],
    filled: &'a mut Range<usize>,
    inner: &'a mut R,
}

impl<'a, R: ?Sized + Read> Reader<'a> for BufReaderMut<'a, R> {
    type Trusted<'b>
        = TrustedBufReader<'a, 'b, R>
    where
        Self: 'b;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        // Same as BufReader - buffer opportunistically, don't limit based on quota.
        fill_buf(self.inner, self.buf, self.filled, n_bytes)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        consume_unchecked(self.filled, amt);
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        consume(self.filled, amt)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        as_trusted_for(self.inner, self.buf, self.filled, n_bytes)
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        copy_into_slice(self.inner, self.buf, self.filled, dst)
    }

    #[inline]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        copy_into_slice_t(self.inner, self.buf, self.filled, dst)
    }
}

/// Trusted reader for [`BufReader`].
///
/// This type captures two possible scenarios when requesting a trusted window:
///
/// 1. The requested window is within the buffer capacity.
/// 2. The requested window is larger than the buffer capacity.
///
/// In the first case, we can provide a [`TrustedSliceReader`], which achieves
/// the desired trusted semantics where bounds checks are eliminated.
///
/// In the second case, we provide a [`BufReaderMut`], which effectively
/// acts as a typical non-trusted [`BufReader`]. An alternative implementation
/// could reallocate the buffer to accomodate the requested window size, but
/// this route was chosen for simplicity, predictability, and user-tuneability.
/// In particular, rather than implicitly reallocating on behalf of the user,
/// one may simply tune capacity for a specific use case.
pub enum TrustedBufReader<'a, 'b, R: ?Sized> {
    WithinCapacity(TrustedSliceReader<'a, 'b>),
    ExceedsCapacity(BufReaderMut<'b, R>),
}

impl<'a, R: ?Sized + Read> Reader<'a> for TrustedBufReader<'a, '_, R> {
    type Trusted<'c>
        = TrustedBufReader<'a, 'c, R>
    where
        Self: 'c;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        match self {
            TrustedBufReader::WithinCapacity(r) => r.fill_buf(n_bytes),
            TrustedBufReader::ExceedsCapacity(r) => r.fill_buf(n_bytes),
        }
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        match self {
            TrustedBufReader::WithinCapacity(r) => r.consume_unchecked(amt),
            TrustedBufReader::ExceedsCapacity(r) => r.consume_unchecked(amt),
        }
    }

    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        match self {
            TrustedBufReader::WithinCapacity(r) => r.consume(amt),
            TrustedBufReader::ExceedsCapacity(r) => r.consume(amt),
        }
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        match self {
            TrustedBufReader::WithinCapacity(r) => {
                Ok(TrustedBufReader::WithinCapacity(r.as_trusted_for(n_bytes)?))
            }
            TrustedBufReader::ExceedsCapacity(r) => {
                as_trusted_for(r.inner, r.buf, r.filled, n_bytes)
            }
        }
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        match self {
            TrustedBufReader::WithinCapacity(r) => r.copy_into_slice(dst),
            TrustedBufReader::ExceedsCapacity(r) => r.copy_into_slice(dst),
        }
    }

    #[inline]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        match self {
            TrustedBufReader::WithinCapacity(r) => r.copy_into_slice_t(dst),
            TrustedBufReader::ExceedsCapacity(r) => r.copy_into_slice_t(dst),
        }
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    #![expect(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};

    #[test]
    fn with_capacity_zero_errors() {
        let mut reader = BufReader::with_capacity(&[1u8, 2, 3][..], 0);
        let result = reader.fill_buf(1);
        assert!(result.is_err());
    }

    #[test]
    fn with_capacity_no_realloc() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::with_capacity(bytes.as_slice(), bytes.len());
            let data = reader.fill_buf(bytes.len()).unwrap();
            prop_assert_eq!(data, bytes.as_slice());
            // fill_buf does not consume
            let data = reader.fill_buf(bytes.len()).unwrap();
            prop_assert_eq!(data, bytes.as_slice());
            reader.consume(bytes.len()).unwrap();
            let data = reader.fill_buf(bytes.len()).unwrap();
            prop_assert_eq!(data, &[]);
        });
    }

    #[test]
    fn fill_buf_returns_less_at_eof() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let data = reader.fill_buf(bytes.len() + 1).unwrap();
            prop_assert_eq!(data, bytes.as_slice());
        });
    }

    #[test]
    fn fill_exact_returns_exact_bytes() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let data = reader.fill_exact(bytes.len()).unwrap();
            prop_assert_eq!(data, bytes.as_slice());
        });
    }

    #[test]
    fn fill_exact_errors_when_insufficient_bytes() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let result = reader.fill_exact(bytes.len() + 1);
            prop_assert!(result.is_err());
        });
    }

    #[test]
    fn copy_into_slice_copies_and_advances() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let mut dst = Vec::with_capacity(bytes.len());
            reader.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(bytes.len()) };
            prop_assert_eq!(&dst, &bytes);
            prop_assert!(reader.consume(1).is_err())
        });
    }

    #[test]
    fn copy_into_slice_errors_when_insufficient() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let mut dst = Vec::with_capacity(bytes.len() + 1);
            let dst = dst.spare_capacity_mut();
            let result = reader.copy_into_slice(dst);
            prop_assert!(result.is_err());
        });
    }

    #[test]
    fn copy_into_slice_direct_read() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::with_capacity(bytes.as_slice(), bytes.len() / 2);
            let mut dst = Vec::with_capacity(bytes.len());
            reader.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(bytes.len()) };
            prop_assert_eq!(&dst, &bytes);
        });
    }

    #[test]
    fn as_trusted_for_correctly_advances() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let half = bytes.len() / 2;
            {
                let mut trusted = unsafe { reader.as_trusted_for(half).unwrap() };
                let data = trusted.fill_exact(half).unwrap();
                prop_assert_eq!(data, &bytes[0..half]);
                trusted.consume(half).unwrap();
            }
            let remaining = reader.fill_buf(bytes.len() - half).unwrap();
            prop_assert_eq!(remaining, &bytes[half..]);
        });
    }

    #[test]
    fn copy_into_slice_transition_from_buffer_to_direct() {
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 21..100))| {
            // - Capacity is 10 bytes
            // - Read 5 bytes into the buffer
            // - Request to copy `bytes.len()`, which is > capacity
            //
            // Should trigger the partial drain + direct read path.
            let mut reader = BufReader::with_capacity(bytes.as_slice(), 10);
            // Prime the buffer with 5 bytes
            let _ = reader.fill_buf(5).unwrap();

            let mut dst = Vec::with_capacity(bytes.len());
            reader.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(bytes.len()) };
            prop_assert_eq!(&dst, &bytes);
        });
    }

    #[test]
    fn fill_buf_compaction_copy() {
        // Ensure we hit the else condition where capacity is sufficient but data is at the end.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 20..100))| {
            let mut reader = BufReader::with_capacity(bytes.as_slice(), 15);

            // Fill buffer partially
            let _ = reader.fill_buf(10).unwrap();
            // Consume 5 bytes -- filled = 5..10.
            reader.consume(5).unwrap();

            // Current filled len = 5. Needed = 7.
            // Total capacity (15) >= Total needed (12).
            let data = reader.fill_buf(12).unwrap();

            prop_assert_eq!(data, &bytes[5..17]);
        });
    }

    #[test]
    fn fill_buf_compaction_copy_nonoverlapping() {
        // Ensure we hit the `copy_nonoverlapping` optimization in `fill_buf`.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 10..100))| {
            let capacity = bytes.len() / 2;
            let consume_amt = capacity * 3 / 4;
            let remaining = capacity - consume_amt;

            let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);

            // Fill entire capacity
            let _ = reader.fill_buf(capacity).unwrap();
            // Consume 75%
            reader.consume(consume_amt).unwrap();

            // Request for more than remaining triggers shift with copy_nonoverlapping.
            let request = remaining + 1;
            let buf = reader.fill_buf(request).unwrap();

            prop_assert_eq!(buf, &bytes[consume_amt..consume_amt + request]);
        });
    }

    #[test]
    fn trusted_reader_streams_beyond_capacity() {
        // Test that TrustedBufReader can handle a quota larger than buffer capacity
        // by refilling the buffer multiple times.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 50..200))| {
            let capacity = 16; // Small buffer
            let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);

            // Request a trusted window larger than buffer capacity
            let mut trusted = unsafe { reader.as_trusted_for(bytes.len()).unwrap() };

            // Read all bytes in small chunks, forcing multiple buffer refills
            let mut collected = Vec::new();
            let chunk_size = 8;
            let mut remaining = bytes.len();

            while remaining > 0 {
                let to_read = chunk_size.min(remaining);
                let data = trusted.fill_exact(to_read).unwrap();
                collected.extend_from_slice(data);
                trusted.consume(to_read).unwrap();
                remaining -= to_read;
            }

            prop_assert_eq!(collected, bytes);
        });
    }

    #[test]
    fn trusted_reader_copy_into_slice_direct_read() {
        // Test that TrustedBufReader's copy_into_slice bypasses buffer for large reads.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 50..200))| {
            let capacity = 16; // Small buffer
            let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);

            let mut trusted = unsafe { reader.as_trusted_for(bytes.len()).unwrap() };

            // Large copy_into_slice should use direct read path
            let mut dst = Vec::with_capacity(bytes.len());
            trusted.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(bytes.len()) };

            prop_assert_eq!(dst, bytes);
        });
    }

    #[test]
    fn trusted_reader_exceeds_capacity_subwindow_transitions_to_within_capacity() {
        let bytes = [0u8; 64];
        let mut reader = BufReader::with_capacity(bytes.as_slice(), 8);

        {
            let mut trusted = unsafe { reader.as_trusted_for(32).unwrap() };
            assert!(matches!(&trusted, TrustedBufReader::ExceedsCapacity(_)));

            {
                let mut sub = unsafe { trusted.as_trusted_for(6).unwrap() };
                assert!(matches!(&sub, TrustedBufReader::WithinCapacity(_)));
                let src = sub.fill_exact(6).unwrap();
                assert_eq!(src, &bytes[..6]);
                sub.consume(6).unwrap();
            }

            let src = trusted.fill_exact(4).unwrap();
            assert_eq!(src, &bytes[6..10]);
            trusted.consume(4).unwrap();
        }

        let src = reader.fill_exact(4).unwrap();
        assert_eq!(src, &bytes[10..14]);
    }
}
