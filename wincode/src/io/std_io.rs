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
    buf: Vec<u8>,
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
            buf: Vec::with_capacity(DEFAULT_BUF_SIZE),
            filled: 0..0,
            inner,
        }
    }

    /// Create a new [`BufReader<R>`] with the specified capacity.
    pub fn with_capacity(inner: R, capacity: usize) -> Self {
        Self {
            buf: Vec::with_capacity(capacity),
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

/// Fill the buffer with up to `n_bytes` from the reader.
///
/// Note this implementation differs from the semantics of [`std::io::BufRead`]
/// in that wincode [`Reader`]s take an `n_bytes` argument.
/// Importantly, implementations should try to read at least `n_bytes`
/// bytes, retrying until either `n_bytes` are read or EOF is hit.
///
/// This function does NOT grow the buffer. If `n_bytes > capacity`, it returns an error.
/// Use [`maybe_grow_and_fill_buf`] if buffer growth is needed.
fn fill_buf<'a, R: Read + ?Sized>(
    r: &mut R,
    buf: &'a mut Vec<u8>,
    filled: &mut Range<usize>,
    n_bytes: usize,
) -> ReadResult<&'a [u8]> {
    // Number of bytes already buffered.
    let buffered_len = filled.len();
    // We already have sufficient bytes in the buffer.
    if buffered_len >= n_bytes {
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        return Ok(unsafe { from_raw_parts(buf.as_ptr().add(filled.start), n_bytes) });
    }

    let capacity = buf.capacity();

    // Error if request exceeds buffer capacity (this function doesn't grow).
    if n_bytes > capacity {
        #[cold]
        fn out_of_memory() -> ReadError {
            ReadError::Io(ErrorKind::OutOfMemory.into())
        }
        return Err(out_of_memory());
    }

    // SAFETY: we check that `n_bytes > capacity` above, so this will not underflow.
    let needed = unsafe { n_bytes.unchecked_sub(buffered_len) };
    // SAFETY: we maintain the invariant that `filled.end` is always less than `capacity`.
    let edge_capacity = unsafe { capacity.unchecked_sub(filled.end) };

    // User requested more bytes than we have space for relative to filled.end.
    // Compact the buffer by shifting existing bytes to the beginning.
    if needed > edge_capacity {
        let base = buf.as_mut_ptr();
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

    // SAFETY: we checked that the buffer has sufficient capacity for `n_bytes`.
    unsafe { fill_buf_unchecked(r, buf, filled, n_bytes) }
}

/// Fill the buffer with up to `n_bytes` from the reader without any
/// fast path checks (e.g., don't return early if we have enough bytes in the buffer)
/// or whether the buffer has capacity for `n_bytes`.
///
/// # Safety
/// - Caller guarantees the buffer has sufficient edge capacity (i.e., `buf.capacity() - filled.end`)
///   for `n_bytes`.
#[expect(clippy::arithmetic_side_effects)]
unsafe fn fill_buf_unchecked<'a, R: Read + ?Sized>(
    r: &mut R,
    buf: &'a mut Vec<u8>,
    filled: &mut Range<usize>,
    n_bytes: usize,
) -> ReadResult<&'a [u8]> {
    let buffered_len = filled.len();
    // Caller guarantees n_bytes is greater than the number of bytes already buffered.
    let needed = unsafe { n_bytes.unchecked_sub(buffered_len) };
    // SAFETY: we maintain the invariant that `filled.end` is always less than `capacity`.
    let edge_capacity = unsafe { buf.capacity().unchecked_sub(filled.end) };

    let mut read = 0;
    // SAFETY:
    // - `filled.end` is always less than `buf.capacity()` by invariant.
    let mut dst = unsafe {
        from_raw_parts_mut(
            buf.as_mut_ptr().cast::<MaybeUninit<u8>>().add(filled.end),
            edge_capacity,
        )
    };
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
    let out = unsafe { from_raw_parts(buf.as_ptr().add(filled.start), filled.len().min(n_bytes)) };
    Ok(out)
}

/// Like [`fill_buf`], but grows the buffer if `n_bytes > capacity`.
///
/// Used by `as_trusted_for` where we need to guarantee a contiguous window of N bytes.
fn maybe_grow_and_fill_buf<'a, R: Read + ?Sized>(
    r: &mut R,
    buf: &'a mut Vec<u8>,
    filled: &mut Range<usize>,
    n_bytes: usize,
) -> ReadResult<&'a [u8]> {
    let buffered_len = filled.len();
    if buffered_len >= n_bytes {
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        return Ok(unsafe { from_raw_parts(buf.as_ptr().add(filled.start), n_bytes) });
    }

    if n_bytes > buf.capacity() {
        // Need to reallocate - copy directly to new buffer rather than shifting (copying) and reallocating.
        let mut new_buf = Vec::with_capacity(n_bytes.next_power_of_two());
        // Copy the existing bytes to the front of the new buffer.
        // SAFETY:
        // - `filled` always points to an initialized portion of the buffer.
        // - `new_buf` is valid for `buffered_len` bytes.
        unsafe {
            ptr::copy_nonoverlapping(
                buf.as_ptr().add(filled.start),
                new_buf.as_mut_ptr(),
                buffered_len,
            );
        }
        *buf = new_buf;
        *filled = 0..buffered_len;
    }

    unsafe { fill_buf_unchecked(r, buf, filled, n_bytes) }
}

impl<R: ?Sized> BufReader<R> {
    /// Return a slice of the buffer that contains the currently filled bytes.
    ///
    /// Unlike `fill_buf`, this will not attempt to fill the buffer.
    #[inline]
    pub fn buffer(&self) -> &[u8] {
        // SAFETY: `filled` always points to an initialized portion of the buffer.
        unsafe { from_raw_parts(self.buf.as_ptr().add(self.filled.start), self.filled.len()) }
    }
}

#[expect(clippy::arithmetic_side_effects)]
#[inline]
fn consume_unchecked(filled: &mut Range<usize>, amt: usize) {
    filled.start += amt;
    // Reset the range if we've consumed all the bytes.
    if (*filled).is_empty() {
        *filled = 0..0;
    }
}

impl<'a, R: ?Sized + Read> Reader<'a> for BufReader<R> {
    type Trusted<'b>
        = TrustedSliceReader<'a, 'b>
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

    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if self.filled.len() < amt {
            return Err(read_size_limit(amt));
        }
        // SAFETY: We just checked that `filled.len() >= amt`.
        unsafe { self.consume_unchecked(amt) };
        Ok(())
    }

    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        let buffer =
            maybe_grow_and_fill_buf(&mut self.inner, &mut self.buf, &mut self.filled, n_bytes)?;
        if buffer.len() != n_bytes {
            return Err(read_size_limit(n_bytes));
        }
        // Contract of `as_trusted_for` specifies that the returned reader will consume all `n_bytes`.
        consume_unchecked(&mut self.filled, n_bytes);

        Ok(TrustedSliceReader::new(buffer))
    }

    fn copy_into_slice(&mut self, mut dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        // The `Reader` trait provides a default implementation of `copy_into_slice`, but we provide
        // an optimization here that will avoid excessive copying or need for reallocation
        // when the required reads are large.

        let len_buffered = self.filled.len();
        let needed = dst.len();
        // Drain whatever we have in the buffer to dst.
        if len_buffered > 0 {
            let to_copy = needed.min(len_buffered);
            let src = self.buffer();
            // SAFETY:
            // - `src` is valid for `len_buffered`
            // - `dst` is valid for `dst.len()`
            // - `to_copy` is min of both.
            unsafe {
                ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), to_copy);
                self.consume_unchecked(to_copy);
            }

            if to_copy == needed {
                return Ok(());
            }

            // Advance dst
            // SAFETY: `to_copy` < `dst.len()` checked above.
            dst = unsafe { dst.get_unchecked_mut(to_copy..) };
        }

        // If the remaining requirement is large (>= capacity), read directly.
        // Note: buffer is guaranteed empty here because we drained it above and didn't return.
        if needed >= self.buf.capacity() {
            while !dst.is_empty() {
                // SAFETY: `read` only writes to uninitialized bytes.
                match self
                    .inner
                    .read(unsafe { transmute::<&mut [MaybeUninit<u8>], &mut [u8]>(dst) })
                {
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
        // Since `dst.len() < capacity`, this will not trigger reallocation in `fill_buf`.
        let src = self.fill_exact(needed)?;
        // SAFETY:
        // - `fill_exact` guarantees `src.len() == dst.len()`
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), needed);
            self.consume_unchecked(needed);
        }
        Ok(())
    }

    #[inline]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        // Similar to `copy_into_slice`, the `Reader` trait provides a default implementation of `copy_into_slice_t`,
        // but we override here and pass through to `copy_into_slice` so we can perform direct writes to destinations if
        // requested read sizes are larger than the buffer capacity.
        let len = size_of_val(dst);
        // SAFETY:
        // - `dst` is plain old data, safe to treat as bytes.
        let slice = unsafe { from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), len) };
        self.copy_into_slice(slice)?;
        Ok(())
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    #![expect(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};

    #[test]
    fn fill_buf_errors_when_exceeds_capacity() {
        // fill_buf does NOT grow the buffer - it errors if n_bytes > capacity.
        let mut reader = BufReader::with_capacity(&[1u8, 2, 3][..], 2);
        let result = reader.fill_buf(3);
        assert!(result.is_err());
    }

    #[test]
    fn as_trusted_for_grows_buffer() {
        // as_trusted_for DOES grow the buffer when needed.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 1..100))| {
            let capacity = bytes.len() / 2;
            let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);
            // Request more than capacity - should grow via as_trusted_for
            let mut trusted = unsafe { reader.as_trusted_for(bytes.len()).unwrap() };
            let data = trusted.fill_buf(bytes.len()).unwrap();
            prop_assert_eq!(data, bytes.as_slice());
        });
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
        // Limit size to ensure n_bytes + 1 doesn't exceed default capacity.
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 0..DEFAULT_BUF_SIZE))| {
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
    fn as_trusted_for_errors_when_insufficient() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let result = unsafe { reader.as_trusted_for(bytes.len() + 1) };
            prop_assert!(result.is_err());
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
}
