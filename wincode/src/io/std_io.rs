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
/// Note this implementation differs than [`std::io::BufRead`]
/// semantics in that wincode [`Reader`]s take an `n_bytes` argument.
/// Importantly, implementations should try to read at least `n_bytes`
/// bytes, retrying until either `n_bytes` are read or EOF is hit.
#[expect(clippy::arithmetic_side_effects)]
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
    let needed = n_bytes - buffered_len;

    // User requested more bytes than we have space for in the buffer.
    //
    // In this case, we need to shift the existing bytes to the beginning of the buffer.
    // This may allow us to skip a reallocation if buf.capacity() - filled.len() >= needed.
    if needed > buf.capacity() - filled.end {
        // Check if we need to reallocate the buffer.
        if n_bytes > buf.capacity() {
            // Need to reallocate - copy directly to new buffer rather than shifting (copying) and reallocating.
            let mut new_buf = Vec::with_capacity(n_bytes.next_power_of_two());
            // Copy the existing bytes to the new buffer.
            // SAFETY:
            // - `filled` always points to an initialized portion of the buffer.
            // - `new_buf` is valid for `buffered_len` bytes.
            unsafe {
                ptr::copy_nonoverlapping(
                    buf.as_ptr().add(filled.start),
                    new_buf.as_mut_ptr(),
                    buffered_len,
                );
                new_buf.set_len(buffered_len);
            }
            *buf = new_buf;
        } else {
            // Just need to compact the buffer.

            // SAFETY: `filled` always points to an initialized portion of the buffer.
            let src = unsafe { buf.as_ptr().add(filled.start) };
            let dst = buf.as_mut_ptr();
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
            unsafe { buf.set_len(buffered_len) }
        }

        *filled = 0..buffered_len;
    }

    let mut read = 0;
    // SAFETY:
    // - `filled.end` is always less than `buf.capacity()`.
    // - We've verified above that we have enough capacity for `needed` relative to `filled.end`.
    let mut dst = unsafe {
        from_raw_parts_mut(
            buf.as_mut_ptr().cast::<MaybeUninit<u8>>().add(filled.end),
            buf.capacity() - filled.end,
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
    #[expect(clippy::arithmetic_side_effects)]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        self.filled.start += amt;
        // Reset the range if we've consumed all the bytes.
        if self.filled.is_empty() {
            self.filled = 0..0;
        }
    }

    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if self.filled.len() < amt {
            return Err(read_size_limit(amt));
        }
        // SAFETY: We just checked that `filled.len() >= amt`.
        unsafe { self.consume_unchecked(amt) };
        Ok(())
    }

    #[expect(clippy::arithmetic_side_effects)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        let buffer = fill_buf(&mut self.inner, &mut self.buf, &mut self.filled, n_bytes)?;
        if buffer.len() != n_bytes {
            return Err(read_size_limit(n_bytes));
        }
        // Contract of `as_trusted_for` specifies that the returned reader will consume all `n_bytes`.
        self.filled.start += n_bytes;
        if self.filled.is_empty() {
            self.filled = 0..0;
        }
        Ok(TrustedSliceReader::new(buffer))
    }

    fn copy_into_slice(&mut self, mut dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        // The `Reader` trait provides a default implementation of `copy_into_slice`, but we provide
        // an optimization here that will avoid excessive copying and reallocation
        // when the required reads are large.

        // Drain whatever we have in the buffer to dst.
        let len_buffered = self.filled.len();
        if len_buffered > 0 {
            let to_copy = dst.len().min(len_buffered);
            let src = self.buffer();
            // SAFETY:
            // - `src` is valid for `len_buffered`
            // - `dst` is valid for `dst.len()`
            // - `to_copy` is min of both.
            unsafe {
                ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), to_copy);
                self.consume_unchecked(to_copy);
            }

            if to_copy == dst.len() {
                return Ok(());
            }

            // Advance dst
            // SAFETY: `to_copy` < `dst.len()` checked above.
            dst = unsafe { dst.get_unchecked_mut(to_copy..) };
        }

        // If the remaining requirement is large (>= capacity), read directly.
        // Note: buffer is guaranteed empty here because we drained it above and didn't return.
        if dst.len() >= self.buf.capacity() {
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
        let src = self.fill_exact(dst.len())?;
        // SAFETY:
        // - `fill_exact` guarantees `src.len() == dst.len()`
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), dst.len());
            self.consume_unchecked(dst.len());
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
    fn with_capacity_zero_realloc() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::with_capacity(bytes.as_slice(), 0);
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
