use std::{
    io::{self, BufRead},
    mem::{transmute, MaybeUninit},
    slice,
};

use crate::io::{ReadResult, Reader, TrustedSliceReader};

pub struct BufReader<R> {
    reader: R,
    /// Bytes consumed by returned trusted reader
    ///
    /// Should be passed on to reader's consume on next opportunity using `&mut self`
    consumed_trusted: usize,
}

impl<R: std::io::Read> BufReader<std::io::BufReader<R>> {
    pub fn with_capacity(r: R, capacity: usize) -> Self {
        Self {
            reader: std::io::BufReader::with_capacity(capacity, r),
            consumed_trusted: 0,
        }
    }

    pub fn new(r: R) -> Self {
        Self {
            reader: std::io::BufReader::new(r),
            consumed_trusted: 0,
        }
    }
}

impl<R: BufRead> BufReader<R> {
    fn flush_trusted_consume(&mut self) {
        if self.consumed_trusted > 0 {
            self.reader.consume(self.consumed_trusted);
            self.consumed_trusted = 0;
        }
    }
}

impl<'a, R: BufRead> Reader<'a> for BufReader<R> {
    type Trusted<'b>
        = TrustedSliceReader<'a, 'b>
    where
        Self: 'b;

    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        self.flush_trusted_consume();
        let buf = BufRead::fill_buf(&mut self.reader)?;
        if buf.len() <= n_bytes {
            Ok(buf)
        } else {
            Ok(&buf[..n_bytes])
        }
    }

    unsafe fn consume_unchecked(&mut self, amt: usize) {
        BufRead::consume(&mut self.reader, amt);
    }

    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if BufRead::fill_buf(&mut self.reader)?.len() < amt {
            return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "not enough bytes").into());
        }
        BufRead::consume(&mut self.reader, amt);
        Ok(())
    }

    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        self.flush_trusted_consume();
        let buf = BufRead::fill_buf(&mut self.reader)?;
        if buf.len() >= n_bytes {
            // actual consume from `R` needs to happen *after* we no longer use `buf`
            self.consumed_trusted += n_bytes;
            Ok(TrustedSliceReader::new(&buf[..n_bytes]))
        } else {
            Err(io::Error::new(io::ErrorKind::UnexpectedEof, "not enough bytes").into())
        }
    }

    fn fill_exact(&mut self, _n_bytes: usize) -> ReadResult<&[u8]> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "fill_exact not supported").into())
    }

    fn fill_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        Err(io::Error::new(io::ErrorKind::Unsupported, "fill_array not supported").into())
    }

    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let mut arr = MaybeUninit::uninit();
        self.copy_into_array(&mut arr)?;
        Ok(unsafe { arr.assume_init() })
    }

    fn peek(&mut self) -> ReadResult<&u8> {
        BufRead::fill_buf(&mut self.reader)?
            .first()
            .ok_or_else(|| super::read_size_limit(1))
    }

    fn copy_into_slice(&mut self, mut dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        while !dst.is_empty() {
            let buf = BufRead::fill_buf(&mut self.reader)?;
            let len = buf.len().min(dst.len());
            if len == 0 {
                return Err(super::read_size_limit(len));
            }
            let (dst_prefix, rest) = unsafe { dst.split_at_mut_unchecked(len) };
            dst_prefix.copy_from_slice(unsafe { transmute(&buf[..len]) });
            BufRead::consume(&mut self.reader, len);
            dst = rest;
        }
        Ok(())
    }

    fn copy_into_array<const N: usize>(
        &mut self,
        dst: &mut MaybeUninit<[u8; N]>,
    ) -> ReadResult<()> {
        let dst = unsafe {
            let ptr = dst.as_mut_ptr() as *mut MaybeUninit<u8>;
            slice::from_raw_parts_mut(ptr, N)
        };
        self.copy_into_slice(dst)
    }

    unsafe fn copy_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        let len = size_of::<T>();
        let dst = unsafe {
            let ptr = dst.as_mut_ptr() as *mut MaybeUninit<u8>;
            slice::from_raw_parts_mut(ptr, len)
        };
        self.copy_into_slice(dst)
    }

    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        let len = size_of_val(dst);
        let dst = unsafe {
            let ptr = dst.as_mut_ptr() as *mut MaybeUninit<u8>;
            slice::from_raw_parts_mut(ptr, len)
        };
        self.copy_into_slice(dst)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};
    const DEFAULT_BUF_SIZE: usize = 8 * 1024;

    #[test]
    fn fill_buf_at_capacity() {
        let mut reader = BufReader::with_capacity(&[1u8, 2, 3][..], 2);
        let buf = reader.fill_buf(3).expect("should return partial buf");
        assert_eq!(buf, &[1u8, 2]);
    }
    #[test]
    fn as_trusted_for_err_on_too_large_request() {
        let bytes = vec![1; 100];
        let capacity = bytes.len() / 2;
        let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);
        assert!(unsafe { reader.as_trusted_for(bytes.len()).is_err() });
    }

    #[test]
    fn as_trusted_within_capacity_in_chunks() {
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 1..100))| {
            // Choose a capacity that is <= total length so we exercise multiple fills,
            let capacity = bytes.len().div_ceil(2);
            let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);
            let mut offset = 0usize;
            while offset < bytes.len() {
                let remaining = bytes.len() - offset;
                let request = capacity.min(remaining);
                // Always request at most `capacity`, so we never ask for more than the buffer can hold in one go.
                let mut trusted = unsafe { reader.as_trusted_for(request).unwrap() };
                let data = trusted.fill_buf(request).unwrap();
                assert_eq!(request, data.len());
                prop_assert_eq!(data, &bytes[offset..offset + data.len()]);
                trusted.consume(request).unwrap();
                offset += request;
            }
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
    fn fill_exact_returns_err() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            assert!(reader.fill_exact(bytes.len()).is_err());
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
            let mut reader = BufReader::with_capacity(bytes.as_slice(), bytes.len().div_ceil(2));
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
            let half = bytes.len().div_ceil(2);
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
    fn fill_buf_fragmented() {
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
            prop_assert_eq!(data, &bytes[5..15]);
            reader.consume(10).unwrap();
            let data = reader.fill_buf(2).unwrap();
            prop_assert_eq!(data, &bytes[15..17]);
        });
    }
    #[test]
    fn fill_buf_fragmented_1() {
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
            // Request for more than remaining hits fragmented data.
            let request = remaining + 1;
            let buf = reader.fill_buf(request).unwrap();
            prop_assert_eq!(buf, &bytes[consume_amt..consume_amt + remaining]);
            reader.consume(remaining).unwrap();
            let buf = reader.fill_buf(request - remaining).unwrap();
            prop_assert_eq!(buf, &bytes[consume_amt + remaining..consume_amt + request]);
        });
    }
}
