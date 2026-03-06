use std::{
    io::BufRead,
    mem::{transmute, MaybeUninit},
};

use crate::io::{slice::SliceUnchecked, ReadResult, Reader};

pub struct BufReader<R> {
    reader: R,
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

impl<'a, R: BufRead + 'a> Reader<'a> for BufReader<R> {
    fn copy_into_slice(&mut self, mut dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        self.flush_trusted_consume();
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

    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        self.flush_trusted_consume();
        // Two separate fill_buf borrows keep the Slice and Reader paths disjoint.
        // The first borrow is fully released before we decide which path to take.
        // Might be possible to solve with precise use<> lifetime tracking using
        // https://github.com/rust-lang/rust/pull/138128 (Rust >=1.87)
        let buf_len = BufRead::fill_buf(&mut self.reader)?.len();
        if buf_len >= n_bytes {
            // actual consume from `R` needs to happen *after* we no longer use `buf`
            self.consumed_trusted += n_bytes;
            let buf = BufRead::fill_buf(&mut self.reader)?;
            return Ok(TrustedBufReader::<'_, '_, R>::Slice(SliceUnchecked::new(
                &buf[..n_bytes],
            )));
        }
        Ok(TrustedBufReader::<'_, '_, R>::Reader(self))
    }

    fn take_byte(&mut self) -> ReadResult<u8> {
        self.flush_trusted_consume();
        let buf = BufRead::fill_buf(&mut self.reader)?;
        if buf.is_empty() {
            return Err(super::read_size_limit(1));
        }
        let byte = buf[0];
        BufRead::consume(&mut self.reader, 1);
        Ok(byte)
    }
}

enum TrustedBufReader<'s, 'b, R> {
    Slice(SliceUnchecked<'b, u8>),
    Reader(&'s mut BufReader<R>),
}

impl<'a, 's, 'b, R: BufRead> Reader<'a> for TrustedBufReader<'s, 'b, R> {
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
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};

    #[test]
    fn fill_buf_at_capacity() {
        let mut reader = BufReader::with_capacity(&[1u8, 2, 3][..], 2);
        let buf: [u8; 2] = reader.take_array().expect("should return partial buf");
        assert_eq!(buf.as_slice(), &[1u8, 2]);
    }
    #[test]
    fn as_trusted_for_falls_back_when_exceeds_capacity() {
        // When the request exceeds buffer capacity, as_trusted_for falls back to the
        // Reader variant rather than erroring; the returned reader reads correctly.
        let bytes = vec![1u8; 100];
        let capacity = bytes.len() / 2;
        let mut reader = BufReader::with_capacity(bytes.as_slice(), capacity);
        let mut trusted = unsafe { reader.as_trusted_for(bytes.len()).unwrap() };
        let mut dst = Vec::with_capacity(bytes.len());
        trusted.copy_into_slice(dst.spare_capacity_mut()).unwrap();
        unsafe { dst.set_len(bytes.len()) };
        assert_eq!(dst, bytes);
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
                let mut dst = Vec::with_capacity(request);
                trusted.copy_into_slice(dst.spare_capacity_mut()).unwrap();
                unsafe { dst.set_len(request) };
                prop_assert_eq!(&dst, &bytes[offset..offset + request]);
                offset += request;
            }
        });
    }
    #[test]
    fn with_capacity_no_realloc() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::with_capacity(bytes.as_slice(), bytes.len());
            let mut dst = Vec::with_capacity(bytes.len());
            reader.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(bytes.len()) };
            prop_assert_eq!(&dst, &bytes);
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
            prop_assert!(reader.take_array::<1>().is_err());
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
                let mut dst = Vec::with_capacity(half);
                trusted.copy_into_slice(dst.spare_capacity_mut()).unwrap();
                unsafe { dst.set_len(half) };
                prop_assert_eq!(&dst, &bytes[0..half]);
            }
            let tail = bytes.len() - half;
            let mut remaining = Vec::with_capacity(tail);
            reader.copy_into_slice(remaining.spare_capacity_mut()).unwrap();
            unsafe { remaining.set_len(tail) };
            prop_assert_eq!(&remaining, &bytes[half..]);
        });
    }
    #[test]
    fn as_trusted_for_reader_errors_on_read_when_insufficient() {
        // as_trusted_for itself now always succeeds (falling back to Reader when
        // the buffer is too small); the error surfaces on the subsequent read.
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            let mut trusted = unsafe { reader.as_trusted_for(bytes.len() + 1).unwrap() };
            let mut dst = Vec::with_capacity(bytes.len() + 1);
            prop_assert!(trusted.copy_into_slice(dst.spare_capacity_mut()).is_err());
        });
    }
    #[test]
    fn copy_into_slice_transition_from_buffer_to_direct() {
        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 21..100))| {
            // Capacity is 10 bytes; bytes.len() > capacity, so copy_into_slice must
            // loop across multiple BufRead fills.
            let mut reader = BufReader::with_capacity(bytes.as_slice(), 10);
            let mut dst = Vec::with_capacity(bytes.len());
            reader.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(bytes.len()) };
            prop_assert_eq!(&dst, &bytes);
        });
    }
    #[test]
    fn take_byte_consumes_and_advances() {
        proptest!(proptest_cfg(), |(bytes in any::<Vec<u8>>())| {
            let mut reader = BufReader::new(bytes.as_slice());
            for &expected in &bytes {
                prop_assert_eq!(reader.take_byte().unwrap(), expected);
            }
            prop_assert!(reader.take_byte().is_err());
        });
    }
    #[test]
    fn take_byte_flushes_trusted_consume() {
        // After a Slice-path as_trusted_for (consumed_trusted=2), take_byte must
        // flush the deferred consume before reading the next byte.
        let mut reader = BufReader::with_capacity(&[1u8, 2, 3, 4, 5][..], 5);
        {
            let mut trusted = unsafe { reader.as_trusted_for(2).unwrap() };
            let two: [u8; 2] = trusted.take_array().unwrap();
            assert_eq!(two, [1, 2]);
        }
        // flush_trusted_consume advances 2; take_byte reads and consumes byte 3.
        assert_eq!(reader.take_byte().unwrap(), 3);
        assert_eq!(reader.take_byte().unwrap(), 4);
        assert_eq!(reader.take_byte().unwrap(), 5);
        assert!(reader.take_byte().is_err());
    }
}
