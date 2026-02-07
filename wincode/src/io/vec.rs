use {super::*, alloc::vec::Vec};

/// Trusted writer for `Vec<u8>` that continues appending to the vector's spare capacity.
///
/// Generally this should not be constructed directly, but rather by calling [`Writer::as_trusted_for`]
/// on a [`Vec<u8>`]. This will ensure that the safety invariants are upheld.
///
/// # Safety
///
/// - This will _not_ grow the vector, and it will not bounds check writes, as it assumes the caller has
///   already reserved enough capacity. The `inner` Vec must have sufficient capacity for all writes.
///   It is UB if this is not upheld.
pub struct TrustedVecWriter<'a> {
    inner: &'a mut Vec<u8>,
}

impl<'a> TrustedVecWriter<'a> {
    const fn new(inner: &'a mut Vec<u8>) -> Self {
        Self { inner }
    }
}

impl Writer for TrustedVecWriter<'_> {
    type Trusted<'b>
        = TrustedVecWriter<'b>
    where
        Self: 'b;

    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let spare = self.inner.spare_capacity_mut();
        // SAFETY: Creator of this writer ensures we have sufficient capacity for all writes.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), spare.as_mut_ptr().cast(), src.len()) };
        // SAFETY: We just wrote `src.len()` bytes to the vector.
        unsafe {
            self.inner
                .set_len(self.inner.len().unchecked_add(src.len()))
        };
        Ok(())
    }

    unsafe fn as_trusted_for(&mut self, _n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        Ok(TrustedVecWriter::new(self.inner))
    }
}

/// Writer implementation for `Vec<u8>` that appends to the vector. The vector will grow as needed.
///
/// # Examples
///
/// Writing to a new vector.
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::io::Writer;
/// let mut vec = Vec::new();
/// let bytes = [1, 2, 3];
/// vec.write(&bytes).unwrap();
/// assert_eq!(vec, &[1, 2, 3]);
/// # }
/// ```
///
/// Writing to an existing vector.
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::io::Writer;
/// let mut vec = vec![1, 2, 3];
/// let bytes = [4, 5, 6];
/// vec.write(&bytes).unwrap();
/// assert_eq!(vec, &[1, 2, 3, 4, 5, 6]);
/// # }
/// ```
///
impl Writer for Vec<u8> {
    type Trusted<'b>
        = TrustedVecWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        self.extend_from_slice(src);
        Ok(())
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        self.reserve(n_bytes);
        // `TrustedVecWriter` will update the length of the vector as it writes.
        Ok(TrustedVecWriter::new(self))
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, alloc::vec, proptest::prelude::*};

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn vec_writer_write_new(bytes in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let mut vec = Vec::new();
            vec.write(&bytes).unwrap();
            prop_assert_eq!(vec, bytes);
        }

        #[test]
        fn vec_writer_write_existing(bytes in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let mut vec = vec![0; 5];
            vec.write(&bytes).unwrap();
            prop_assert_eq!(&vec[..5], &[0; 5]);
            prop_assert_eq!(&vec[5..], bytes);
        }

        #[test]
        fn vec_writer_trusted(bytes in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let mut vec = Vec::new();
            let half = bytes.len() / 2;
            let quarter = half / 2;
            vec.write(&bytes[..half]).unwrap();

            let mut t1 = unsafe { vec.as_trusted_for(bytes.len() - half) }.unwrap();
            t1
                .write(&bytes[half..half + quarter])
                .unwrap();

            let mut t2 = unsafe { t1.as_trusted_for(quarter) }.unwrap();
            t2.write(&bytes[half + quarter..]).unwrap();

            prop_assert_eq!(vec, bytes);
        }

        #[test]
        fn vec_writer_trusted_existing(bytes in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let mut vec = vec![0; 5];
            let half = bytes.len() / 2;
            let quarter = half / 2;
            vec.write(&bytes[..half]).unwrap();

            let mut t1 = unsafe { vec.as_trusted_for(bytes.len() - half) }.unwrap();
            t1
                .write(&bytes[half..half + quarter])
                .unwrap();

            let mut t2 = unsafe { t1.as_trusted_for(quarter) }.unwrap();
            t2.write(&bytes[half + quarter..]).unwrap();

            prop_assert_eq!(&vec[..5], &[0; 5]);
            prop_assert_eq!(&vec[5..], bytes);
        }

        #[test]
        fn test_writer_write_from_t(int in any::<u64>()) {
            let mut writer = Vec::new();
            unsafe { writer.write_t(&int).unwrap() };
            prop_assert_eq!(writer, int.to_le_bytes());
        }

        #[test]
        fn test_writer_write_slice_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            let mut writer = Vec::new();
            unsafe { writer.write_slice_t(&ints).unwrap() };
            prop_assert_eq!(writer, bytes);
        }
    }
}
