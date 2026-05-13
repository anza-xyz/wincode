use {super::*, alloc::vec::Vec};

struct VecUnchecked<'a> {
    inner: &'a mut Vec<u8>,
}

impl<'a> VecUnchecked<'a> {
    /// # Safety
    ///
    /// Caller must ensure that `inner` has enough spare capacity for all writes
    /// performed through this unchecked writer, and that those writes stay within
    /// the trusted window reserved by `as_trusted_for`.
    const unsafe fn new(inner: &'a mut Vec<u8>) -> Self {
        Self { inner }
    }
}

impl<'a> Writer for VecUnchecked<'a> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let cur_len = self.inner.len();

        // SAFETY:
        // - The outer `as_trusted_for` call ensured sufficient capacity for the trusted
        //   window before constructing this writer.
        // - The trusted-writer contract requires all writes through this writer,
        //   including forwarded nested trusted writes, to stay within that window.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap with
        //   the internal buffer.
        unsafe {
            core::ptr::copy_nonoverlapping(
                src.as_ptr(),
                self.inner.as_mut_ptr().add(cur_len),
                src.len(),
            );
        }

        unsafe {
            #[expect(clippy::arithmetic_side_effects)]
            self.inner.set_len(cur_len + src.len())
        }

        Ok(())
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
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        self.extend_from_slice(src);
        Ok(())
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        self.reserve(n_bytes);
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of returned `Writer`.
        Ok(unsafe { VecUnchecked::new(self) })
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

            {
                let mut t1 = unsafe { vec.as_trusted_for(bytes.len() - half) }.unwrap();
                t1
                    .write(&bytes[half..half + quarter])
                    .unwrap();

                let mut t2 = unsafe { t1.as_trusted_for(quarter) }.unwrap();
                t2.write(&bytes[half + quarter..]).unwrap();
            }

            prop_assert_eq!(vec, bytes);
        }

        #[test]
        fn vec_writer_trusted_existing(bytes in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let mut vec = vec![0; 5];
            let half = bytes.len() / 2;
            let quarter = half / 2;
            vec.write(&bytes[..half]).unwrap();

            {
                let mut t1 = unsafe { vec.as_trusted_for(bytes.len() - half) }.unwrap();
                t1
                    .write(&bytes[half..half + quarter])
                    .unwrap();

                let mut t2 = unsafe { t1.as_trusted_for(quarter) }.unwrap();
                t2.write(&bytes[half + quarter..]).unwrap();
            }

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

    #[test]
    fn vec_trusted_writer_does_not_extend_len_before_write() {
        let mut vec = Vec::with_capacity(8);
        {
            let _trusted = unsafe { vec.as_trusted_for(8) }.unwrap();
        }

        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn vec_trusted_writer_extends_len_only_for_written_bytes() {
        let mut vec = Vec::with_capacity(8);
        {
            let mut trusted = unsafe { vec.as_trusted_for(8) }.unwrap();
            trusted.write(&[1, 2, 3]).unwrap();
        }

        assert_eq!(vec, [1, 2, 3]);
    }
}
