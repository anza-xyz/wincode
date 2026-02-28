use {super::*, alloc::vec::Vec, slice::SliceMutUnchecked};

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
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        let size = hint.size();
        let cur_len = self.len();
        self.reserve(size);
        #[allow(clippy::uninit_vec)]
        unsafe {
            self.set_len(cur_len.unchecked_add(size))
        };

        let slice = unsafe {
            from_raw_parts_mut(
                self.as_mut_ptr().cast::<MaybeUninit<u8>>().add(cur_len),
                size,
            )
        };

        Ok(unsafe { SliceMutUnchecked::new(slice) })
    }
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        self.extend_from_slice(src);
        Ok(())
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
                let mut t1 = unsafe { vec.write_hint(bytes.len() - half) }.unwrap();
                t1
                    .write(&bytes[half..half + quarter])
                    .unwrap();

                let mut t2 = unsafe { t1.write_hint(quarter) }.unwrap();
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
                let mut t1 = unsafe { vec.write_hint(bytes.len() - half) }.unwrap();
                t1
                    .write(&bytes[half..half + quarter])
                    .unwrap();

                let mut t2 = unsafe { t1.write_hint(quarter) }.unwrap();
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
}
