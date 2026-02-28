use super::*;

pub struct Iter<I, R> {
    inner: I,
    current: Option<R>,
}

impl<I, R> Iter<I, R> {
    pub const fn new(inner: I) -> Self {
        Self {
            inner,
            current: None,
        }
    }
}

impl<'a, I, R> Reader<'a> for Iter<I, R>
where
    R: Reader<'a>,
    I: Iterator<Item = R>,
{
    #[expect(clippy::arithmetic_side_effects)]
    fn read(&mut self, mut dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        if self.current.is_none() {
            self.current = self.inner.next();
        }
        let Some(mut current) = self.current.as_mut() else {
            return Ok(0);
        };

        let mut read = 0;
        while !dst.is_empty() {
            match current.read(dst) {
                Ok(0) => {
                    let Some(next) = self.inner.next() else {
                        return Ok(read);
                    };
                    self.current = Some(next);
                    current = unsafe { self.current.as_mut().unwrap_unchecked() };
                }
                Ok(n) => {
                    read += n;
                    dst = unsafe { dst.get_unchecked_mut(n..) };
                }
                #[cfg(feature = "std")]
                Err(ReadError::Io(e)) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        Ok(read)
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {
        super::*, crate::proptest_config::proptest_cfg, alloc::vec::Vec, core::iter::empty,
        proptest::prelude::*,
    };

    #[test]
    fn iter_read_empty_returns_zero() {
        let mut iter = Iter::new(empty::<&[u8]>());
        let mut dst = [MaybeUninit::<u8>::uninit(); 8];
        let n = iter.read(&mut dst).unwrap();
        assert_eq!(n, 0);
    }

    #[test]
    fn iter_copy_into_slice_concatenates_chunks() {
        let chunks = [&[1_u8, 2] as &[u8], &[], &[3, 4, 5], &[6], &[], &[7, 8, 9]];
        let expected = [1u8, 2, 3, 4, 5, 6, 7, 8, 9];

        let mut iter = Iter::new(chunks.into_iter());

        let mut dst = Vec::with_capacity(expected.len());
        iter.copy_into_slice(dst.spare_capacity_mut()).unwrap();
        unsafe { dst.set_len(expected.len()) };
        assert_eq!(dst, expected);
    }

    #[test]
    fn iter_copy_into_slice_errors_when_short() {
        let readers = [&[1_u8, 2] as &[u8], &[3]].into_iter();
        let mut iter = Iter::new(readers);

        let mut dst = Vec::<u8>::with_capacity(5);
        let err = iter.copy_into_slice(dst.spare_capacity_mut()).unwrap_err();
        assert!(matches!(err, ReadError::ReadSizeLimit(2)));
    }

    #[test]
    fn iter_copy_into_slice_matches_flattened_chunks() {
        proptest!(proptest_cfg(), |(chunks: Vec<Vec<u8>>)| {
            let expected: Vec<u8> = chunks.iter().flatten().copied().collect();
            let readers = chunks.iter().map(Vec::as_slice);
            let mut iter = Iter::new(readers);

            let mut dst = Vec::with_capacity(expected.len());
            iter.copy_into_slice(dst.spare_capacity_mut()).unwrap();
            unsafe { dst.set_len(expected.len()) };
            prop_assert_eq!(dst, expected);
        });
    }
}
