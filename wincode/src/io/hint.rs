use core::iter::{once, repeat_n};

#[expect(clippy::len_without_is_empty)]
pub trait Hint {
    /// Iterator over the size of each operation.
    fn iter(&self) -> impl Iterator<Item = usize>;

    /// Aggregate size of all operations.
    #[inline]
    fn size(&self) -> usize {
        self.iter().sum()
    }

    /// Number of operations comprising the hint.
    #[inline]
    fn len(&self) -> usize {
        self.iter().count()
    }

    /// Chunk the aggregate size of the hint by the given chunk size.
    ///
    /// The last value will contain the remainder, if any.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use wincode::io::Hint;
    /// let hint = 512.by(3);
    /// let chunked_by = hint.chunk_by(8192);
    /// assert_eq!(chunked_by.collect::<Vec<_>>(), [1536]);
    /// ```
    ///
    /// ```
    /// # use wincode::io::Hint;
    /// let chunked_by = 512.chunk_by(128);
    /// assert_eq!(chunked_by.collect::<Vec<_>>(), [128, 128, 128, 128]);
    /// ```
    ///
    /// ```
    /// # use wincode::io::Hint;
    /// let chunked_by = 576.chunk_by(128);
    /// assert_eq!(chunked_by.collect::<Vec<_>>(), [128, 128, 128, 128, 64]);
    /// ```
    #[expect(clippy::arithmetic_side_effects)]
    #[inline]
    fn chunk_by(&self, chunk_size: usize) -> impl Iterator<Item = usize> {
        let size = self.size();
        let quotient = size / chunk_size;
        let remainder = size % chunk_size;
        let tail = (remainder != 0).then_some(remainder);
        repeat_n(chunk_size, quotient).chain(tail)
    }

    /// Combine two hints.
    ///
    /// The resulting [`Hint`] implementation will aggregate the
    /// sizes, lengths, and iterators of both hints.
    ///
    /// ```
    /// # use wincode::io::{Hint, Chunks};
    /// let hint = 8.and(512.by(2));
    /// assert_eq!(hint.size(), 1032);
    /// assert_eq!(hint.iter().collect::<Vec<_>>(), [8, 512, 512]);
    /// ```
    #[inline]
    fn and<B>(self, b: B) -> And<Self, B>
    where
        Self: Sized,
    {
        And::new(self, b)
    }

    /// Repeat the size of the hint the given number of times,
    /// creating a `self.size() × n_chunks` hint.
    ///
    /// ```
    /// # use wincode::io::Hint;
    /// let hint = 16.by(64);
    /// assert_eq!(hint.size(), 1024);
    /// assert_eq!(hint.len(), 64);
    /// ```
    #[inline]
    fn by(self, n_chunks: usize) -> Chunks<Self>
    where
        Self: Sized,
    {
        Chunks {
            inner: self,
            n_chunks,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Chunks<T> {
    pub inner: T,
    pub n_chunks: usize,
}

impl<T> Hint for Chunks<T>
where
    T: Hint,
{
    #[inline]
    #[expect(clippy::arithmetic_side_effects)]
    fn size(&self) -> usize {
        self.inner.size() * self.n_chunks
    }

    #[inline]
    fn len(&self) -> usize {
        self.n_chunks
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = usize> {
        repeat_n(self.inner.size(), self.n_chunks)
    }
}

impl Hint for usize {
    #[inline]
    fn size(&self) -> usize {
        *self
    }

    #[inline]
    fn len(&self) -> usize {
        1
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = usize> {
        once(*self)
    }
}

impl<const N: usize, T> Hint for [T; N]
where
    T: Hint,
{
    #[inline]
    fn size(&self) -> usize {
        self.iter().sum()
    }

    #[inline]
    fn len(&self) -> usize {
        self.as_slice().iter().map(|x| x.len()).sum()
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = usize> {
        self.as_slice().iter().flat_map(|x| x.iter())
    }
}

pub struct And<A, B> {
    a: A,
    b: B,
}

impl<A, B> And<A, B> {
    pub fn new(a: A, b: B) -> Self {
        Self { a, b }
    }
}

impl<A, B> Hint for And<A, B>
where
    A: Hint,
    B: Hint,
{
    #[inline]
    #[expect(clippy::arithmetic_side_effects)]
    fn size(&self) -> usize {
        self.a.size() + self.b.size()
    }

    #[inline]
    #[expect(clippy::arithmetic_side_effects)]
    fn len(&self) -> usize {
        self.a.len() + self.b.len()
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = usize> {
        self.a.iter().chain(self.b.iter())
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use {super::*, alloc::vec::Vec};

    fn assert_chunk_by_invariants(hint: impl Hint, chunk_size: usize) {
        let size = hint.size();
        let chunks: Vec<_> = hint.chunk_by(chunk_size).collect();

        assert_eq!(chunks.iter().sum::<usize>(), size);
        assert!(chunks.iter().all(|&n| n > 0 && n <= chunk_size));

        let expected_len = if size == 0 {
            0
        } else {
            size.div_ceil(chunk_size)
        };
        assert_eq!(chunks.len(), expected_len);
    }

    #[test]
    #[should_panic]
    fn chunk_by_zero_panics() {
        let _ = 8usize.chunk_by(0);
    }

    #[test]
    fn chunk_by_invariants_hold_for_various_hints() {
        assert_chunk_by_invariants(0, 8);
        assert_chunk_by_invariants(1, 8);
        assert_chunk_by_invariants(576, 128);
        assert_chunk_by_invariants(512.by(3), 8192);
        assert_chunk_by_invariants([8.by(2), 16.by(1)], 5);
        assert_chunk_by_invariants(8.and(512.by(2)), 64);
    }

    #[test]
    fn and_iter_preserves_order() {
        let hint = 8.and(512.by(2));
        assert_eq!(hint.size(), 1032);
        assert_eq!(hint.len(), 3);
        assert_eq!(hint.iter().collect::<Vec<_>>(), [8, 512, 512]);
    }

    #[test]
    fn array_iter_flattens_inner_hints() {
        let hint = [2.by(2), 3.by(3)];
        assert_eq!(hint.size(), 13);
        assert_eq!(hint.len(), 5);
        assert_eq!(hint.iter().collect::<Vec<_>>(), [2, 2, 3, 3, 3]);
    }

    #[test]
    fn by_repeats_inner_size() {
        let hint = 16.by(4);
        assert_eq!(hint.size(), 64);
        assert_eq!(hint.len(), 4);
        assert_eq!(hint.iter().collect::<Vec<_>>(), [16, 16, 16, 16]);
    }

    #[test]
    fn composite_iter_sum_matches_size() {
        let hint = 8.and(4.by(3)).and([2.by(1), 3.by(2)]);
        let iter = hint.iter().collect::<Vec<_>>();
        assert_eq!(iter, [8, 4, 4, 4, 2, 3, 3]);
        assert_eq!(iter.iter().sum::<usize>(), hint.size());
        assert_eq!(hint.len(), iter.len());
    }
}
