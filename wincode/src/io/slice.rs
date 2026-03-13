use {
    super::*,
    core::{marker::PhantomData, ptr::copy_nonoverlapping},
};

/// Split the given mutable slice by `len` bytes, advancing the slice by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline(always)]
fn advance_slice_mut_checked<'a, T>(input: &mut &'a mut [T], len: usize) -> Option<&'a mut [T]> {
    let (dst, rest) = mem::take(input).split_at_mut_checked(len)?;
    *input = rest;
    Some(dst)
}

/// Split the given mutable slice by `len` bytes, advancing the slice by `len` bytes.
///
/// # Safety
///
/// Calling this method with an out-of-bounds `len` is undefined behavior
/// even if the resulting reference is not used. The caller has to ensure that
/// `0 <= len <= self.len()`.
#[inline(always)]
unsafe fn advance_slice_mut_unchecked<'a, T>(input: &mut &'a mut [T], len: usize) -> &'a mut [T] {
    let (dst, rest) = unsafe { mem::take(input).split_at_mut_unchecked(len) };
    *input = rest;
    dst
}

/// Split the given slice by `len` bytes, advancing the slice by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline(always)]
fn advance_slice_checked<'a, T>(input: &mut &'a [T], len: usize) -> Option<&'a [T]> {
    let (dst, rest) = input.split_at_checked(len)?;
    *input = rest;
    Some(dst)
}

/// Split the given slice by `len` bytes, advancing the slice by `len` bytes.
///
/// # Safety
///
/// Calling this method with an out-of-bounds `len` is undefined behavior
/// even if the resulting reference is not used. The caller has to ensure that
/// `0 <= len <= self.len()`.
#[inline(always)]
unsafe fn advance_slice_unchecked<'a, T>(input: &mut &'a [T], len: usize) -> &'a [T] {
    let (dst, rest) = unsafe { input.split_at_unchecked(len) };
    *input = rest;
    dst
}

/// Implementation of [`Reader`] over a slice that does not perform any bounds checks.
///
/// This implementation inherits the lifetime of the underlying slice, and can be used
/// for zero-copy [`Reader`] implementations.
pub struct SliceUnchecked<'a, T> {
    buf: &'a [T],
}

impl<'a, T> SliceUnchecked<'a, T> {
    /// Create a new [`SliceUnchecked`] from the given slice.
    ///
    /// # Safety
    ///
    /// [`SliceUnchecked`]'s implementation of [`Reader`] will not perform any
    /// bounds checks on the slice. It is up to the caller to ensure that any
    /// [`Reader`] operations performed are within the bounds of the slice.
    pub const unsafe fn new(buf: &'a [T]) -> Self {
        Self { buf }
    }
}

impl<'a> Reader<'a> for SliceUnchecked<'a, u8> {
    #[inline]
    fn copy_into_slice(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        // SAFETY: by constructing `SliceUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, buf.len()) };
        // SAFETY:
        // -  Given the previous assumption that the caller guarantees the underlying
        //    slice in bounds for the next `buf.len()` bytes, we assume that `chunk` is a valid,
        //    in bounds, `buf.len()` bytes slice.
        // - Given Rust's aliasing rules, we can assume that `buf` does not overlap with the internal buffer.
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        // SAFETY: by constructing `SliceUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, N) };
        // SAFETY: given the previous assumption that the caller guarantees the underlying
        // slice in bounds for the next `N` bytes, we assume that `chunk` is a valid
        // `&[u8; N]` slice.
        Ok(unsafe { *(chunk.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        // SAFETY: by constructing `SliceUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, len) };
        Ok(chunk)
    }

    #[inline]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.take_borrowed(len)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        unsafe { advance_slice_unchecked(&mut self.buf, amt) };
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        // SAFETY: by constructing `SliceUnchecked`, caller guarantees
        // they will read and consume within the bounds of the slice.
        unsafe { self.consume_unchecked(amt) }
    }

    #[inline]
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        // SAFETY: by constructing `SliceUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        unsafe { Ok(&*(self.buf.as_ptr().cast::<[u8; N]>())) }
    }
}

/// Implementation of [`Reader`] and [`Writer`] over a slice that does not perform any bounds checks.
///
/// This implementation inherits the lifetime of the underlying slice, and can be used
/// for zero-copy [`Reader`] implementations.
pub struct SliceMutUnchecked<'a, T> {
    buf: &'a mut [T],
}

#[cfg(test)]
impl<T> core::ops::Deref for SliceMutUnchecked<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.buf
    }
}

impl<'a, T> SliceMutUnchecked<'a, T> {
    /// Create a new [`SliceMutUnchecked`] from the given slice.
    ///
    /// # Safety
    ///
    /// [`SliceMutUnchecked`]'s implementation of [`Reader`] and [`Writer`] will
    /// not perform any bounds checks on the slice. It is up to the caller to
    /// ensure that any [`Reader`] or [`Writer`] operations performed are within
    /// the bounds of the slice.
    ///
    /// ## Reading
    ///
    /// - The total number of bytes accessed/consumed must be within
    ///   the bounds of the slice.
    ///
    /// ## Writing
    ///
    /// - All writes performed must stay within the bounds of the slice.
    /// - It is permitted to overwrite the same bytes multiple times.
    pub const unsafe fn new(buf: &'a mut [T]) -> Self {
        Self { buf }
    }
}

impl<'a> Reader<'a> for SliceMutUnchecked<'a, u8> {
    #[inline]
    fn copy_into_slice(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, buf.len()) };
        // SAFETY:
        // -  Given the previous assumption that the caller guarantees the underlying
        //    slice in bounds for the next `buf.len()` bytes, we assume that `chunk` is a valid,
        //    in bounds, `buf.len()` bytes slice.
        // - Given Rust's aliasing rules, we can assume that `buf` does not overlap with the internal buffer.
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, N) };
        // SAFETY: given the previous assumption that the caller guarantees the underlying
        // slice in bounds for the next `N` bytes, we assume that `chunk` is a valid
        // `&[u8; N]` slice.
        Ok(unsafe { *(chunk.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn take_borrowed_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        Ok(unsafe { advance_slice_mut_unchecked(&mut self.buf, len) })
    }

    #[inline]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        self.take_borrowed_mut(len).map(|s| &*s)
    }

    #[inline]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.take_borrowed(len)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        unsafe { advance_slice_mut_unchecked(&mut self.buf, amt) };
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        unsafe { self.consume_unchecked(amt) }
    }

    #[inline]
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will read within the bounds of the slice.
        unsafe { Ok(&*(self.buf.as_ptr().cast::<[u8; N]>())) }
    }
}

/// Implementation of [`Reader`] over a slice that does not perform any bounds checks.
///
/// This implementation inherits the lifetime of its lexical scope, and can be used
/// for non-borrowing [`Reader`] implementations.
pub struct SliceScopedUnchecked<'a, 'b, T> {
    inner: SliceUnchecked<'b, T>,
    _marker: PhantomData<&'a [T]>,
}

impl<'b, T> SliceScopedUnchecked<'_, 'b, T> {
    /// Create a new [`SliceScopedUnchecked`] from the given slice.
    ///
    /// # Safety
    ///
    /// [`SliceScopedUnchecked`]'s implementation of [`Reader`] will not perform any
    /// bounds checks on the slice. It is up to the caller to ensure that any
    /// [`Reader`] operations performed are within the bounds of the slice.
    #[inline(always)]
    pub const unsafe fn new(buf: &'b [T]) -> Self {
        Self {
            inner: unsafe { SliceUnchecked::new(buf) },
            _marker: PhantomData,
        }
    }
}

impl<'a> Reader<'a> for SliceScopedUnchecked<'a, '_, u8> {
    #[inline(always)]
    fn copy_into_slice(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        self.inner.copy_into_slice(buf)
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        self.inner.take_array()
    }

    #[inline(always)]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.inner.take_scoped(len)
    }

    #[inline(always)]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        unsafe { self.inner.consume_unchecked(amt) }
    }

    #[inline(always)]
    fn consume(&mut self, amt: usize) {
        self.inner.consume(amt)
    }

    #[inline(always)]
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        self.inner.peek_array()
    }
}

impl<'a> Reader<'a> for &'a [u8] {
    #[inline]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let Some(src) = advance_slice_checked(self, len) else {
            return Err(read_size_limit(len));
        };
        Ok(src)
    }

    #[inline(always)]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.take_borrowed(len)
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let Some(src) = advance_slice_checked(self, dst.len()) else {
            return Err(read_size_limit(dst.len()));
        };
        // SAFETY:
        // - `advance_slice_checked` guarantees that `src` is exactly `dst.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `dst` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) };
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let Some((src, rest)) = self.split_first_chunk() else {
            return Err(read_size_limit(N));
        };
        *self = rest;
        Ok(*src)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        *self = unsafe { self.get_unchecked(amt..) };
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        *self = &self[amt.min(self.len())..];
    }

    #[inline]
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        let Some(src) = self.first_chunk() else {
            return Err(read_size_limit(N));
        };
        Ok(src)
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        let Some(window) = advance_slice_checked(self, n_bytes) else {
            return Err(read_size_limit(n_bytes));
        };
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will will not read beyond the bounds of the slice, `n_bytes`.
        Ok(unsafe { SliceUnchecked::new(window) })
    }
}

impl<'a> Reader<'a> for &'a mut [u8] {
    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        let Some(window) = advance_slice_mut_checked(self, n_bytes) else {
            return Err(read_size_limit(n_bytes));
        };
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will will not read beyond the bounds of the slice, `n_bytes`.
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline]
    fn take_borrowed_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        let Some(src) = advance_slice_mut_checked(self, len) else {
            return Err(read_size_limit(len));
        };
        Ok(src)
    }

    #[inline]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        self.take_borrowed_mut(len).map(|s| &*s)
    }

    #[inline]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.take_borrowed(len)
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = self.take_borrowed(dst.len())?;
        // SAFETY:
        // - `borrow_exact` guarantees that `src` is exactly dst.len() bytes.
        // - Given Rust's aliasing rules, we can assume that `buf` does not overlap with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) }
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let Some((src, rest)) = mem::take(self).split_first_chunk_mut() else {
            return Err(read_size_limit(N));
        };
        *self = rest;
        Ok(*src)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        *self = unsafe { mem::take(self).get_unchecked_mut(amt..) };
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        let this = mem::take(self);
        let len = this.len();
        *self = &mut this[amt.min(len)..];
    }

    #[inline]
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        let Some(src) = self.first_chunk() else {
            return Err(read_size_limit(N));
        };
        Ok(src)
    }
}

impl Writer for SliceMutUnchecked<'_, u8> {
    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will write within the bounds of the slice.
        let dst = unsafe { advance_slice_mut_unchecked(&mut self.buf, src.len()) };
        // SAFETY:
        // -  Given the previous assumption that the caller guarantees the underlying
        //    slice in bounds for the next `buf.len()` bytes, we assume that `dst` is a valid,
        //    in bounds, `src.len()` bytes slice.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }
        Ok(())
    }
}

impl Writer for SliceMutUnchecked<'_, MaybeUninit<u8>> {
    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        // SAFETY: by constructing `SliceMutUnchecked`, caller guarantees
        // they will write within the bounds of the slice.
        let dst = unsafe { advance_slice_mut_unchecked(&mut self.buf, src.len()) };
        // SAFETY:
        // -  Given the previous assumption that the caller guarantees the underlying
        //    slice in bounds for the next `buf.len()` bytes, we assume that `dst` is a valid,
        //    in bounds, `src.len()` bytes slice.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }
        Ok(())
    }
}

impl Writer for &mut [MaybeUninit<u8>] {
    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        let Some(window) = advance_slice_mut_checked(self, n_bytes) else {
            return Err(write_size_limit(n_bytes));
        };
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of the slice.
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let Some(dst) = advance_slice_mut_checked(self, src.len()) else {
            return Err(write_size_limit(src.len()));
        };

        // SAFETY: `advance_slice_mut_checked` guarantees that `dst` is exactly `src.len()` bytes.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }
        Ok(())
    }
}

impl Writer for &mut [u8] {
    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        let Some(window) = advance_slice_mut_checked(self, n_bytes) else {
            return Err(write_size_limit(n_bytes));
        };
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of the slice.
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let Some(dst) = advance_slice_mut_checked(self, src.len()) else {
            return Err(write_size_limit(src.len()));
        };

        // SAFETY:
        // - `advance_slice_mut_checked` guarantees that `dst` is exactly `src.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }
        Ok(())
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, alloc::vec::Vec, proptest::prelude::*};

    #[test]
    fn test_reader_peek_byte() {
        let mut reader = b"hello" as &[u8];
        assert!(matches!(reader.peek_byte(), Ok(b'h')));
    }

    #[test]
    fn test_reader_peek_byte_empty() {
        let mut reader = b"" as &[u8];
        assert!(matches!(
            reader.peek_byte(),
            Err(ReadError::ReadSizeLimit(1))
        ));
    }

    /// Execute the given block with supported readers.
    macro_rules! with_readers {
        ($bytes:expr, |$reader:ident| $body:block) => {{
            {
                let mut $reader = $bytes.as_slice();
                $body
            }
            {
                let mut $reader = unsafe { SliceUnchecked::new($bytes) };
                $body
            }
            {
                let mut $reader = Cursor::new($bytes);
                $body
            }
        }};
    }

    /// Execute the given block with readers that will bounds check (and thus not panic).
    macro_rules! with_untrusted_readers {
        ($bytes:expr, |$reader:ident| $body:block) => {{
            {
                let mut $reader = $bytes.as_slice();
                $body
            }
            {
                let mut $reader = Cursor::new($bytes);
                $body
            }
        }};
    }

    /// Execute the given block with slice reference writer and trusted slice writer for the given buffer.
    macro_rules! with_writers {
        ($buffer:expr, |$writer:ident| $body:block) => {{
            {
                let mut $writer = $buffer.spare_capacity_mut();
                $body
                $buffer.clear();
            }
            {
                let mut $writer = unsafe { SliceMutUnchecked::new($buffer.spare_capacity_mut()) };
                $body
                $buffer.clear();
            }
            {
                let _capacity = $buffer.capacity();
                $buffer.resize(_capacity, 0);
                let mut $writer = $buffer.as_mut_slice();
                $body
                $buffer.clear();
            }
        }};
    }

    // Execute the given block with slice writer of the given preallocated buffer.
    macro_rules! with_known_len_writers {
        ($buffer:expr, |$writer:ident| $body_write:block, $body_check:expr) => {{
            let capacity = $buffer.capacity();
            {
                $buffer.resize(capacity, 0);
                $buffer.fill(0);
                let mut $writer = $buffer.as_mut_slice();
                $body_write
                $body_check;
                $buffer.clear();
            }
            {
                $buffer.fill(0);
                $buffer.clear();
                let mut $writer = $buffer.spare_capacity_mut();
                $body_write
                unsafe { $buffer.set_len(capacity) }
                $body_check;
            }
        }};
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_reader_copy_into_slice(bytes in any::<Vec<u8>>()) {
            with_readers!(&bytes, |reader| {
                let mut vec = Vec::with_capacity(bytes.len());
                let half = bytes.len() / 2;
                let dst = vec.spare_capacity_mut();
                reader.copy_into_slice(&mut dst[..half]).unwrap();
                unsafe { reader.as_trusted_for(bytes.len() - half) }
                    .unwrap()
                    .copy_into_slice(&mut dst[half..])
                    .unwrap();
                unsafe { vec.set_len(bytes.len()) };
                prop_assert_eq!(&vec, &bytes);
            });
        }

        #[test]
        fn test_reader_take_scoped(bytes in any::<Vec<u8>>()) {
            with_readers!(&bytes, |reader| {
                let read = reader.take_scoped(bytes.len()).unwrap();
                prop_assert_eq!(&read, &bytes);
            });
        }

        #[test]
        fn reader_take_scoped_input_too_large(bytes in any::<Vec<u8>>()) {
            with_untrusted_readers!(&bytes, |reader| {
                prop_assert!(matches!(reader.take_scoped(bytes.len() + 1), Err(ReadError::ReadSizeLimit(x)) if x == bytes.len() + 1));
            });
        }

        #[test]
        fn test_reader_copy_into_slice_input_too_large(bytes in any::<Vec<u8>>()) {
            with_untrusted_readers!(&bytes, |reader| {
                let mut vec = Vec::with_capacity(bytes.len() + 1);
                let dst = vec.spare_capacity_mut();
                prop_assert!(matches!(reader.copy_into_slice(dst), Err(ReadError::ReadSizeLimit(x)) if x == bytes.len() + 1));
            });
        }

        #[test]
        fn test_reader_consume(bytes in any::<Vec<u8>>()) {
            with_untrusted_readers!(&bytes, |reader| {
                reader.consume(bytes.len());
                prop_assert!(matches!(reader.peek_byte(), Err(ReadError::ReadSizeLimit(1))));
            });
        }

        #[test]
        fn test_reader_copy_into_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_readers!(&bytes, |reader| {
                for int in &ints {
                    let mut val = MaybeUninit::<u64>::uninit();
                    unsafe { reader.copy_into_t(&mut val).unwrap() };
                    unsafe { prop_assert_eq!(val.assume_init(), *int) };
                }
            });
        }

        #[test]
        fn test_reader_copy_into_slice_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_readers!(&bytes, |reader| {
                let mut vals: Vec<u64> = Vec::with_capacity(ints.len());
                let dst = vals.spare_capacity_mut();
                unsafe { reader.copy_into_slice_t(dst).unwrap() };
                unsafe { vals.set_len(ints.len()) };
                prop_assert_eq!(&vals, &ints);
            });
        }

        #[test]
        fn test_writer_write(bytes in any::<Vec<u8>>()) {
            let capacity = bytes.len();
            let mut buffer = Vec::with_capacity(capacity);
            with_writers!(&mut buffer, |writer| {
                writer.write(&bytes).unwrap();
                let written = capacity - writer.len();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &bytes);
            });

            with_known_len_writers!(&mut buffer, |writer| {
                writer.write(&bytes).unwrap();
            }, prop_assert_eq!(&buffer, &bytes));
        }

        #[test]
        fn test_writer_write_input_too_large(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len() - 1);
            let mut writer = buffer.spare_capacity_mut();
            prop_assert!(matches!(writer.write(&bytes), Err(WriteError::WriteSizeLimit(x)) if x == bytes.len()));
        }

        #[test]
        fn test_writer_write_t(int in any::<u64>()) {
            let capacity = 8;
            let mut buffer = Vec::with_capacity(capacity);
            with_writers!(&mut buffer, |writer| {
                unsafe { writer.write_t(&int).unwrap() };
                let written = capacity - writer.len();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &int.to_le_bytes());
            });

            with_known_len_writers!(&mut buffer, |writer| {
                unsafe { writer.write_t(&int).unwrap() };
            }, prop_assert_eq!(&buffer, &int.to_le_bytes()));
        }

        #[test]
        fn test_writer_write_slice_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            let capacity = bytes.len();
            let mut buffer = Vec::with_capacity(capacity);
            with_writers!(&mut buffer, |writer| {
                unsafe { writer.write_slice_t(&ints).unwrap() };
                let written = capacity - writer.len();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &bytes);
            });

            with_known_len_writers!(&mut buffer, |writer| {
                unsafe { writer.write_slice_t(&ints).unwrap() };
            }, prop_assert_eq!(&buffer, &bytes));
        }
    }
}
