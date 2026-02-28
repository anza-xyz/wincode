use {super::*, core::marker::PhantomData, std::ptr::copy_nonoverlapping};

/// Get a slice of `len` bytes for writing, advancing the writer by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline(always)]
fn advance_slice_mut_checked<'a, T>(input: &mut &'a mut [T], len: usize) -> Option<&'a mut [T]> {
    let (dst, rest) = mem::take(input).split_at_mut_checked(len)?;
    *input = rest;
    Some(dst)
}

/// Get a slice of `len` bytes for writing, advancing the writer by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline(always)]
unsafe fn advance_slice_mut_unchecked<'a, T>(input: &mut &'a mut [T], len: usize) -> &'a mut [T] {
    let (dst, rest) = unsafe { mem::take(input).split_at_mut_unchecked(len) };
    *input = rest;
    dst
}

/// Get a slice of `len` bytes for writing, advancing the writer by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline(always)]
fn advance_slice_checked<'a, T>(input: &mut &'a [T], len: usize) -> Option<&'a [T]> {
    let (dst, rest) = input.split_at_checked(len)?;
    *input = rest;
    Some(dst)
}

/// Get a slice of `len` bytes for writing, advancing the writer by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline(always)]
unsafe fn advance_slice_unchecked<'a, T>(input: &mut &'a [T], len: usize) -> &'a [T] {
    let (dst, rest) = unsafe { input.split_at_unchecked(len) };
    *input = rest;
    dst
}

pub struct SliceUnchecked<'a, T> {
    buf: &'a [T],
}

impl<'a, T> SliceUnchecked<'a, T> {
    #[inline(always)]
    pub const unsafe fn new(buf: &'a [T]) -> Self {
        Self { buf }
    }
}

impl<'a> Reader<'a> for SliceUnchecked<'a, u8> {
    #[inline]
    fn read(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        let len = dst.len().min(self.buf.len());
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, len) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), dst.as_mut_ptr().cast(), len) };
        Ok(len)
    }

    #[inline]
    fn copy_into_slice(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, buf.len()) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, N) };
        Ok(unsafe { *(chunk.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, len) };
        Ok(chunk)
    }
}

pub struct SliceMutUnchecked<'a, T> {
    buf: &'a mut [T],
}

impl<'a, T> SliceMutUnchecked<'a, T> {
    #[inline(always)]
    pub const unsafe fn new(buf: &'a mut [T]) -> Self {
        Self { buf }
    }
}

impl<'a> Reader<'a> for SliceMutUnchecked<'a, u8> {
    #[inline]
    fn read(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        let len = dst.len().min(self.buf.len());
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, len) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), dst.as_mut_ptr().cast(), len) };
        Ok(len)
    }

    #[inline]
    fn copy_into_slice(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, buf.len()) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, N) };
        Ok(unsafe { *(chunk.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        Ok(unsafe { advance_slice_mut_unchecked(&mut self.buf, len) })
    }
}

pub struct SliceScopedUnchecked<'a, 'b, T> {
    inner: SliceUnchecked<'b, T>,
    _marker: PhantomData<&'a [T]>,
}

impl<'b, T> SliceScopedUnchecked<'_, 'b, T> {
    #[inline(always)]
    pub const unsafe fn new(buf: &'b [T]) -> Self {
        Self {
            inner: unsafe { SliceUnchecked::new(buf) },
            _marker: PhantomData,
        }
    }
}
impl<'a> Reader<'a> for SliceScopedUnchecked<'a, '_, u8> {
    #[inline]
    fn read(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        self.inner.read(dst)
    }

    #[inline(always)]
    fn copy_into_slice(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        self.inner.copy_into_slice(buf)
    }

    #[inline]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        self.inner.take_array()
    }
}

impl<'a> Reader<'a> for &'a [u8] {
    #[inline]
    fn read(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        let len = dst.len().min(self.len());
        let chunk = unsafe { advance_slice_unchecked(self, len) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), dst.as_mut_ptr().cast(), len) };
        Ok(len)
    }

    #[inline(always)]
    unsafe fn read_hint(&mut self, hint: impl Hint) -> ReadResult<impl Reader<'a>> {
        let size = hint.size();
        let Some(window) = advance_slice_checked(self, size) else {
            return Err(read_size_limit(size));
        };
        Ok(unsafe { SliceUnchecked::new(window) })
    }

    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let Some(src) = advance_slice_checked(self, len) else {
            return Err(read_size_limit(len));
        };
        Ok(src)
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let Some(src) = advance_slice_checked(self, dst.len()) else {
            return Err(read_size_limit(dst.len()));
        };
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
}

impl<'a> Reader<'a> for &'a mut [u8] {
    #[inline]
    fn read(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        let len = dst.len().min(self.len());
        let chunk = unsafe { advance_slice_mut_unchecked(self, len) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), dst.as_mut_ptr().cast(), len) };
        Ok(len)
    }

    #[inline(always)]
    unsafe fn read_hint(&mut self, hint: impl Hint) -> ReadResult<impl Reader<'a>> {
        let size = hint.size();
        let Some(window) = advance_slice_mut_checked(self, size) else {
            return Err(read_size_limit(size));
        };
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        let Some(src) = advance_slice_mut_checked(self, len) else {
            return Err(read_size_limit(len));
        };
        Ok(src)
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = self.borrow_exact(dst.len())?;
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) };
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
}

impl Writer for SliceMutUnchecked<'_, u8> {
    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = unsafe { advance_slice_mut_unchecked(&mut self.buf, src.len()) };
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) };
        Ok(())
    }
}

impl Writer for SliceMutUnchecked<'_, MaybeUninit<u8>> {
    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = unsafe { advance_slice_mut_unchecked(&mut self.buf, src.len()) };
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) };
        Ok(())
    }
}

impl Writer for &mut [MaybeUninit<u8>] {
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        let size = hint.size();
        let Some(window) = advance_slice_mut_checked(self, size) else {
            return Err(write_size_limit(size));
        };
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let Some(dst) = advance_slice_mut_checked(self, src.len()) else {
            return Err(write_size_limit(src.len()));
        };
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) };
        Ok(())
    }
}

impl Writer for &mut [u8] {
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        let size = hint.size();
        let Some(window) = advance_slice_mut_checked(self, size) else {
            return Err(write_size_limit(size));
        };
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let Some(dst) = advance_slice_mut_checked(self, src.len()) else {
            return Err(write_size_limit(src.len()));
        };
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) };
        Ok(())
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, alloc::vec::Vec, proptest::prelude::*};

    /// Execute the given block with supported readers.
    macro_rules! with_readers {
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

    /// Execute the given block with readers that will bounds check (and thus not panic).
    macro_rules! with_untrusted_readers {
        ($bytes:expr, |$reader:ident| $body:block) => {{
            {
                let mut $reader = $bytes.as_slice();
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
                unsafe { reader.read_hint(bytes.len() - half) }
                    .unwrap()
                    .copy_into_slice(&mut dst[half..])
                    .unwrap();
                unsafe { vec.set_len(bytes.len()) };
                prop_assert_eq!(&vec, &bytes);
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
