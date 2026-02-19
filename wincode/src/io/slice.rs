use {
    super::*,
    core::{
        marker::PhantomData,
        mem::{self, MaybeUninit},
        ptr::copy_nonoverlapping,
    },
};

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

impl<'a> Reader<'a> for &'a [u8] {
    #[inline(always)]
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>> {
        match Chunks::from_slice_checked(chunk_size, n_chunks, self) {
            Ok(chunks) => Ok(chunks.map(|buf| unsafe { SliceUnchecked::new(buf) })),
            Err(total) => Err(read_size_limit(total)),
        }
    }

    #[inline(always)]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        let Some(chunk) = advance_slice_checked(self, chunk_size) else {
            return Err(read_size_limit(chunk_size));
        };

        Ok(unsafe { SliceUnchecked::new(chunk) })
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let Some(chunk) = advance_slice_checked(self, buf.len()) else {
            return Err(read_size_limit(buf.len()));
        };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline(always)]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let Some((chunk, rest)) = self.split_first_chunk() else {
            return Err(read_size_limit(N));
        };
        *self = rest;
        Ok(*chunk)
    }

    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let Some(chunk) = advance_slice_checked(self, len) else {
            return Err(read_size_limit(len));
        };
        Ok(chunk)
    }
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
    #[inline(always)]
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>> {
        Ok(unsafe {
            Chunks::from_slice_unchecked(chunk_size, n_chunks, &mut self.buf)
                .map(|buf| SliceUnchecked::new(buf))
        })
    }

    #[inline(always)]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, chunk_size) };
        Ok(unsafe { SliceUnchecked::new(chunk) })
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, buf.len()) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, N) };
        Ok(unsafe { *(chunk.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, len) };
        Ok(chunk)
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
    #[inline(always)]
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>> {
        Ok(unsafe {
            Chunks::from_slice_unchecked(chunk_size, n_chunks, &mut self.inner.buf)
                .map(|buf| SliceScopedUnchecked::new(buf))
        })
    }

    #[inline(always)]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        let chunk = unsafe { advance_slice_unchecked(&mut self.inner.buf, chunk_size) };
        Ok(unsafe { SliceScopedUnchecked::new(chunk) })
    }

    #[inline(always)]
    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        self.inner.read_exact(buf)
    }

    #[inline(always)]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        self.inner.read_array()
    }
}

pub struct Chunks<'a, T> {
    chunk_size: usize,
    n_chunks: usize,
    i: usize,
    buf: &'a [T],
}

#[cold]
const fn cold<T>(t: T) -> T {
    t
}

impl<'a, T> Chunks<'a, T> {
    pub const unsafe fn new_unchecked(chunk_size: usize, n_chunks: usize, buf: &'a [T]) -> Self {
        Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf,
        }
    }

    pub fn new_checked(chunk_size: usize, n_chunks: usize, buf: &'a [T]) -> Result<Self, usize> {
        let Some(total) = chunk_size.checked_mul(n_chunks) else {
            return Err(cold(usize::MAX));
        };
        if buf.len() < total {
            return Err(cold(total));
        }
        Ok(Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf,
        })
    }

    #[inline(always)]
    pub fn from_slice_checked(
        chunk_size: usize,
        n_chunks: usize,
        buf: &mut &'a [T],
    ) -> Result<Self, usize> {
        let Some(total) = chunk_size.checked_mul(n_chunks) else {
            return Err(cold(usize::MAX));
        };
        let Some(window) = advance_slice_checked(buf, total) else {
            return Err(cold(total));
        };
        Ok(Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf: window,
        })
    }

    #[inline(always)]
    #[expect(clippy::arithmetic_side_effects)]
    pub unsafe fn from_slice_unchecked(
        chunk_size: usize,
        n_chunks: usize,
        buf: &mut &'a [T],
    ) -> Self {
        let total = chunk_size * n_chunks;
        let window = advance_slice_unchecked(buf, total);
        Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf: window,
        }
    }

    #[expect(clippy::arithmetic_side_effects)]
    #[inline]
    pub const fn len(&self) -> usize {
        self.n_chunks - self.i
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> Iterator for Chunks<'a, T> {
    type Item = &'a [T];

    #[expect(clippy::arithmetic_side_effects)]
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.i == self.n_chunks {
            return None;
        }
        self.i += 1;
        let chunk = unsafe { advance_slice_unchecked(&mut self.buf, self.chunk_size) };
        Some(chunk)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

pub struct ChunksMut<'a, T> {
    chunk_size: usize,
    n_chunks: usize,
    i: usize,
    buf: &'a mut [T],
}

impl<'a, T> ChunksMut<'a, T> {
    #[inline(always)]
    pub const unsafe fn new_unchecked(
        chunk_size: usize,
        n_chunks: usize,
        buf: &'a mut [T],
    ) -> Self {
        Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf,
        }
    }

    #[inline(always)]
    pub fn new_checked(
        chunk_size: usize,
        n_chunks: usize,
        buf: &'a mut [T],
    ) -> Result<Self, usize> {
        let Some(total) = chunk_size.checked_mul(n_chunks) else {
            return Err(cold(usize::MAX));
        };
        if buf.len() < total {
            return Err(cold(total));
        }
        Ok(Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf,
        })
    }

    #[inline(always)]
    pub fn from_slice_checked(
        chunk_size: usize,
        n_chunks: usize,
        buf: &mut &'a mut [T],
    ) -> Result<Self, usize> {
        let Some(total) = chunk_size.checked_mul(n_chunks) else {
            return Err(cold(usize::MAX));
        };
        let Some(window) = advance_slice_mut_checked(buf, total) else {
            return Err(cold(total));
        };
        Ok(Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf: window,
        })
    }

    #[inline(always)]
    #[expect(clippy::arithmetic_side_effects)]
    pub unsafe fn from_slice_unchecked(
        chunk_size: usize,
        n_chunks: usize,
        buf: &mut &'a mut [T],
    ) -> Self {
        let total = chunk_size * n_chunks;
        let window = advance_slice_mut_unchecked(buf, total);
        Self {
            chunk_size,
            n_chunks,
            i: 0,
            buf: window,
        }
    }

    #[expect(clippy::arithmetic_side_effects)]
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.n_chunks - self.i
    }
}

impl<'a, T> Iterator for ChunksMut<'a, T> {
    type Item = &'a mut [T];

    #[expect(clippy::arithmetic_side_effects)]
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.i == self.n_chunks {
            return None;
        }
        self.i += 1;
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, self.chunk_size) };
        Some(chunk)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

pub struct SliceMutUnchecked<'a, T> {
    buf: &'a mut [T],
}

impl<'a, T> SliceMutUnchecked<'a, T> {
    #[inline]
    pub const unsafe fn new(buf: &'a mut [T]) -> Self {
        Self { buf }
    }
}

impl<'a> Reader<'a> for SliceMutUnchecked<'a, u8> {
    #[inline(always)]
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>> {
        Ok(unsafe {
            ChunksMut::from_slice_unchecked(chunk_size, n_chunks, &mut self.buf)
                .map(|buf| SliceMutUnchecked::new(buf))
        })
    }

    #[inline(always)]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, chunk_size) };
        Ok(unsafe { SliceMutUnchecked::new(chunk) })
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, buf.len()) };
        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, N) };
        Ok(unsafe { *(chunk.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        Ok(unsafe { advance_slice_mut_unchecked(&mut self.buf, len) })
    }
}

impl<'a> Reader<'a> for &'a mut [u8] {
    #[inline(always)]
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>> {
        match ChunksMut::from_slice_checked(chunk_size, n_chunks, self) {
            Ok(chunks) => Ok(chunks.map(|buf| unsafe { SliceMutUnchecked::new(buf) })),
            Err(total) => Err(read_size_limit(total)),
        }
    }

    #[inline(always)]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        let Some(chunk) = advance_slice_mut_checked(self, chunk_size) else {
            return Err(read_size_limit(chunk_size));
        };

        Ok(unsafe { SliceMutUnchecked::new(chunk) })
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let Some(chunk) = advance_slice_mut_checked(self, buf.len()) else {
            return Err(read_size_limit(buf.len()));
        };

        unsafe { copy_nonoverlapping(chunk.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        Ok(())
    }

    #[inline(always)]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let Some((chunk, rest)) = mem::take(self).split_first_chunk_mut() else {
            return Err(read_size_limit(N));
        };
        *self = rest;
        Ok(*chunk)
    }

    #[inline]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        advance_slice_mut_checked(self, len).ok_or_else(|| read_size_limit(len))
    }
}

impl Writer for SliceMutUnchecked<'_, u8> {
    #[inline(always)]
    unsafe fn chunks_mut(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> WriteResult<impl Iterator<Item = impl Writer>> {
        Ok(unsafe {
            ChunksMut::from_slice_unchecked(chunk_size, n_chunks, &mut self.buf)
                .map(|buf| SliceMutUnchecked::new(buf))
        })
    }

    #[inline(always)]
    unsafe fn chunk_mut(&mut self, chunk_size: usize) -> WriteResult<impl Writer> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, chunk_size) };
        Ok(unsafe { SliceMutUnchecked::new(chunk) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = unsafe { advance_slice_mut_unchecked(&mut self.buf, src.len()) };
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), src.len()) };
        Ok(())
    }
}

impl Writer for SliceMutUnchecked<'_, MaybeUninit<u8>> {
    #[inline(always)]
    unsafe fn chunks_mut(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> WriteResult<impl Iterator<Item = impl Writer>> {
        Ok(unsafe {
            ChunksMut::from_slice_unchecked(chunk_size, n_chunks, &mut self.buf)
                .map(|buf| SliceMutUnchecked::new(buf))
        })
    }

    #[inline(always)]
    unsafe fn chunk_mut(&mut self, chunk_size: usize) -> WriteResult<impl Writer> {
        let chunk = unsafe { advance_slice_mut_unchecked(&mut self.buf, chunk_size) };
        Ok(unsafe { SliceMutUnchecked::new(chunk) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = unsafe { advance_slice_mut_unchecked(&mut self.buf, src.len()) };
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), src.len()) };
        Ok(())
    }
}

impl Writer for &mut [MaybeUninit<u8>] {
    #[inline(always)]
    unsafe fn chunks_mut(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> WriteResult<impl Iterator<Item = impl Writer>> {
        match ChunksMut::from_slice_checked(chunk_size, n_chunks, self) {
            Ok(chunks) => Ok(chunks.map(|buf| unsafe { SliceMutUnchecked::new(buf) })),
            Err(total) => Err(write_size_limit(total)),
        }
    }

    #[inline(always)]
    unsafe fn chunk_mut(&mut self, chunk_size: usize) -> WriteResult<impl Writer> {
        let Some(chunk) = advance_slice_mut_checked(self, chunk_size) else {
            return Err(write_size_limit(chunk_size));
        };
        Ok(unsafe { SliceMutUnchecked::new(chunk) })
    }

    #[inline]
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
    unsafe fn chunks_mut(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> WriteResult<impl Iterator<Item = impl Writer>> {
        match ChunksMut::from_slice_checked(chunk_size, n_chunks, self) {
            Ok(chunks) => Ok(chunks.map(|buf| unsafe { SliceMutUnchecked::new(buf) })),
            Err(total) => Err(write_size_limit(total)),
        }
    }

    #[inline(always)]
    unsafe fn chunk_mut(&mut self, chunk_size: usize) -> WriteResult<impl Writer> {
        let Some(chunk) = advance_slice_mut_checked(self, chunk_size) else {
            return Err(write_size_limit(chunk_size));
        };
        Ok(unsafe { SliceMutUnchecked::new(chunk) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let Some(dst) = advance_slice_mut_checked(self, src.len()) else {
            return Err(write_size_limit(src.len()));
        };
        // Avoid the bounds check of `copy_from_slice` by using `copy_nonoverlapping`,
        // since we already bounds check in `get_slice_mut`.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len()) };
        Ok(())
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {
        super::{Cursor, ReadError, Reader, WriteError, Writer},
        crate::proptest_config::proptest_cfg,
        alloc::vec::Vec,
        core::mem::MaybeUninit,
        proptest::prelude::*,
    };

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
                reader.read_exact(&mut dst[..half]).unwrap();
                unsafe { reader.chunk(bytes.len() - half) }
                    .unwrap()
                    .read_exact(&mut dst[half..])
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
                prop_assert!(matches!(reader.read_exact(dst), Err(ReadError::ReadSizeLimit(x)) if x == bytes.len() + 1));
            });
        }


        #[test]
        fn test_reader_copy_into_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_readers!(&bytes, |reader| {
                for int in &ints {
                    let mut val = MaybeUninit::<u64>::uninit();
                    unsafe { reader.read_t(&mut val).unwrap() };
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
                unsafe { reader.read_slice_t(dst).unwrap() };
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
