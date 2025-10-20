//! [`Reader`] and [`Writer`] implementations.
use {
    core::{mem::MaybeUninit, ptr},
    thiserror::Error,
};

#[derive(Error, Debug, PartialEq, Eq, Clone, Copy)]
pub enum ReadError {
    #[error("Attempting to read {0} bytes")]
    ReadSizeLimit(usize),
}

pub type ReadResult<T> = core::result::Result<T, ReadError>;

#[cold]
fn read_size_limit(len: usize) -> ReadError {
    ReadError::ReadSizeLimit(len)
}

/// Trait for structured reading of bytes from a source into potentially uninitialized memory.
pub trait Reader<'a> {
    /// A variant of the reader that can elide bounds checking.
    ///
    /// Useful for sections of code where there is enough information to bulk prefetch bytes
    /// with a single bounds check for the entire chunk.
    type Trusted: Reader<'a>;
    /// Peek up to `n_bytes` bytes without consuming them.
    ///
    /// This is _not_ required to return exactly `n_bytes`, it is required
    /// to return _up to_ `n_bytes`, so take care to check the length
    /// if you need to ensure you get exactly `n_bytes`.
    fn peek_buffered(&self, n_bytes: usize) -> &'a [u8];
    /// Consume and return a slice of `len` bytes, returning an error if the
    /// reader does not have enough bytes.
    fn read_slice(&mut self, len: usize) -> ReadResult<&'a [u8]>;
    /// Consume and return a reference to an array of `N` bytes, returning an error if the
    /// reader does not have enough bytes.
    #[inline]
    fn read_array<const N: usize>(&mut self) -> ReadResult<&'a [u8; N]> {
        let src = self.read_slice(N)?;
        // SAFETY:
        // - `read_slice` ensures we read N bytes.
        Ok(unsafe { &*src.as_ptr().cast::<[u8; N]>() })
    }
    /// Consume exactly `amt` bytes without checking bounds.
    ///
    /// May panic if the reader does not have enough bytes.
    fn consume_unchecked(&mut self, amt: usize);
    /// Consume exactly `amt` bytes, returning an error if the reader does not have enough bytes.
    fn consume(&mut self, amt: usize) -> ReadResult<()>;
    /// Bulk read `n_bytes` with a single bounds check, returning a [`Reader`]
    /// that can elide bounds checking for the entire chunk.
    ///
    /// Should return an error if the reader does not have enough space.
    fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted>;

    /// Peek the next byte without consuming it.
    #[inline]
    fn peek(&self) -> ReadResult<&'a u8> {
        self.peek_buffered(1)
            .first()
            .ok_or_else(|| read_size_limit(1))
    }

    /// Copy exactly `dst.len()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    fn read_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = self.read_slice(dst.len())?;
        // SAFETY:
        // - `read_slice` must do the appropriate bounds checking.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), dst.len()) };
        Ok(())
    }

    /// Copy exactly `N` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    fn read_into_array<const N: usize>(
        &mut self,
        dst: &mut MaybeUninit<[u8; N]>,
    ) -> ReadResult<()> {
        let src = self.read_array::<N>()?;
        // SAFETY:
        // - `read_array` must do the appropriate bounds checking.
        unsafe { ptr::copy_nonoverlapping(src, dst.as_mut_ptr(), 1) };
        Ok(())
    }

    /// Copy exactly `size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    unsafe fn read_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        let src = self.read_slice(size_of::<T>())?;
        // SAFETY:
        // - `read_slice` must do the appropriate bounds checking.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), size_of::<T>()) };
        Ok(())
    }

    /// Copy exactly `dst.len() * size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    unsafe fn read_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        let bytes = self.read_slice(size_of_val(dst))?;
        // SAFETY:
        // - `read_slice` must do the appropriate bounds checking.
        unsafe {
            ptr::copy_nonoverlapping(bytes.as_ptr(), dst.as_mut_ptr().cast(), size_of_val(dst))
        };
        Ok(())
    }
}

/// In-memory [`Reader`] that does not perform bounds checking.
///
/// Methods will panic if reads go out of bounds, so ensure that
/// the chain of [`SchemaRead`](crate::SchemaRead) implementations that
/// follow have statically known read requirements.
pub struct TrustedSliceReader<'a> {
    cursor: &'a [u8],
}

impl<'a> TrustedSliceReader<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { cursor: bytes }
    }
}

impl<'a> Reader<'a> for TrustedSliceReader<'a> {
    type Trusted = Self;

    #[inline]
    fn peek_buffered(&self, n_bytes: usize) -> &'a [u8] {
        &self.cursor[..n_bytes.min(self.cursor.len())]
    }

    #[inline]
    fn read_slice(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let (src, rest) = self.cursor.split_at(len);
        self.cursor = rest;
        Ok(src)
    }

    #[inline]
    fn consume_unchecked(&mut self, amt: usize) {
        self.cursor = &self.cursor[amt..];
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        self.cursor = &self.cursor[amt..];
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted> {
        Ok(TrustedSliceReader::new(self.read_slice(n_bytes)?))
    }
}

/// In-memory, bounds-checked [`Reader`].
pub struct SliceReader<'a> {
    cursor: &'a [u8],
}

impl<'a> SliceReader<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { cursor: bytes }
    }
}

impl<'a> Reader<'a> for SliceReader<'a> {
    type Trusted = TrustedSliceReader<'a>;

    #[inline]
    fn peek_buffered(&self, n_bytes: usize) -> &'a [u8] {
        &self.cursor[..n_bytes.min(self.cursor.len())]
    }

    #[inline]
    fn read_slice(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let Some((src, rest)) = self.cursor.split_at_checked(len) else {
            return Err(read_size_limit(len));
        };
        self.cursor = rest;
        Ok(src)
    }

    #[inline]
    fn consume_unchecked(&mut self, amt: usize) {
        self.cursor = &self.cursor[amt..];
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if self.cursor.len() < amt {
            return Err(read_size_limit(amt));
        };
        self.consume_unchecked(amt);
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n: usize) -> ReadResult<Self::Trusted> {
        Ok(TrustedSliceReader::new(self.read_slice(n)?))
    }
}

#[derive(Error, Debug, PartialEq, Eq, Clone, Copy)]
pub enum WriteError {
    #[error("Attempting to write {0} bytes")]
    WriteSizeLimit(usize),
    #[error("Writer has trailing bytes: {0}")]
    WriterTrailingBytes(usize),
}

#[cold]
fn write_size_limit(len: usize) -> WriteError {
    WriteError::WriteSizeLimit(len)
}

#[cold]
fn writer_trailing_bytes(bytes: usize) -> WriteError {
    WriteError::WriterTrailingBytes(bytes)
}

pub type WriteResult<T> = core::result::Result<T, WriteError>;

/// Trait for structured writing of bytes into a source of potentially uninitialized memory.
pub trait Writer {
    /// A variant of the [`Writer`] that can elide bounds checking.
    ///
    /// Useful for sections of code where there is enough information to bulk prefetch memory
    /// with a single bounds check for the entire chunk.
    type Trusted<'a>: Writer
    where
        Self: 'a;

    /// Get the number of bytes written to the destination.
    fn finish(self) -> usize;
    /// Get the number of bytes written to the buffer, and error if there are trailing bytes.
    fn finish_disallow_trailing_bytes(self) -> WriteResult<usize>;
    /// Consume and return a slice of `len` bytes for writing, returning an error if the
    /// writer does not have enough space.
    ///
    /// It is the caller's responsibility to fully initialize the returned slice.
    fn get_slice_mut(&mut self, len: usize) -> WriteResult<&mut [MaybeUninit<u8>]>;
    /// Consume and return a reference to an array of `N` bytes for writing, returning an error if the
    /// writer does not have enough space.
    ///
    /// It is the caller's responsibility to fully initialize the returned array.
    #[inline]
    fn get_array_mut<const N: usize>(&mut self) -> WriteResult<&mut MaybeUninit<[u8; N]>> {
        let dst = self.get_slice_mut(N)?;
        // SAFETY:
        // - get_slice_mut ensures that the returned slice has at least N bytes
        Ok(unsafe { &mut *dst.as_mut_ptr().cast::<MaybeUninit<[u8; N]>>() })
    }
    /// Bulk fetch `n_bytes` of potentially uninitialized memory with a single bounds check,
    /// returning a [`Writer`] over that memory that can elide bounds checking when writing.
    ///
    /// Should return an error if the writer does not have enough space.
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>>;

    /// Copy exactly `src.len()` bytes from the given `src` into the internal buffer.
    ///
    /// # Safety
    ///
    /// - `src` must not overlap with the internal buffer.
    #[inline]
    fn write_from_slice(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.get_slice_mut(src.len())?;
        // SAFETY:
        // - `get_slice_mut` must do the appropriate bounds checking.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), src.len()) };
        Ok(())
    }

    /// Copy exactly `N` bytes from the given `src` into the internal buffer.
    ///
    /// # Safety
    ///
    /// - `src` must not overlap with the internal buffer.
    #[inline]
    fn write_from_array<const N: usize>(&mut self, src: &[u8; N]) -> WriteResult<()> {
        let dst = self.get_array_mut::<N>()?;
        // SAFETY:
        // - `get_array_mut` must do the appropriate bounds checking.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), 1) };
        Ok(())
    }

    /// Write `T` as bytes into the internal buffer.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data.
    /// - `src` must not overlap with the internal buffer.
    #[inline]
    unsafe fn write_from_t<T>(&mut self, src: &T) -> WriteResult<()> {
        let dst = self.get_slice_mut(size_of::<T>())?;
        unsafe {
            ptr::copy_nonoverlapping((src as *const T).cast(), dst.as_mut_ptr(), size_of::<T>())
        };
        Ok(())
    }

    /// Write `[T]` as bytes into the internal buffer.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data.
    /// - `src` must not overlap with the internal buffer.
    #[inline]
    unsafe fn write_from_slice_t<T>(&mut self, src: &[T]) -> WriteResult<()> {
        let dst = self.get_slice_mut(size_of_val(src))?;
        // SAFETY:
        // - `get_slice_mut` must do the appropriate bounds checking.
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), size_of_val(src))
        };
        Ok(())
    }
}

/// In-memory [`Writer`] that does not perform bounds checking.
///
/// Methods will panic if writes go out of bounds, so ensure that
/// the chain of [`SchemaWrite`](crate::SchemaWrite) implementations that
/// follow have statically known size requirements.
pub struct TrustedSliceWriter<'a> {
    buffer: &'a mut [MaybeUninit<u8>],
    pos: usize,
    /// The original length of the source that created the trusted writer.
    ///
    /// This can be used to check for trailing bytes when the writer is finished.
    source_len: usize,
    /// The global position of the writer relative to the original source.
    global_pos: usize,
}

impl<'a> TrustedSliceWriter<'a> {
    /// Create a new [`TrustedSliceWriter`] from a fresh buffer.
    ///
    /// Prefer [`TrustedSliceWriter::from_source`] if you're starting from an untrusted buffer.
    pub fn new(buffer: &'a mut [MaybeUninit<u8>]) -> Self {
        Self::from_source(buffer, buffer.len(), 0)
    }

    /// Create a new [`TrustedSliceWriter`] from an untrusted buffer, providing
    /// the length of the original source.
    ///
    /// Prefer [`TrustedSliceWriter::new`] if you're starting from a fresh buffer.
    pub fn from_source(
        buffer: &'a mut [MaybeUninit<u8>],
        source_len: usize,
        global_pos: usize,
    ) -> Self {
        Self {
            buffer,
            pos: 0,
            source_len,
            global_pos,
        }
    }
}

impl<'a> Writer for TrustedSliceWriter<'a> {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn finish(self) -> usize {
        self.global_pos + self.pos
    }

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn finish_disallow_trailing_bytes(self) -> WriteResult<usize> {
        let final_pos = self.global_pos + self.pos;
        // Pos should never write beyond the source length.
        let rem = self.source_len - final_pos;
        if rem != 0 {
            return Err(writer_trailing_bytes(rem));
        }

        Ok(final_pos)
    }

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn get_slice_mut(&mut self, len: usize) -> WriteResult<&mut [MaybeUninit<u8>]> {
        let dst = &mut self.buffer[self.pos..self.pos + len];
        self.pos += len;
        Ok(dst)
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<TrustedSliceWriter<'_>> {
        let source_len = self.source_len;
        // Position can never exceed the source length, and as such will never overflow usize::MAX.
        #[allow(clippy::arithmetic_side_effects)]
        let global_pos = self.global_pos + self.pos;
        Ok(TrustedSliceWriter::from_source(
            self.get_slice_mut(n_bytes)?,
            source_len,
            global_pos,
        ))
    }
}

/// In-memory, bounds-checked [`Writer`].
pub struct SliceWriter<'a> {
    buffer: &'a mut [MaybeUninit<u8>],
    pos: usize,
}

impl<'a> SliceWriter<'a> {
    pub fn new(buffer: &'a mut [MaybeUninit<u8>]) -> Self {
        Self { buffer, pos: 0 }
    }
}

impl<'a> Writer for SliceWriter<'a> {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn finish(self) -> usize {
        self.pos
    }

    fn finish_disallow_trailing_bytes(self) -> WriteResult<usize> {
        if self.pos != self.buffer.len() {
            return Err(writer_trailing_bytes(
                self.buffer.len().saturating_sub(self.pos),
            ));
        }
        Ok(self.pos)
    }

    #[inline]
    fn get_slice_mut(&mut self, len: usize) -> WriteResult<&mut [MaybeUninit<u8>]> {
        let dst = &mut self.buffer[self.pos..];
        if dst.len() < len {
            return Err(write_size_limit(len));
        }

        let dst = &mut dst[..len];

        #[allow(clippy::arithmetic_side_effects)]
        {
            self.pos += len;
        }
        Ok(dst)
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<TrustedSliceWriter<'_>> {
        let source_len = self.buffer.len();
        let global_pos = self.pos;
        Ok(TrustedSliceWriter::from_source(
            self.get_slice_mut(n_bytes)?,
            source_len,
            global_pos,
        ))
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};

    #[test]
    fn test_reader_peek() {
        let reader = SliceReader::new(b"hello");
        assert_eq!(reader.peek(), Ok(&b'h'));
    }

    #[test]
    fn test_reader_peek_empty() {
        let reader = SliceReader::new(b"");
        assert_eq!(reader.peek(), Err(ReadError::ReadSizeLimit(1)));
    }

    /// Execute the given block with both [`SliceReader`] and [`TrustedSliceReader`] for the given bytes.
    macro_rules! with_both_readers {
        ($bytes:expr, |$reader:ident| $body:block) => {{
            {
                let mut $reader = SliceReader::new($bytes);
                $body
            }
            {
                let mut $reader = TrustedSliceReader::new($bytes);
                $body
            }
        }};
    }

    /// Execute the given block with both [`SliceReader`] and [`TrustedSliceReader`] for the given bytes.
    #[allow(unused_macros)]
    macro_rules! with_both_writers {
        ($buffer:expr, |$writer:ident| $body:block) => {{
            {
                let mut $writer = SliceWriter::new($buffer.spare_capacity_mut());
                $body
                $buffer.clear();
            }
            {
                let mut $writer = TrustedSliceWriter::new($buffer.spare_capacity_mut());
                $body
            }
        }};
    }

    #[test]
    #[should_panic]
    fn trusted_reader_read_slice_input_too_large() {
        let bytes = [1, 2, 3, 4, 5];
        let mut reader = TrustedSliceReader::new(&bytes);
        let _ = reader.read_slice(bytes.len() + 1);
    }

    #[test]
    #[should_panic]
    fn trusted_reader_read_into_slice_input_too_large() {
        let bytes = [1, 2, 3, 4, 5];
        let mut reader = TrustedSliceReader::new(&bytes);
        let mut dst = [MaybeUninit::<u8>::uninit(); 6];
        let _ = reader.read_into_slice(&mut dst);
    }

    #[test]
    #[should_panic]
    fn trusted_reader_consume_input_too_large() {
        let bytes = [1, 2, 3, 4, 5];
        let mut reader = TrustedSliceReader::new(&bytes);
        let _ = reader.consume(bytes.len() + 1);
    }

    #[test]
    #[should_panic]
    fn trusted_writer_write_from_slice_input_too_large() {
        let bytes = [1, 2, 3, 4, 5];
        let mut buffer = [MaybeUninit::<u8>::uninit(); 4];
        let mut writer = TrustedSliceWriter::new(&mut buffer);
        let _ = writer.write_from_slice(&bytes);
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_reader_read_into_slice(bytes in any::<Vec<u8>>()) {
            with_both_readers!(&bytes, |reader| {
                let mut vec = Vec::with_capacity(bytes.len());
                let dst = vec.spare_capacity_mut();
                reader.read_into_slice(dst).unwrap();
                unsafe { vec.set_len(bytes.len()) };
                prop_assert_eq!(&vec, &bytes);
            });
        }

        #[test]
        fn test_reader_read_slice(bytes in any::<Vec<u8>>()) {
            with_both_readers!(&bytes, |reader| {
                let read = reader.read_slice(bytes.len()).unwrap();
                prop_assert_eq!(&read, &bytes);
            });
        }

        #[test]
        fn slice_reader_read_slice_input_too_large(bytes in any::<Vec<u8>>()) {
            let mut reader = SliceReader::new(&bytes);
            assert_eq!(reader.read_slice(bytes.len() + 1), Err(ReadError::ReadSizeLimit(bytes.len() + 1)));
        }


        #[test]
        fn test_reader_read_into_slice_input_too_large(bytes in any::<Vec<u8>>()) {
            let mut reader = SliceReader::new(&bytes);
            let mut vec = Vec::with_capacity(bytes.len() + 1);
            let dst = vec.spare_capacity_mut();
            prop_assert_eq!(reader.read_into_slice(dst), Err(ReadError::ReadSizeLimit(bytes.len() + 1)));
        }

        #[test]
        fn test_reader_consume(bytes in any::<Vec<u8>>()) {
            with_both_readers!(&bytes, |reader| {
                reader.consume(bytes.len()).unwrap();
                prop_assert_eq!(reader.peek_buffered(1), &[]);
            });
        }

        #[test]
        fn test_reader_consume_input_too_large(bytes in any::<Vec<u8>>()) {
            let mut reader = SliceReader::new(&bytes);
            prop_assert_eq!(reader.consume(bytes.len() + 1), Err(ReadError::ReadSizeLimit(bytes.len() + 1)));
        }

        #[test]
        fn test_read_into_t(ints in proptest::collection::vec(any::<u64>(), 1..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_both_readers!(&bytes, |reader| {
                for int in &ints {
                    let mut val = MaybeUninit::<u64>::uninit();
                    unsafe { reader.read_into_t(&mut val).unwrap() };
                    unsafe { prop_assert_eq!(val.assume_init(), *int) };
                }
            });
        }

        #[test]
        fn test_read_into_slice_t(ints in proptest::collection::vec(any::<u64>(), 1..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_both_readers!(&bytes, |reader| {
                let mut vals: Vec<u64> = Vec::with_capacity(ints.len());
                let dst = vals.spare_capacity_mut();
                unsafe { reader.read_into_slice_t(dst).unwrap() };
                unsafe { vals.set_len(ints.len()) };
                prop_assert_eq!(&vals, &ints);
            });
        }

        #[test]
        fn test_writer_write_from_slice(bytes in any::<Vec<u8>>()) {
            let mut buffer = Vec::with_capacity(bytes.len());
            with_both_writers!(&mut buffer, |writer| {
                writer.write_from_slice(&bytes).unwrap();
                let written = writer.finish_disallow_trailing_bytes().unwrap();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &bytes);
            });
        }

        #[test]
        fn test_writer_write_from_slice_input_too_large(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len() - 1);
            let mut writer = SliceWriter::new(buffer.spare_capacity_mut());
            assert_eq!(writer.write_from_slice(&bytes), Err(WriteError::WriteSizeLimit(bytes.len())));
        }

        #[test]
        fn test_writer_finish_returns_written_bytes(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len());
            with_both_writers!(&mut buffer, |writer| {
                writer.write_from_slice(&bytes).unwrap();
                prop_assert_eq!(writer.finish(), bytes.len());
            });
        }

        #[test]
        fn test_writer_finish_disallow_trailing_bytes_error(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len());
            with_both_writers!(&mut buffer, |writer| {
                writer.write_from_slice(&bytes[..bytes.len() - 1]).unwrap();
                prop_assert_eq!(writer.finish_disallow_trailing_bytes(), Err(WriteError::WriterTrailingBytes(1)));
            });
        }

        #[test]
        fn test_writer_finish_disallow_trailing_bytes_success(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len());
            with_both_writers!(&mut buffer, |writer| {
                writer.write_from_slice(&bytes).unwrap();
                prop_assert_eq!(writer.finish_disallow_trailing_bytes(), Ok(bytes.len()));
            });
        }

        #[test]
        fn test_writer_write_from_t(int in any::<u64>()) {
            let mut buffer = Vec::with_capacity(8);
            with_both_writers!(&mut buffer, |writer| {
                unsafe { writer.write_from_t(&int).unwrap() };
                let written = writer.finish_disallow_trailing_bytes().unwrap();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &int.to_le_bytes());
            });
        }

        #[test]
        fn test_writer_write_slice_t(ints in proptest::collection::vec(any::<u64>(), 1..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            let mut buffer = Vec::with_capacity(bytes.len());
            with_both_writers!(&mut buffer, |writer| {
                unsafe { writer.write_from_slice_t(&ints).unwrap() };
                let written = writer.finish_disallow_trailing_bytes().unwrap();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &bytes);
            });
        }

        #[test]
        fn writer_to_trusted_trailing_bytes(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len());
            let mut writer = SliceWriter::new(buffer.spare_capacity_mut());
            let mut trusted_writer = writer.as_trusted_for(bytes.len() - 1).unwrap();
            trusted_writer.write_from_slice(&bytes[..bytes.len() - 1]).unwrap();
            prop_assert_eq!(
                trusted_writer.finish_disallow_trailing_bytes(),
                Err(WriteError::WriterTrailingBytes(1))
            );
        }

        #[test]
        fn writer_to_trusted_chain_trailing_bytes(
            (to_write, bytes) in
                proptest::collection::vec(any::<u8>(), 8..=100)
                    .prop_flat_map(|bytes| (0..(bytes.len() - 1) / 2, Just(bytes))),
        ) {
            let mut buffer = Vec::with_capacity(bytes.len());
            let mut writer = SliceWriter::new(buffer.spare_capacity_mut());
            let mut t1 = writer.as_trusted_for(to_write * 2).unwrap();
            t1.write_from_slice(&bytes[..to_write]).unwrap();
            let mut t2 = t1.as_trusted_for(to_write).unwrap();
            t2.write_from_slice(&bytes[to_write..to_write * 2]).unwrap();
            prop_assert_eq!(
                t2.finish_disallow_trailing_bytes(),
                Err(WriteError::WriterTrailingBytes(bytes.len() - to_write * 2))
            );
        }

        #[test]
        fn trusted_writer_doesnt_move_cursor(
            (to_write, bytes) in
                proptest::collection::vec(any::<u8>(), 8..=100)
                    .prop_flat_map(|bytes| (0..bytes.len(), Just(bytes))),
        ) {
            let mut buffer = Vec::with_capacity(bytes.len());
            let mut writer = SliceWriter::new(buffer.spare_capacity_mut());
            let t1 = writer.as_trusted_for(to_write).unwrap();

            prop_assert_eq!(
                t1.finish_disallow_trailing_bytes(),
                Err(WriteError::WriterTrailingBytes(bytes.len()))
            );
        }

        #[test]
        fn writer_to_trusted_chain_finish_returns_written_bytes(
            (to_write, bytes) in
                proptest::collection::vec(any::<u8>(), 8..=100)
                    .prop_flat_map(|bytes| (0..bytes.len() / 2, Just(bytes))),
        ) {
            let mut buffer = Vec::with_capacity(bytes.len());
            let mut writer = SliceWriter::new(buffer.spare_capacity_mut());
            let mut t1 = writer.as_trusted_for(to_write * 2).unwrap();
            t1.write_from_slice(&bytes[..to_write]).unwrap();
            let mut t2 = t1.as_trusted_for(to_write).unwrap();
            t2.write_from_slice(&bytes[to_write..to_write * 2]).unwrap();
            prop_assert_eq!(t2.finish(), to_write * 2);
        }
    }
}
