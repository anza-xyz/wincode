//! [`Reader`] and [`Writer`] implementations.
use {
    core::{mem::MaybeUninit, ptr, slice},
    thiserror::Error,
};

/// In-memory reader that allows direct reads from the source buffer
/// into user given destination buffers.
pub struct Reader<'a> {
    cursor: &'a [u8],
}

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

impl<'a> Reader<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { cursor: bytes }
    }

    #[inline]
    pub fn peek(&self) -> ReadResult<&u8> {
        self.cursor.first().ok_or_else(|| read_size_limit(0))
    }

    /// Copy exactly `dst.len()` bytes from the [`Reader`] into `dst`.
    #[inline]
    pub fn read_exact(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let Some((src, rest)) = self.cursor.split_at_checked(dst.len()) else {
            return Err(read_size_limit(dst.len()));
        };
        unsafe {
            // SAFETY:
            // - `dst` must not overlap with the cursor (shouldn't be the case unless the user is doing something they shouldn't).
            // - We just checked that we have enough bytes remaining in the cursor.
            ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), dst.len());
        }
        self.cursor = rest;
        Ok(())
    }

    /// Copy exactly `size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    #[inline]
    pub unsafe fn read_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        self.read_slice_t(slice::from_mut(dst))
    }

    /// Copy exactly `dst.len() * size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    #[inline]
    pub unsafe fn read_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        let slice = unsafe {
            slice::from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), size_of_val(dst))
        };
        self.read_exact(slice)?;
        Ok(())
    }

    /// Read exactly `len` bytes from the cursor into a slice.
    #[inline]
    pub fn read_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let Some((src, rest)) = self.cursor.split_at_checked(len) else {
            return Err(read_size_limit(len));
        };
        self.cursor = rest;
        Ok(src)
    }

    /// Read T from the cursor into a new T.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    #[inline(always)]
    pub unsafe fn get_t<T>(&mut self) -> ReadResult<T> {
        let mut val = MaybeUninit::<T>::uninit();
        self.read_t(&mut val)?;
        Ok(val.assume_init())
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        self.cursor
    }

    /// Advance the cursor by `amt` bytes without checking bounds.
    #[inline(always)]
    pub fn consume_unchecked(&mut self, amt: usize) {
        self.cursor = &self.cursor[amt..];
    }

    /// Advance `amt` bytes from the reader and discard them.
    #[inline]
    pub fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if self.cursor.len() < amt {
            return Err(read_size_limit(amt));
        };
        self.consume_unchecked(amt);
        Ok(())
    }
}

/// In-memory writer that allows direct writes from user given buffers
/// into the internal destination buffer.
pub struct Writer<'a> {
    buffer: &'a mut [MaybeUninit<u8>],
    pos: usize,
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

impl<'a> Writer<'a> {
    pub fn new(buffer: &'a mut [MaybeUninit<u8>]) -> Self {
        Self { buffer, pos: 0 }
    }

    /// Get the number of bytes written to the buffer.
    #[inline]
    pub fn finish(self) -> usize {
        self.pos
    }

    /// Get the number of bytes written to the buffer, and error if there are trailing bytes.
    pub fn finish_disallow_trailing_bytes(self) -> WriteResult<usize> {
        if self.pos != self.buffer.len() {
            return Err(writer_trailing_bytes(
                self.buffer.len().saturating_sub(self.pos),
            ));
        }
        Ok(self.pos)
    }

    /// Write exactly `src.len()` bytes from the given `src` into the internal buffer.
    #[inline]
    pub fn write_exact(&mut self, src: &[u8]) -> WriteResult<()> {
        if self.buffer.len().saturating_sub(self.pos) < src.len() {
            return Err(write_size_limit(src.len()));
        }

        unsafe {
            // SAFETY:
            // - `src` mustn't overlap with the internal buffer (shouldn't be the case unless the user is doing something they shouldn't).
            // - We just checked that we have enough capacity in the internal buffer.
            ptr::copy_nonoverlapping(
                src.as_ptr(),
                self.buffer.as_mut_ptr().add(self.pos).cast(),
                src.len(),
            );
        }
        self.pos += src.len();
        Ok(())
    }

    /// Write `len` bytes from the given `write` function into the internal buffer.
    ///
    /// This method can be used to get `len` [`MaybeUninit<u8>`] bytes from internal
    /// buffer for direct writes.
    ///
    /// # Safety
    ///
    /// - `write` must write EXACTLY `len` bytes into the given buffer.
    pub unsafe fn write_with<F>(&mut self, len: usize, write: F) -> WriteResult<()>
    where
        F: FnOnce(&mut [MaybeUninit<u8>]) -> WriteResult<()>,
    {
        let upper_bound = self
            .pos
            .checked_add(len)
            .ok_or_else(|| write_size_limit(len))?;
        let dst = self
            .buffer
            .get_mut(self.pos..upper_bound)
            .ok_or_else(|| write_size_limit(len))?;
        write(dst)?;
        self.pos = upper_bound;
        Ok(())
    }

    /// Write `T` as bytes into the internal buffer.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data.
    #[inline]
    pub unsafe fn write_t<T>(&mut self, value: &T) -> WriteResult<()> {
        self.write_slice_t(slice::from_ref(value))
    }

    /// Write `[T]` as bytes into the internal buffer.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data.
    #[inline]
    pub unsafe fn write_slice_t<T>(&mut self, value: &[T]) -> WriteResult<()> {
        unsafe {
            self.write_exact(slice::from_raw_parts(
                value.as_ptr().cast(),
                size_of_val(value),
            ))
        }
    }
}
