//! [`Reader`] and [`Writer`] implementations.
use {
    core::{
        mem::{transmute, MaybeUninit},
        ptr,
        slice::{from_raw_parts, from_raw_parts_mut},
    },
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum ReadError {
    #[error("Attempting to read {0} bytes")]
    ReadSizeLimit(usize),
    #[error(
        "Unsupported zero-copy operation: reader does not support deserializing zero-copy types"
    )]
    UnsupportedZeroCopy,
    #[cfg(feature = "std")]
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

pub type ReadResult<T> = core::result::Result<T, ReadError>;

#[cold]
pub const fn read_size_limit(len: usize) -> ReadError {
    ReadError::ReadSizeLimit(len)
}

#[inline(always)]
const fn transpose<const N: usize, T>(src: &mut MaybeUninit<[T; N]>) -> &mut [MaybeUninit<T>; N] {
    unsafe { transmute(src) }
}

/// Trait for structured reading of bytes from a source into potentially uninitialized memory.
///
/// # Zero-copy semantics
/// Only implement [`Reader::borrow_exact`] for sources where stable borrows into the backing storage are possible.
/// Callers should prefer [`Reader::fill_exact`] to remain compatible with readers that don’t support zero-copy.
/// Returns [`ReadError::UnsupportedZeroCopy`] for readers that do not support zero-copy.
pub trait Reader<'a> {
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>>;

    #[inline]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        let mut chunks = unsafe { self.chunks(chunk_size, 1) }?;
        let Some(chunk) = chunks.next() else {
            return Err(read_size_limit(chunk_size));
        };
        Ok(chunk)
    }

    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()>;

    #[inline(always)]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let mut ar = MaybeUninit::<[u8; N]>::uninit();

        self.read_exact(transpose(&mut ar))?;
        Ok(unsafe { ar.assume_init() })
    }

    #[inline(always)]
    fn read_byte(&mut self) -> ReadResult<u8> {
        Ok(self.read_array::<1>()?[0])
    }

    #[inline]
    unsafe fn read_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        let len = size_of_val(dst);
        let dst = unsafe { from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), len) };
        self.read_exact(dst)
    }

    #[inline]
    unsafe fn read_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        let dst = unsafe {
            from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), size_of::<T>())
        };
        self.read_exact(dst)
    }

    /// Zero-copy: return a borrowed slice of exactly `len` bytes and advance by `len`.
    ///
    /// The returned slice is tied to `'a`. Prefer [`Reader::fill_exact`] unless you truly need zero-copy.
    /// Errors for readers that don't support zero-copy.
    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        Self::borrow_exact_mut(self, len).map(|s| &*s)
    }

    /// Zero-copy: return a borrowed mutable slice of exactly `len` bytes and advance by `len`.
    ///
    /// Errors for readers that don't support zero-copy.
    #[expect(unused_variables)]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        Err(ReadError::UnsupportedZeroCopy)
    }

    /// Get a mutable reference to the [`Reader`].
    ///
    /// Useful in situations where one only has an `impl Reader<'de>` that
    /// needs to be passed to mulitple functions requiring `impl Reader<'de>`.
    ///
    /// Always prefer this over `&mut reader` to avoid recursive borrows.
    ///
    /// ```
    /// # use wincode::{io::Reader, ReadResult, config::Config, SchemaRead};
    /// # use core::mem::MaybeUninit;
    /// struct FooBar {
    ///     foo: u32,
    ///     bar: u32,
    /// }
    ///
    /// unsafe impl<'de, C: Config> SchemaRead<'de, C> for FooBar {
    ///     type Dst = Self;
    ///
    ///     fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self>) -> ReadResult<()> {
    ///         // `reader.by_ref()`; Good ✅
    ///         let foo = <u32 as SchemaRead<'de, C>>::get(reader.by_ref())?;
    ///         let bar = <u32 as SchemaRead<'de, C>>::get(reader)?;
    ///         dst.write(FooBar { foo, bar });
    ///         Ok(())
    ///     }
    /// }
    /// ```
    #[inline(always)]
    fn by_ref(&mut self) -> impl Reader<'a> {
        self
    }
}

impl<'a, R: Reader<'a> + ?Sized> Reader<'a> for &mut R {
    #[inline(always)]
    fn by_ref(&mut self) -> impl Reader<'a> {
        &mut **self
    }

    #[inline(always)]
    unsafe fn chunks(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> ReadResult<impl Iterator<Item = impl Reader<'a>>> {
        unsafe { (*self).chunks(chunk_size, n_chunks) }
    }

    #[inline(always)]
    unsafe fn chunk(&mut self, chunk_size: usize) -> ReadResult<impl Reader<'a>> {
        unsafe { (*self).chunk(chunk_size) }
    }

    #[inline(always)]
    fn read_exact(&mut self, buf: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        (*self).read_exact(buf)
    }

    #[inline(always)]
    fn read_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        (*self).read_array()
    }

    #[inline(always)]
    fn read_byte(&mut self) -> ReadResult<u8> {
        (*self).read_byte()
    }

    #[inline(always)]
    unsafe fn read_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        (*self).read_slice_t(dst)
    }

    #[inline(always)]
    unsafe fn read_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        (*self).read_t(dst)
    }

    #[inline(always)]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        (*self).borrow_exact(len)
    }

    #[inline(always)]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        (*self).borrow_exact_mut(len)
    }
}

#[derive(Error, Debug)]
pub enum WriteError {
    #[error("Attempting to write {0} bytes")]
    WriteSizeLimit(usize),
    #[cfg(feature = "std")]
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

#[cold]
const fn write_size_limit(len: usize) -> WriteError {
    WriteError::WriteSizeLimit(len)
}

pub type WriteResult<T> = core::result::Result<T, WriteError>;

/// Trait for structured writing of bytes into a source of potentially uninitialized memory.
pub trait Writer {
    /// # Safety
    unsafe fn chunks_mut(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> WriteResult<impl Iterator<Item = impl Writer>>;

    /// # Safety
    #[inline(always)]
    unsafe fn chunks_mut_zip<I>(
        &mut self,
        chunk_size: usize,
        iter: I,
    ) -> WriteResult<impl Iterator<Item = (I::Item, impl Writer)>>
    where
        I: ExactSizeIterator,
    {
        let mut chunks = unsafe { self.chunks_mut(chunk_size, iter.len()) }?;
        Ok(iter.map(move |item| (item, unsafe { chunks.next().unwrap_unchecked() })))
    }

    /// # Safety
    #[inline]
    unsafe fn chunk_mut(&mut self, chunk_size: usize) -> WriteResult<impl Writer> {
        let mut chunks = unsafe { self.chunks_mut(chunk_size, 1) }?;
        let Some(chunk) = chunks.next() else {
            return Err(write_size_limit(chunk_size));
        };
        Ok(chunk)
    }

    /// Get a mutable reference to the [`Writer`].
    ///
    /// Useful in situations where one has an `impl Writer` that
    /// needs to be passed to mulitple functions requiring `impl Writer`.
    ///
    /// Always prefer this over `&mut writer` to avoid recursive borrows.
    ///
    /// ```
    /// # use wincode::{io::Writer, WriteResult, config::Config, SchemaWrite};
    /// # use core::mem::MaybeUninit;
    /// struct FooBar {
    ///     foo: u32,
    ///     bar: u32,
    /// }
    ///
    /// unsafe impl<C: Config> SchemaWrite<C> for FooBar {
    ///     type Src = Self;
    /// #
    /// #    fn size_of(src: &Self::Src) -> WriteResult<usize> {
    /// #        let foo = <u32 as SchemaWrite<C>>::size_of(&src.foo)?;
    /// #        let bar = <u32 as SchemaWrite<C>>::size_of(&src.bar)?;
    /// #        Ok(foo + bar)
    /// #    }
    ///
    ///     fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
    ///         // `writer.by_ref()`; Good ✅
    ///         let foo = <u32 as SchemaWrite<C>>::write(writer.by_ref(), &src.foo)?;
    ///         let bar = <u32 as SchemaWrite<C>>::write(writer, &src.bar)?;
    ///         Ok(())
    ///     }
    /// }
    /// ```
    #[inline(always)]
    fn by_ref(&mut self) -> impl Writer {
        self
    }

    /// Finalize the writer by performing any required cleanup or flushing.
    ///
    /// # Regarding trusted writers
    ///
    /// Trusted writers are not guaranteed to live as long as the parent [`Writer`] that
    /// created them, and are typically short-lived. wincode will call `finish` after
    /// trusted writers have completed their work, so they may rely on `finish` perform
    /// local cleanup when needed. Importantly, trusted writers must not perform actions
    /// that would invalidate the parent [`Writer`].
    ///
    /// For example, a file writer may buffer internally and delegate to trusted
    /// sub-writers with their own buffers. These trusted writers should not close
    /// the underlying file descriptor or other parent-owned resources, as that would
    /// invalidate the parent writer.
    fn finish(&mut self) -> WriteResult<()> {
        Ok(())
    }

    /// Write exactly `src.len()` bytes from the given `src` into the writer.
    fn write(&mut self, src: &[u8]) -> WriteResult<()>;

    /// Write `T` as bytes into the source.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data.
    #[inline]
    unsafe fn write_t<T: ?Sized>(&mut self, src: &T) -> WriteResult<()> {
        let src = from_raw_parts((src as *const T).cast::<u8>(), size_of_val(src));
        self.write(src)?;
        Ok(())
    }

    /// Write `[T]` as bytes into the source.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data.
    #[inline]
    unsafe fn write_slice_t<T>(&mut self, src: &[T]) -> WriteResult<()> {
        let len = size_of_val(src);
        let src = from_raw_parts(src.as_ptr().cast::<u8>(), len);
        self.write(src)?;
        Ok(())
    }
}

impl<W: Writer + ?Sized> Writer for &mut W {
    #[inline(always)]
    unsafe fn chunks_mut(
        &mut self,
        chunk_size: usize,
        n_chunks: usize,
    ) -> WriteResult<impl Iterator<Item = impl Writer>> {
        (*self).chunks_mut(chunk_size, n_chunks)
    }

    #[inline(always)]
    unsafe fn chunk_mut(&mut self, chunk_size: usize) -> WriteResult<impl Writer> {
        (*self).chunk_mut(chunk_size)
    }

    #[inline(always)]
    fn by_ref(&mut self) -> impl Writer {
        &mut **self
    }

    #[inline(always)]
    fn finish(&mut self) -> WriteResult<()> {
        (*self).finish()
    }

    #[inline(always)]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        (*self).write(src)
    }

    #[inline(always)]
    unsafe fn write_t<T: ?Sized>(&mut self, src: &T) -> WriteResult<()> {
        (*self).write_t(src)
    }

    #[inline(always)]
    unsafe fn write_slice_t<T>(&mut self, src: &[T]) -> WriteResult<()> {
        (*self).write_slice_t(src)
    }
}

// mod cursor;
mod cursor;
pub mod slice;
#[cfg(feature = "alloc")]
mod vec;
pub use cursor::Cursor;
