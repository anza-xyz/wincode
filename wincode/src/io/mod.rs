//! [`Reader`] and [`Writer`] implementations.
use {
    core::{
        mem::{self, transmute, MaybeUninit},
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
pub(super) const fn transpose<const N: usize, T>(
    src: &mut MaybeUninit<[T; N]>,
) -> &mut [MaybeUninit<T>; N] {
    unsafe { transmute(src) }
}

/// Trait for structured reading of bytes from a source into potentially uninitialized memory.
///
/// # Zero-copy semantics
/// Only implement [`Reader::borrow_exact`] for sources where stable borrows into the backing storage are possible.
/// Callers should prefer [`Reader::copy_into_slice`] to remain compatible with readers that don’t support zero-copy.
/// Returns [`ReadError::UnsupportedZeroCopy`] for readers that do not support zero-copy.
pub trait Reader<'a> {
    /// Return exactly `N` bytes as `[u8; N]` and advance by `N`.
    ///
    /// Errors if fewer than `N` bytes are available.
    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let mut ar = MaybeUninit::<[u8; N]>::uninit();

        self.copy_into_slice(transpose(&mut ar))?;
        Ok(unsafe { ar.assume_init() })
    }

    #[inline(always)]
    fn take_byte(&mut self) -> ReadResult<u8> {
        Ok(self.take_array::<1>()?[0])
    }

    /// Zero-copy: return a borrowed slice of exactly `len` bytes and advance by `len`.
    ///
    /// The returned slice is tied to `'a`. Prefer [`Reader::copy_into_slice`] unless you truly need zero-copy.
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

    /// Advance the parent by `n_bytes` and return a [`Reader`] that can elide bounds checks within
    /// that `n_bytes` window.
    ///
    /// Implementors must:
    /// - Ensure that either at least `n_bytes` bytes are available backing the
    ///   returned reader, or return an error.
    /// - Arrange that the returned `Trusted` reader's methods operate within
    ///   that `n_bytes` window (it may buffer or prefetch arbitrarily).
    ///
    /// Note:
    /// - `as_trusted_for` is intended for callers that know they will operate
    ///   within a fixed-size window and want to avoid intermediate bounds checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that, through the returned reader, they do not
    /// cause more than `n_bytes` bytes to be logically read or consumed
    /// without performing additional bounds checks.
    ///
    /// Concretely:
    /// - The total number of bytes accessed/consumed via the `Trusted` reader
    ///   (`copy_into_*`, `take_*`, etc.) must be **<= `n_bytes`**.
    ///
    /// Violating this is undefined behavior, because `Trusted` readers are
    /// permitted to elide bounds checks within the `n_bytes` window; reading past the
    /// `n_bytes` window may read past the end of the underlying buffer.
    #[expect(unused_variables)]
    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        Ok(self)
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

    /// Copy and consume exactly `dst.len()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `dst` must not overlap with the internal buffer.
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()>;

    /// Copy and consume exactly `size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    unsafe fn copy_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        let dst = unsafe {
            from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), size_of::<T>())
        };
        self.copy_into_slice(dst)
    }

    /// Copy and consume exactly `dst.len() * size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        let len = size_of_val(dst);
        let dst = unsafe { from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), len) };
        self.copy_into_slice(dst)
    }
}

impl<'a, R: Reader<'a> + ?Sized> Reader<'a> for &mut R {
    #[inline(always)]
    fn by_ref(&mut self) -> impl Reader<'a> {
        &mut **self
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        (*self).take_array()
    }

    #[inline(always)]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        (*self).borrow_exact(len)
    }

    #[inline(always)]
    fn borrow_exact_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        (*self).borrow_exact_mut(len)
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        (*self).as_trusted_for(n_bytes)
    }

    #[inline(always)]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        (*self).copy_into_slice(dst)
    }

    #[inline(always)]
    unsafe fn copy_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        (*self).copy_into_t(dst)
    }

    #[inline(always)]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        (*self).copy_into_slice_t(dst)
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

    /// Advance the parent by `n_bytes` and return a [`Writer`] that can elide bounds checks within
    /// that `n_bytes` window.
    ///
    /// Implementors must:
    /// - Ensure that either at least `n_bytes` bytes are available backing the
    ///   returned writer, or return an error.
    /// - Arrange that the returned `Trusted` writer's methods operate within
    ///   that `n_bytes` window (it may buffer or prefetch arbitrarily).
    ///
    /// Note:
    /// - `as_trusted_for` is intended for callers that know they will operate
    ///   within an exact-size window and want to avoid intermediate bounds checks.
    ///
    /// # Safety
    ///
    /// The caller must treat the returned writer as having exclusive access to
    /// exactly `n_bytes` bytes of **uninitialized** output space in the parent,
    /// and must:
    ///
    /// - Ensure that no write performed through the `Trusted` writer can
    ///   address memory outside of that `n_bytes` window.
    /// - In case the caller does not return an error, ensure that, before the
    ///   `Trusted` writer is finished or the parent writer is used again,
    ///   **every byte** in that `n_bytes` window has been initialized at least
    ///   once via the `Trusted` writer.
    /// - In case the caller does not return an error, call [`Writer::finish`]
    ///   on the `Trusted` writer when writing is complete and before the parent
    ///   writer is used again.
    ///
    /// Concretely:
    /// - All writes performed via the `Trusted` writer (`write`, `write_t`,
    ///   `write_slice_t`, etc.) must stay within the `[0, n_bytes)` region of
    ///   the reserved space.
    /// - It is permitted to overwrite the same bytes multiple times, but if the
    ///   caller returns no error, the union of all bytes written must cover the
    ///   entire `[0, n_bytes)` window.
    ///
    /// Violating this is undefined behavior, because:
    /// - `Trusted` writers are permitted to elide bounds checks within the
    ///   `n_bytes` window; writing past the window may write past the end of
    ///   the underlying destination.
    /// - Failing to initialize all `n_bytes` without returning an error may
    ///   leave uninitialized memory in the destination that later safe code
    ///   assumes to be fully initialized.
    #[expect(unused_variables)]
    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        Ok(self)
    }

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
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        (*self).as_trusted_for(n_bytes)
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

mod cursor;
pub mod slice;
#[cfg(feature = "alloc")]
mod vec;
pub use cursor::Cursor;
