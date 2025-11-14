//! [`Reader`] and [`Writer`] implementations.
use {
    core::{
        mem::{self, transmute, MaybeUninit},
        ptr,
        slice::from_raw_parts,
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
const fn read_size_limit(len: usize) -> ReadError {
    ReadError::ReadSizeLimit(len)
}

/// Trait for structured reading of bytes from a source into potentially uninitialized memory.
///
/// # Advancement semantics
/// - `fill_*` methods never advance.
/// - `copy_into_*` and `borrow_*` methods advance by the number of bytes read.
/// - [`Reader::as_trusted_for`] advances the parent by the number of bytes requested.
///
/// # Zero-copy semantics
/// Only implement [`Reader::borrow_exact`] for sources where stable borrows into the backing storage are possible.
/// Callers should prefer [`Reader::fill_exact`] to remain compatible with readers that don’t support zero-copy.
/// Returns [`ReadError::UnsupportedZeroCopy`] for readers that do not support zero-copy.
pub trait Reader<'a> {
    /// A variant of the [`Reader`] that can elide bounds checking within a given window.
    ///
    /// Trusted variants of the [`Reader`] should generally not be constructed directly,
    /// but rather by calling [`Reader::as_trusted_for`] on a trusted [`Reader`].
    /// This will ensure that the safety invariants are upheld.
    type Trusted<'b>: Reader<'a>
    where
        Self: 'b;

    /// Return up to `n_bytes` from the internal buffer without advancing. Implementations may
    /// read more data internally to satisfy future requests. Returns fewer than `n_bytes` at EOF.
    ///
    /// This is _not_ required to return exactly `n_bytes`, it is required to return _up to_ `n_bytes`.
    /// Use [`Reader::fill_exact`] if you need exactly `n_bytes`.
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]>;

    /// Return exactly `n_bytes` without advancing.
    ///
    /// Errors if the source cannot provide enough bytes.
    fn fill_exact(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        let src = self.fill_buf(n_bytes)?;
        if src.len() != n_bytes {
            return Err(read_size_limit(n_bytes));
        }
        Ok(src)
    }

    /// Return exactly `N` bytes as `&[u8; N]` without advancing.
    ///
    /// Errors if fewer than `N` bytes are available.
    fn fill_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        let src = self.fill_exact(N)?;
        // SAFETY:
        // - `fill_exact` ensures we read N bytes.
        Ok(unsafe { &*src.as_ptr().cast::<[u8; N]>() })
    }

    /// Zero-copy: return a borrowed slice of exactly `len` bytes and advance by `len`.
    ///
    /// The returned slice is tied to `'a`. Prefer [`Reader::fill_exact`] unless you truly need zero-copy.
    /// Errors for readers that don't support zero-copy.
    #[allow(unused_variables)]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        Err(ReadError::UnsupportedZeroCopy)
    }

    /// Advance by exactly `amt` bytes without bounds checks.
    ///
    /// May panic if fewer than `amt` bytes remain.
    ///
    /// # Safety
    ///
    /// - `amt` must be less than or equal to the number of bytes remaining in the reader.
    unsafe fn consume_unchecked(&mut self, amt: usize);

    /// Advance the reader exactly `amt` bytes, returning an error if the source does not have enough bytes.
    fn consume(&mut self, amt: usize) -> ReadResult<()>;

    /// Advance the parent by `n_bytes` and return a [`Reader`] that can elide bounds checks within
    /// that `n_bytes` window.
    ///
    /// Implementations may use this to bulk prefetch bytes for the `n_bytes` window.
    ///
    /// Implementations must ensure at least `n_bytes` are available or return an error.
    /// Callers must not read beyond `n_bytes` on the returned reader; behavior is unspecified beyond that.
    fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>>;

    /// Return a reference to the next byte without advancing.
    ///
    /// May buffer more bytes if necessary. Errors if no bytes remain.
    #[inline]
    fn peek(&mut self) -> ReadResult<&u8> {
        self.fill_buf(1)?.first().ok_or_else(|| read_size_limit(1))
    }

    /// Copy and consume exactly `dst.len()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = self.fill_exact(dst.len())?;
        // SAFETY:
        // - `fill_exact` must do the appropriate bounds checking.
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr().cast(), dst.as_mut_ptr(), dst.len());
            self.consume_unchecked(dst.len());
        }
        Ok(())
    }

    /// Copy and consume exactly `N` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    fn copy_into_array<const N: usize>(
        &mut self,
        dst: &mut MaybeUninit<[u8; N]>,
    ) -> ReadResult<()> {
        let src = self.fill_array::<N>()?;
        // SAFETY:
        // - `fill_array` must do the appropriate bounds checking.
        unsafe {
            ptr::copy_nonoverlapping(src, dst.as_mut_ptr(), 1);
            self.consume_unchecked(N);
        }
        Ok(())
    }

    /// Copy and consume exactly `size_of::<T>()` bytes from the [`Reader`] into `dst`.
    ///
    /// # Safety
    ///
    /// - `T` must be initialized by reads of `size_of::<T>()` bytes.
    /// - `dst` must not overlap with the internal buffer.
    #[inline]
    unsafe fn copy_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        let src = self.fill_exact(size_of::<T>())?;
        // SAFETY:
        // - `fill_exact` must do the appropriate bounds checking.
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), size_of::<T>());
            self.consume_unchecked(size_of::<T>());
        }
        Ok(())
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
        let bytes = self.fill_exact(len)?;
        // SAFETY:
        // - `fill_exact` must do the appropriate bounds checking.
        unsafe {
            ptr::copy_nonoverlapping(bytes.as_ptr(), dst.as_mut_ptr().cast(), len);
            self.consume_unchecked(len);
        }
        Ok(())
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
    /// A variant of the [`Writer`] that can elide bounds checking within a given window.
    ///
    /// Trusted variants of the [`Writer`] should generally not be constructed directly,
    /// but rather by calling [`Writer::as_trusted_for`] on a trusted [`Writer`].
    /// This will ensure that the safety invariants are upheld.
    type Trusted<'a>: Writer
    where
        Self: 'a;

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
    /// Implementations must ensure at least `n_bytes` are available for writing or return an error.
    /// Callers must not write beyond `n_bytes` on the returned writer; behavior is unspecified beyond that.
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>>;

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

mod cursor;
mod slice;
#[cfg(feature = "alloc")]
mod vec;
pub use {cursor::Cursor, slice::*};
