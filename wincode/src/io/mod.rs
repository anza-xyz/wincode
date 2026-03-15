//! [`Reader`] and [`Writer`] implementations.
use {
    core::{
        mem::{self, MaybeUninit, transmute},
        ptr,
        slice::{from_raw_parts, from_raw_parts_mut},
    },
    thiserror::Error,
};

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum BorrowKind {
    /// Borrowed from the call site, not extending past it.
    CallSite,
    /// Borrowed from the backing store, extending past the call site.
    Backing,
    /// Mutably borrowed from the backing store, extending past the call site.
    BackingMut,
}

impl BorrowKind {
    #[inline]
    pub const fn mask(self) -> u8 {
        1u8 << (self as u8)
    }
}

impl core::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BorrowKind::CallSite => f.write_str("call-site scoped borrows"),
            BorrowKind::Backing => f.write_str("borrows extending past the call site"),
            BorrowKind::BackingMut => f.write_str("mutable borrows extending past the call site"),
        }
    }
}

#[derive(Error, Debug)]
pub enum ReadError {
    #[error("Attempting to read {0} bytes")]
    ReadSizeLimit(usize),
    #[error("Unsupported borrow operation: reader does not support {0}")]
    UnsupportedBorrow(BorrowKind),
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
/// # Borrowing semantics
/// - Only implement [`Reader::take_borrowed`] or [`Reader::take_borrowed_mut`] for sources
///   where stable borrows into the backing storage are possible.
/// - Callers should prefer [`Reader::copy_into_slice`] or `take_*` methods to remain
///   compatible with readers that don't support borrowing, if possible.
/// - Returns [`ReadError::UnsupportedBorrow`] for readers that do not support borrowing.
pub trait Reader<'a> {
    /// Borrow capabilities of this reader.
    ///
    /// A bitmask of [`BorrowKind`] values indicating which kinds of borrows are supported.
    ///
    /// Users of [`Reader`] can call [`Reader::supports_borrow`] to check if a borrow kind
    /// is supported.
    const BORROW_KINDS: u8 = 0;

    /// Checks if this reader supports the given borrow kind.
    ///
    /// # Examples
    /// ```
    /// # use wincode::io::{Reader, BorrowKind, Cursor};
    /// #
    /// let reader = [1, 2, 3, 4, 5];
    /// assert!(reader.as_slice().supports_borrow(BorrowKind::Backing));
    ///
    /// let mut reader = [1, 2, 3, 4, 5];
    /// assert!(reader.as_mut_slice().supports_borrow(BorrowKind::BackingMut));
    ///
    /// let reader = Cursor::new([1, 2, 3, 4, 5]);
    /// assert!(reader.supports_borrow(BorrowKind::CallSite));
    /// assert!(!reader.supports_borrow(BorrowKind::Backing));
    /// ```
    #[inline]
    fn supports_borrow(&self, kind: BorrowKind) -> bool {
        Self::BORROW_KINDS & kind.mask() != 0
    }

    /// Return exactly `N` bytes as `&[u8; N]` without advancing.
    ///
    /// Errors if fewer than `N` bytes are available.
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]>;

    /// Get the next byte without advancing.
    ///
    /// Errors if no bytes remain.
    #[inline]
    fn peek_byte(&mut self) -> ReadResult<u8> {
        Ok(self.peek_array::<1>()?[0])
    }

    /// Return exactly `N` bytes as `[u8; N]` and advance by `N`.
    ///
    /// Errors if fewer than `N` bytes are available.
    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let mut ar = MaybeUninit::<[u8; N]>::uninit();

        self.copy_into_slice(transpose(&mut ar))?;
        Ok(unsafe { ar.assume_init() })
    }

    /// Return the next byte and advance by `1`.
    ///
    /// Errors if the reader is exhausted.
    #[inline(always)]
    fn take_byte(&mut self) -> ReadResult<u8> {
        Ok(self.take_array::<1>()?[0])
    }

    /// Return a borrowed slice of exactly `len` bytes and advance
    /// the reader by `len`.
    ///
    /// The returned slice is tied to the reader's backing lifetime `'a`.
    /// This means the slice may outlive the borrow of the call, and is
    /// valid after the reader is dropped or reborrowed.
    ///
    /// This stronger guarantee is typically only possible for readers backed
    /// by stable storage (for example `&'a [u8]` or memory-mapped buffers).
    ///
    /// Prefer [`Reader::take_scoped`] unless you specifically require a slice
    /// that lives for `'a`. Prefer [`Reader::copy_into_slice`] if you ultimately
    /// intend to copy the slice.
    ///
    /// Errors if the reader cannot provide `len` bytes or does not support
    /// borrowing into stable storage that outlives the reader.
    #[expect(unused_variables)]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        Err(ReadError::UnsupportedBorrow(BorrowKind::Backing))
    }

    /// Return a mutably borrowed slice of exactly `len` bytes and advance
    /// the reader by `len`.
    ///
    /// The returned slice is tied to the reader's backing lifetime `'a`.
    /// This means the slice may outlive the borrow of the call, and is
    /// valid after the reader is dropped or reborrowed.
    ///
    /// This stronger guarantee is typically only possible for readers backed
    /// by stable storage (for example `&'a mut [u8]` or memory-mapped buffers).
    ///
    /// Errors if the reader cannot provide `len` bytes or does not support
    /// mutable borrowing into stable, mutable storage that outlives the reader.
    #[expect(unused_variables)]
    fn take_borrowed_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        Err(ReadError::UnsupportedBorrow(BorrowKind::BackingMut))
    }

    /// Return a call-site scoped slice of exactly `len` bytes and advance by `len`.
    ///
    /// The returned slice is tied to the borrow of `self`, meaning it is only
    /// valid while the current borrow of the reader is alive. Implementations
    /// are free to return slices backed by internal buffers or transient windows
    /// into the underlying source.
    ///
    /// Prefer [`Reader::copy_into_slice`] if you ultimately intend to copy the slice.
    ///
    /// Errors for readers that don't support call-site scoped borrowing.
    #[expect(unused_variables)]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        Err(ReadError::UnsupportedBorrow(BorrowKind::CallSite))
    }

    /// Advance by exactly `amt` bytes without bounds checks.
    ///
    /// May panic if fewer than `amt` bytes remain.
    ///
    /// # Safety
    ///
    /// - `amt` must be less than or equal to the number of bytes remaining in the reader.
    unsafe fn consume_unchecked(&mut self, amt: usize);

    /// Advance the reader by `amt` bytes.
    ///
    /// This method must be safe for any `amt`.
    /// If `amt` exceeds the bytes currently available or remaining, implementations
    /// may handle the over-consumption in an implementation-defined way, such as
    /// clamping to exhaustion or advancing according to the reader's underlying
    /// model. Callers must not rely on a specific outcome in that case.
    ///
    /// Unlike [`Reader::consume_unchecked`], this method must not invoke undefined
    /// behavior when `amt` exceeds the reader's available bytes.
    fn consume(&mut self, amt: usize);

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
        // SAFETY: Caller ensures that `T` is initialized by reads of `size_of::<T>()` bytes.
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
        // SAFETY: Caller ensures that `T` is initialized by reads of `size_of::<T>()` bytes.
        let dst = unsafe { from_raw_parts_mut(dst.as_mut_ptr().cast::<MaybeUninit<u8>>(), len) };
        self.copy_into_slice(dst)
    }
}

impl<'a, R: Reader<'a> + ?Sized> Reader<'a> for &mut R {
    const BORROW_KINDS: u8 = R::BORROW_KINDS;

    #[inline(always)]
    fn by_ref(&mut self) -> impl Reader<'a> {
        &mut **self
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        (*self).take_array()
    }

    #[inline(always)]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        (*self).take_scoped(len)
    }

    #[inline(always)]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        (*self).take_borrowed(len)
    }

    #[inline(always)]
    fn take_borrowed_mut(&mut self, len: usize) -> ReadResult<&'a mut [u8]> {
        (*self).take_borrowed_mut(len)
    }

    #[inline(always)]
    fn take_byte(&mut self) -> ReadResult<u8> {
        (*self).take_byte()
    }

    #[inline(always)]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        unsafe { (*self).consume_unchecked(amt) }
    }

    #[inline(always)]
    fn consume(&mut self, amt: usize) {
        (*self).consume(amt)
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        unsafe { (*self).as_trusted_for(n_bytes) }
    }

    #[inline(always)]
    fn peek_array<const N: usize>(&mut self) -> ReadResult<&[u8; N]> {
        (*self).peek_array()
    }

    #[inline(always)]
    fn peek_byte(&mut self) -> ReadResult<u8> {
        (*self).peek_byte()
    }

    #[inline(always)]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        (*self).copy_into_slice(dst)
    }

    #[inline(always)]
    unsafe fn copy_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        unsafe { (*self).copy_into_t(dst) }
    }

    #[inline(always)]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        unsafe { (*self).copy_into_slice_t(dst) }
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
        let src = unsafe { from_raw_parts((src as *const T).cast::<u8>(), size_of_val(src)) };
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
        let src = unsafe { from_raw_parts(src.as_ptr().cast::<u8>(), len) };
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
        unsafe { (*self).as_trusted_for(n_bytes) }
    }

    #[inline(always)]
    unsafe fn write_t<T: ?Sized>(&mut self, src: &T) -> WriteResult<()> {
        unsafe { (*self).write_t(src) }
    }

    #[inline(always)]
    unsafe fn write_slice_t<T>(&mut self, src: &[T]) -> WriteResult<()> {
        unsafe { (*self).write_slice_t(src) }
    }
}

mod cursor;
pub mod slice;
#[cfg(feature = "alloc")]
mod vec;
pub use cursor::Cursor;
