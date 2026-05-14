#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use {
    super::*,
    core::ptr::copy_nonoverlapping,
    slice::{SliceMutUnchecked, SliceScopedUnchecked},
};

/// `Cursor` wraps an in-memory buffer, providing [`Reader`] and [`Writer`] functionality
/// for types implementing <code>[AsRef]<\[u8]></code>.
///
/// This can be especially useful for wrapping [`Reader`]s and [`Writer`]s that are consumed by
/// reading or writing like `&[u8]` or `&mut [MaybeUninit<u8>]`, making them reusable.
///
/// # Examples
///
/// Using `Cursor` to write to a `MaybeUninit<[u8; N]>`.
///
/// ```
/// # use rand::random;
/// # use core::mem::MaybeUninit;
/// use wincode::io::{Cursor, Reader, Writer};
///
/// fn rand_bytes() -> [u8; 8] {
///     random::<u64>().to_le_bytes()
/// }
///
/// let mut data = MaybeUninit::<[u8; 8]>::uninit();
///
/// let mut cursor = Cursor::new(&mut data);
/// let bytes = rand_bytes();
/// cursor.write(&bytes).unwrap();
/// assert_eq!(unsafe { data.assume_init() }, bytes);
///
/// // We can write over the same buffer multiple times with a new Cursor.
/// let mut cursor = Cursor::new(&mut data);
/// let bytes = rand_bytes();
/// cursor.write(&bytes).unwrap();
/// assert_eq!(unsafe { data.assume_init() }, bytes);
/// ```
///
/// Using `Cursor` to write to a `Vec`'s spare capacity.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use rand::random;
/// use wincode::io::{Cursor, Reader, Writer};
///
/// # fn rand_bytes() -> [u8; 8] {
/// #     random::<u64>().to_le_bytes()
/// # }
/// let mut data = Vec::with_capacity(8);
///
/// let mut cursor = Cursor::new(&mut data);
/// let bytes = rand_bytes();
/// cursor.write(&bytes).unwrap();
/// assert_eq!(data, bytes);
///
/// // We can write over the same buffer multiple times with a new Cursor.
/// let mut cursor = Cursor::new(&mut data);
/// let bytes = rand_bytes();
/// cursor.write(&bytes).unwrap();
/// assert_eq!(data, bytes);
/// # }
/// ```
pub struct Cursor<T> {
    inner: T,
    pos: usize,
}

impl<T> Cursor<T> {
    pub const fn new(inner: T) -> Self {
        Self { inner, pos: 0 }
    }

    /// Creates a new cursor at the given position.
    pub const fn new_at(inner: T, pos: usize) -> Self {
        Self { inner, pos }
    }

    /// Sets the position of the cursor.
    pub const fn set_position(&mut self, pos: usize) {
        self.pos = pos;
    }

    /// Consumes the cursor and returns the inner value.
    pub fn into_inner(self) -> T {
        self.inner
    }

    /// Returns the current position of the cursor.
    pub const fn position(&self) -> usize {
        self.pos
    }
}

#[inline(always)]
#[expect(clippy::arithmetic_side_effects)]
fn advance_slice_checked<'a, T>(buf: &'a [T], pos: &mut usize, len: usize) -> Option<&'a [T]> {
    let buf_len = buf.len();
    let buf = buf[(*pos).min(buf_len)..].get(..len)?;
    *pos += len;
    Some(buf)
}

#[inline(always)]
#[expect(clippy::arithmetic_side_effects)]
fn advance_slice_mut_checked<'a, T>(
    buf: &'a mut [T],
    pos: &mut usize,
    len: usize,
) -> Option<&'a mut [T]> {
    let buf_len = buf.len();
    let buf = buf[(*pos).min(buf_len)..].get_mut(..len)?;
    *pos += len;
    Some(buf)
}

impl<T> Cursor<T>
where
    T: AsRef<[u8]>,
{
    /// Split the cursor at `len` and consume the left slice.
    #[inline(always)]
    fn advance_slice_checked(&mut self, len: usize) -> ReadResult<&[u8]> {
        let Some(slice) = advance_slice_checked(self.inner.as_ref(), &mut self.pos, len) else {
            return Err(read_size_limit(len));
        };
        Ok(slice)
    }
}

impl<'a, T> Reader<'a> for Cursor<T>
where
    T: AsRef<[u8]>,
{
    const BORROW_KINDS: u8 = BorrowKind::CallSite.mask();

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = self.advance_slice_checked(dst.len())?;
        // SAFETY:
        // - `advance_slice_checked` guarantees that `src` is exactly `dst.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `dst` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) }
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let src = self.advance_slice_checked(N)?;
        // SAFETY: advance_slice_checked guarantees that `src` is exactly `N` bytes.
        Ok(unsafe { *(src.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.advance_slice_checked(len)
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        let window = self.advance_slice_checked(n_bytes)?;
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will will not read beyond the bounds of the slice, `n_bytes`.
        Ok(unsafe { SliceScopedUnchecked::new(window) })
    }
}

impl<T> Cursor<&mut [T]> {
    #[inline(always)]
    fn advance_slice_mut_checked(&mut self, len: usize) -> WriteResult<&mut [T]> {
        let Some(slice) = advance_slice_mut_checked(self.inner, &mut self.pos, len) else {
            return Err(write_size_limit(len));
        };
        Ok(slice)
    }
}

impl Writer for Cursor<&mut [MaybeUninit<u8>]> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.advance_slice_mut_checked(src.len())?;
        // SAFETY:
        // - `advance_slice_mut_checked` guarantees that `dst` is exactly `src.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }

        Ok(())
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        let window = self.advance_slice_mut_checked(n_bytes)?;
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of the slice.
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }
}

impl Writer for Cursor<&mut [u8]> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.advance_slice_mut_checked(src.len())?;
        // SAFETY:
        // - `advance_slice_mut_checked` guarantees that `dst` is exactly `src.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }
        Ok(())
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        let window = self.advance_slice_mut_checked(n_bytes)?;
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of the slice.
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }
}

impl<const N: usize> Cursor<&mut MaybeUninit<[u8; N]>> {
    #[inline(always)]
    fn advance_slice_mut_checked(&mut self, len: usize) -> WriteResult<&mut [MaybeUninit<u8>]> {
        let Some(slice) = advance_slice_mut_checked(transpose(self.inner), &mut self.pos, len)
        else {
            return Err(write_size_limit(len));
        };
        Ok(slice)
    }
}

impl<const N: usize> Writer for Cursor<&mut MaybeUninit<[u8; N]>> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.advance_slice_mut_checked(src.len())?;
        // SAFETY:
        // - `advance_slice_mut_checked` guarantees that `dst` is exactly `src.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap
        //   with the internal buffer.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }

        Ok(())
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        let window = self.advance_slice_mut_checked(n_bytes)?;
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of the slice.
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }
}

/// Helper functions for writing to `Cursor<&mut Vec<u8>>` and `Cursor<Vec<u8>>`.
#[cfg(feature = "alloc")]
pub(super) mod vec {
    use super::*;

    /// Grow the vector if necessary to accommodate the given `needed` bytes.
    ///
    /// Note this differs from [`Vec::reserve`] in that it reserves relative to the cursor's
    /// current position, rather than the initialized length of the vector. The `Cursor<Vec<u8>>`
    /// implementation overwrites existing elements of the vector, so growing relative to length
    /// would unnecessarily over-allocate memory.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    #[inline]
    fn maybe_grow(inner: &mut Vec<u8>, pos: usize, needed: usize) -> WriteResult<()> {
        let Some(required) = pos.checked_add(needed) else {
            return Err(write_size_limit(needed));
        };
        if required > inner.capacity() {
            grow(inner, required);
        }
        #[cold]
        fn grow(inner: &mut Vec<u8>, required: usize) {
            // SAFETY: We just checked that `required > inner.capacity()` (which is greater than
            // or equal to `inner.len()`), so this will not underflow.
            let additional = unsafe { required.unchecked_sub(inner.len()) };
            inner.reserve(additional);
        }
        Ok(())
    }

    /// Zero-fill the gap between `inner.len()` and `pos`, if `pos` is past the
    /// current initialized length.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `inner.capacity() >= pos`.
    ///
    /// If `pos > inner.len()`, the range `inner.len()..pos` must be spare capacity
    /// owned by `inner` and valid to write as `MaybeUninit<u8>`. This function
    /// initializes that entire gap with zero bytes.
    ///
    /// Callers should normally establish this by calling `maybe_grow(inner, pos, n)`
    /// with any `n` such that `pos + n` is checked and fits in the vector capacity.
    #[inline]
    unsafe fn zero_fill_gap(inner: &mut Vec<u8>, pos: usize) {
        if let Some(init_gap) = pos.checked_sub(inner.len()) {
            let spare = inner.spare_capacity_mut();
            debug_assert!(spare.len() >= init_gap);

            unsafe {
                spare
                    .get_unchecked_mut(..init_gap)
                    .fill(MaybeUninit::new(0));
            }
        }
    }

    /// Prepare `inner` for a write of `needed` bytes starting at cursor position `pos`.
    ///
    /// This checks that `pos + needed` fits in `usize`, ensures the vector has enough
    /// capacity for the whole write window, and zero-initializes any sparse gap between
    /// the current length and `pos`. It does not change the vector's length: callers must
    /// only expose newly initialized bytes after the write window itself has been
    /// initialized, typically via [`add_len`] or an equivalent `set_len`.
    #[inline]
    pub(crate) fn prepare_write(inner: &mut Vec<u8>, pos: usize, needed: usize) -> WriteResult<()> {
        maybe_grow(inner, pos, needed)?;
        // SAFETY: `maybe_grow` checked `pos + needed` and ensured capacity for it,
        // so `inner.capacity() >= pos`; `zero_fill_gap` only writes `inner.len()..pos`.
        unsafe { zero_fill_gap(inner, pos) };
        Ok(())
    }

    /// Add `len` to the cursor's position and update the length of the vector if necessary.
    ///
    /// # SAFETY:
    /// - Must be called after a successful write to the vector.
    #[inline(always)]
    pub(super) unsafe fn add_len(inner: &mut Vec<u8>, pos: &mut usize, len: usize) {
        // SAFETY: We just wrote `len` bytes to the vector, so `pos + len` is valid.
        let next_pos = unsafe { pos.unchecked_add(len) };

        // If pos exceeds the length of the vector, we just wrote to uninitialized capacity,
        // which is now initialized.
        if next_pos > inner.len() {
            unsafe {
                inner.set_len(next_pos);
            }
        }
        *pos = next_pos;
    }

    /// Write `src` to the vector at the current position and advance the position by `src.len()`.
    pub(super) fn write(inner: &mut Vec<u8>, pos: &mut usize, src: &[u8]) -> WriteResult<()> {
        prepare_write(inner, *pos, src.len())?;
        // SAFETY: `prepare_write` ensured at least `*pos + src.len()` capacity is
        // available.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), inner.as_mut_ptr().add(*pos), src.len()) };
        // SAFETY: `prepare_write` initialized any gap before `*pos`, and we
        // just wrote `src.len()` bytes starting at `*pos`.
        unsafe { add_len(inner, pos, src.len()) };
        Ok(())
    }

    #[inline]
    pub(super) unsafe fn as_trusted_for<'a>(
        inner: &'a mut Vec<u8>,
        pos: &'a mut usize,
        n_bytes: usize,
    ) -> WriteResult<impl Writer> {
        prepare_write(inner, *pos, n_bytes)?;
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will fully initialize `n_bytes` of memory and will not write
        // beyond the bounds of the slice.
        Ok(unsafe { VecPosUnchecked::new(inner, pos) })
    }
}

#[cfg(feature = "alloc")]
struct VecPosUnchecked<'a> {
    inner: &'a mut Vec<u8>,
    pos: &'a mut usize,
}

#[cfg(feature = "alloc")]
impl<'a> VecPosUnchecked<'a> {
    /// # Safety
    ///
    /// The caller must ensure that `*pos` is within `inner`'s capacity and
    /// that any gap before `*pos` has already been initialized. Writes through
    /// this unchecked writer must stay within the trusted window reserved by
    /// the caller.
    const unsafe fn new(inner: &'a mut Vec<u8>, pos: &'a mut usize) -> Self {
        Self { inner, pos }
    }
}

#[cfg(feature = "alloc")]
impl<'a> Writer for VecPosUnchecked<'a> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        // SAFETY:
        // - `as_trusted_for` ensured sufficient capacity for the trusted window before
        //   constructing this writer.
        // - The trusted-writer contract requires all writes through this writer to stay
        //   within that reserved window.
        // - Given Rust's aliasing rules, we can assume that `src` does not overlap with
        //   the internal buffer.
        unsafe {
            copy_nonoverlapping(
                src.as_ptr(),
                self.inner.as_mut_ptr().add(*self.pos),
                src.len(),
            );
        }

        // SAFETY: any gap before the trusted window was initialized before
        // constructing this writer, and this call just initialized the bytes
        // from the previous cursor position through `next_pos`.
        unsafe { vec::add_len(self.inner, self.pos, src.len()) }

        Ok(())
    }
}

/// Writer implementation for `&mut Vec<u8>` that overwrites the underlying vector's memory.
/// The vector will grow as needed.
///
/// # Examples
///
/// Overwriting an existing vector.
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::io::{Cursor, Writer};
/// let mut vec = vec![0; 3];
/// let mut cursor = Cursor::new(&mut vec);
/// let bytes = [1, 2, 3, 4];
/// cursor.write(&bytes).unwrap();
/// assert_eq!(&vec, &[1, 2, 3, 4]);
/// # }
/// ```
///
/// Growing a vector.
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::io::{Cursor, Writer};
/// let mut vec = vec![];
/// let mut cursor = Cursor::new(&mut vec);
/// let bytes = [1, 2, 3];
/// cursor.write(&bytes).unwrap();
/// assert_eq!(&vec, &[1, 2, 3]);
/// # }
/// ```
#[cfg(feature = "alloc")]
impl Writer for Cursor<&mut Vec<u8>> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        vec::write(self.inner, &mut self.pos, src)
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        unsafe { vec::as_trusted_for(self.inner, &mut self.pos, n_bytes) }
    }
}

/// Writer implementation for `Vec<u8>` that overwrites the underlying vector's memory.
/// The vector will grow as needed.
/// # Examples
///
/// Overwriting an existing vector.
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::io::{Cursor, Writer};
/// let mut cursor = Cursor::new(vec![0; 3]);
/// let bytes = [1, 2, 3, 4];
/// cursor.write(&bytes).unwrap();
/// assert_eq!(cursor.into_inner(), &[1, 2, 3, 4]);
/// # }
/// ```
///
/// Growing a vector.
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::io::{Cursor, Writer};
/// let mut cursor = Cursor::new(vec![]);
/// let bytes = [1, 2, 3];
/// cursor.write(&bytes).unwrap();
/// assert_eq!(cursor.into_inner(), &[1, 2, 3]);
/// # }
/// ```
#[cfg(feature = "alloc")]
impl Writer for Cursor<Vec<u8>> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        vec::write(&mut self.inner, &mut self.pos, src)
    }

    #[inline(always)]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        unsafe { vec::as_trusted_for(&mut self.inner, &mut self.pos, n_bytes) }
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, alloc::vec, proptest::prelude::*};

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn cursor_read_no_panic_no_ub_check(bytes in any::<Vec<u8>>(), pos in any::<usize>()) {
            let mut cursor = Cursor::new_at(&bytes, pos);

            let mut dst = Vec::with_capacity(bytes.len());
            let res = cursor.copy_into_slice(dst.spare_capacity_mut());
            if pos > bytes.len() && !bytes.is_empty() {
                prop_assert!(matches!(res, Err(ReadError::ReadSizeLimit(x)) if x == bytes.len()));
            } else {
                unsafe { dst.set_len(bytes.len()) };
                prop_assert_eq!(&dst, &bytes[pos.min(bytes.len())..]);
            }
        }

        #[test]
        fn cursor_zero_len_ops_ok(bytes in any::<Vec<u8>>(), pos in any::<usize>()) {
            let mut cursor = Cursor::new_at(&bytes, pos);
            let start = cursor.position();

            let mut buf: [MaybeUninit::<u8>; 0] = [];
            cursor.copy_into_slice(&mut buf).unwrap();
            prop_assert_eq!(cursor.position(), start);

            unsafe { <Cursor<_> as Reader>::as_trusted_for(&mut cursor, 0) }.unwrap();
            prop_assert_eq!(cursor.position(), start);
        }

        #[test]
        fn cursor_as_trusted_for_remaining_advances_to_len(bytes in any::<Vec<u8>>(), pos in any::<usize>()) {
            // Clamp pos to be within [0, len] so the request is valid.
            let len = bytes.len();
            let pos = if len == 0 { 0 } else { pos % (len + 1) };
            let mut cursor = Cursor::new_at(&bytes, pos);
            let remaining = len.saturating_sub(pos);

            {
                let _trusted = unsafe { <Cursor<_> as Reader>::as_trusted_for(&mut cursor, remaining) }.unwrap();
            }

            // After consuming the exact remaining, position should be exactly len.
            prop_assert_eq!(cursor.position(), len);
        }

        #[test]
        fn cursor_extremal_pos_max_zero_len_ok(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new_at(&bytes, usize::MAX);

            // Zero-length ops still succeed and do not advance.
            let mut buf: [MaybeUninit::<u8>; 0] = [];
            let start = cursor.position();
            prop_assert!(cursor.copy_into_slice(&mut buf).is_ok());
            {
                let _trusted = unsafe { <Cursor<_> as Reader>::as_trusted_for(&mut cursor, 0) }.unwrap();
            }
            prop_assert_eq!(cursor.position(), start);
        }

        #[test]
        fn uninit_slice_write_no_panic_no_ub_check(bytes in any::<Vec<u8>>(), pos in any::<usize>()) {
            let mut output: Vec<u8> = Vec::with_capacity(bytes.len());
            let mut cursor = Cursor::new_at(output.spare_capacity_mut(), pos);
            let res = cursor.write(&bytes);
            if pos > bytes.len() && !bytes.is_empty() {
                prop_assert!(matches!(res, Err(WriteError::WriteSizeLimit(x)) if x == bytes.len()));
            } else if pos == 0 {
                prop_assert_eq!(output, bytes);
            }
        }

        #[test]
        fn vec_write_no_panic_no_ub_check(bytes in any::<Vec<u8>>(), pos in any::<u16>()) {
            let pos = pos as usize;
            let mut output: Vec<u8> = Vec::new();
            let mut cursor = Cursor::new_at(&mut output, pos);
            // Vec impl grows, so it should be valid to write to any position within memory limits.
            cursor.write(&bytes).unwrap();
            prop_assert_eq!(&output[pos..], &bytes);
        }

        #[test]
        fn cursor_write_vec_new(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(Vec::new());
            cursor.write(&bytes).unwrap();
            prop_assert_eq!(&cursor.inner, &bytes);

            let mut vec = Vec::with_capacity(bytes.len());
            let mut cursor = Cursor::new(vec.spare_capacity_mut());
            cursor.write(&bytes).unwrap();
            unsafe { vec.set_len(bytes.len()) };
            prop_assert_eq!(&vec, &bytes);
        }

        #[test]
        fn cursor_write_existing_vec(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(vec![0; bytes.len()]);
            cursor.write(&bytes).unwrap();
            prop_assert_eq!(&cursor.inner, &bytes);
        }

        #[test]
        fn cursor_write_existing_grow_vec(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(vec![0; bytes.len() / 2]);
            cursor.write(&bytes).unwrap();
            prop_assert_eq!(&cursor.inner, &bytes);
        }

        #[test]
        fn cursor_write_partial_vec(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(vec![1; bytes.len()]);
            let half = bytes.len() - bytes.len() / 2;
            cursor.write(&bytes[..half]).unwrap();
            prop_assert_eq!(&cursor.inner[..half], &bytes[..half]);
            // Remaining bytes are untouched
            prop_assert_eq!(&cursor.inner[half..], &vec![1; bytes.len() - half]);
            cursor.write(&bytes[half..]).unwrap();
            prop_assert_eq!(&cursor.inner, &bytes);
        }

        #[test]
        fn cursor_write_trusted_vec(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(vec![1; bytes.len()]);
            let half = bytes.len() - bytes.len() / 2;
            cursor.write(&bytes[..half]).unwrap();
            unsafe { <Cursor<_> as Writer>::as_trusted_for(&mut cursor, bytes.len() - half) }
                .unwrap()
                .write(&bytes[half..])
                .unwrap();
            cursor.finish().unwrap();
            prop_assert_eq!(&cursor.inner, &bytes);
        }

        #[test]
        fn cursor_write_trusted_grow_vec(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(vec![1; bytes.len() / 2]);
            let half = bytes.len() - bytes.len() / 2;
            cursor.write(&bytes[..half]).unwrap();
            unsafe { <Cursor<_> as Writer>::as_trusted_for(&mut cursor, bytes.len() - half) }
                .unwrap()
                .write(&bytes[half..])
                .unwrap();
            cursor.finish().unwrap();
            prop_assert_eq!(&cursor.inner, &bytes);
        }

        #[test]
        fn cursor_write_trusted_oversized_vec(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new(vec![1; bytes.len() * 2]);
            let half = bytes.len() - bytes.len() / 2;
            cursor.write(&bytes[..half]).unwrap();
            unsafe { <Cursor<_> as Writer>::as_trusted_for(&mut cursor, bytes.len() - half) }
                .unwrap()
                .write(&bytes[half..])
                .unwrap();
            cursor.finish().unwrap();
            prop_assert_eq!(&cursor.inner[..bytes.len()], &bytes);
            // Remaining bytes are untouched
            prop_assert_eq!(&cursor.inner[bytes.len()..], &vec![1; bytes.len()]);
        }

        #[cfg(feature = "derive")]
        #[test]
        fn cursor_read_items_with_inner_zero_copy(bytes in proptest::collection::vec(any::<u8>(), 64)) {
            use crate::{config::DefaultConfig, SchemaRead};

            // Test reader not supporting zero-copy, but used to read items that contain nested
            // zero-copy content
            #[derive(crate::SchemaRead)]
            #[wincode(internal)]
            struct NonZeroCopyWrapper {
                zero_copy_content: [u8; 8],
            }

            let mut cursor = Cursor::new(&bytes);
            let mut dst = MaybeUninit::uninit();
            <[NonZeroCopyWrapper; 8] as SchemaRead<DefaultConfig>>::read(&mut cursor, &mut dst)
                .unwrap();
            let deserialized = unsafe { dst.assume_init() };
            for (i, chunk) in bytes.chunks_exact(size_of::<NonZeroCopyWrapper>()).enumerate() {
                prop_assert_eq!(&deserialized[i].zero_copy_content, chunk);
            }
        }
    }

    #[test]
    fn cursor_vec_write_zero_fills_gap() {
        let mut output = vec![1, 2, 3];
        let mut cursor = Cursor::new_at(&mut output, 6);

        cursor.write(&[9, 10]).unwrap();

        assert_eq!(output, vec![1, 2, 3, 0, 0, 0, 9, 10]);
    }

    #[test]
    fn cursor_vec_trusted_write_zero_fills_gap() {
        let mut output = vec![1, 2, 3];
        let mut cursor = Cursor::new_at(&mut output, 6);

        unsafe { <Cursor<_> as Writer>::as_trusted_for(&mut cursor, 2) }
            .unwrap()
            .write(&[9, 10])
            .unwrap();

        assert_eq!(output, vec![1, 2, 3, 0, 0, 0, 9, 10]);
    }

    #[test]
    fn cursor_vec_finish_does_not_extend_len() {
        let mut output = Vec::with_capacity(8);
        let mut cursor = Cursor::new_at(&mut output, 6);

        cursor.finish().unwrap();

        assert_eq!(output.len(), 0);
    }
}
