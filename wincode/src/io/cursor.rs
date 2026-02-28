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
    #[inline]
    #[expect(clippy::arithmetic_side_effects)]
    fn read(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<usize> {
        let buf = self.inner.as_ref();

        let src = &buf[self.pos.min(buf.len())..];
        let len = dst.len().min(src.len());

        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), len) }
        self.pos += len;
        Ok(len)
    }

    #[inline(always)]
    unsafe fn read_hint(&mut self, hint: impl Hint) -> ReadResult<impl Reader<'a>> {
        let size = hint.size();
        let window = self.advance_slice_checked(size)?;
        Ok(unsafe { SliceScopedUnchecked::new(window) })
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = self.advance_slice_checked(dst.len())?;
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) }
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let src = self.advance_slice_checked(N)?;
        Ok(unsafe { *(src.as_ptr().cast::<[u8; N]>()) })
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
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        let size = hint.size();
        let window = self.advance_slice_mut_checked(size)?;
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.advance_slice_mut_checked(src.len())?;
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }

        Ok(())
    }
}

impl Writer for Cursor<&mut [u8]> {
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        let size = hint.size();
        let window = self.advance_slice_mut_checked(size)?;
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.advance_slice_mut_checked(src.len())?;
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }

        Ok(())
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
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        let size = hint.size();
        let window = self.advance_slice_mut_checked(size)?;
        Ok(unsafe { SliceMutUnchecked::new(window) })
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = self.advance_slice_mut_checked(src.len())?;
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) }

        Ok(())
    }
}

/// Helper functions for writing to `Cursor<&mut Vec<u8>>` and `Cursor<Vec<u8>>`.
#[cfg(feature = "alloc")]
mod vec {
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
    pub(super) fn maybe_grow(inner: &mut Vec<u8>, pos: usize, needed: usize) -> WriteResult<()> {
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

    /// Add `len` to the cursor's position and update the length of the vector if necessary.
    ///
    /// # SAFETY:
    /// - Must be called after a successful write to the vector.
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
        maybe_grow(inner, *pos, src.len())?;
        // SAFETY: We just ensured at least `pos + src.len()` capacity is available.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), inner.as_mut_ptr().add(*pos), src.len()) };
        // SAFETY: We just wrote `src.len()` bytes to the vector.
        unsafe { add_len(inner, pos, src.len()) };
        Ok(())
    }

    #[inline]
    pub(super) fn finish(inner: &mut Vec<u8>, pos: usize) {
        if pos > inner.len() {
            unsafe {
                inner.set_len(pos);
            }
        }
    }

    #[inline(always)]
    #[expect(clippy::arithmetic_side_effects)]
    pub(super) unsafe fn write_hint<'a>(
        inner: &'a mut Vec<u8>,
        pos: &'a mut usize,
        hint: impl Hint,
    ) -> WriteResult<impl Writer> {
        let size = hint.size();
        maybe_grow(inner, *pos, size)?;
        let buf = unsafe {
            from_raw_parts_mut(inner.as_mut_ptr().add(*pos).cast::<MaybeUninit<u8>>(), size)
        };

        *pos += size;
        Ok(unsafe { SliceMutUnchecked::new(buf) })
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
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        vec::write_hint(self.inner, &mut self.pos, hint)
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        vec::write(self.inner, &mut self.pos, src)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        vec::finish(self.inner, self.pos);
        Ok(())
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
    #[inline(always)]
    unsafe fn write_hint(&mut self, hint: impl Hint) -> WriteResult<impl Writer> {
        vec::write_hint(&mut self.inner, &mut self.pos, hint)
    }

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        vec::write(&mut self.inner, &mut self.pos, src)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        vec::finish(&mut self.inner, self.pos);
        Ok(())
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

            unsafe { <Cursor<_> as Reader>::read_hint(&mut cursor, 0) }.unwrap();
            prop_assert_eq!(cursor.position(), start);
        }

        #[test]
        fn cursor_extremal_pos_max_zero_len_ok(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new_at(&bytes, usize::MAX);

            // Zero-length ops still succeed and do not advance.
            let mut buf: [MaybeUninit::<u8>; 0] = [];
            let start = cursor.position();
            prop_assert!(cursor.copy_into_slice(&mut buf).is_ok());
            {
                let _trusted = unsafe { <Cursor<_> as Reader>::read_hint(&mut cursor, 0) }.unwrap();
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
            unsafe { <Cursor<_> as Writer>::write_hint(&mut cursor, bytes.len() - half) }
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
            unsafe { <Cursor<_> as Writer>::write_hint(&mut cursor, bytes.len() - half) }
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
            unsafe { <Cursor<_> as Writer>::write_hint(&mut cursor, bytes.len() - half) }
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
}
