use super::*;
#[cfg(feature = "alloc")]
use {alloc::vec::Vec, core::slice::from_raw_parts_mut};

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

impl<T> Cursor<T>
where
    T: AsRef<[u8]>,
{
    /// Returns a slice of the remaining bytes in the cursor.
    #[inline]
    fn cur_slice(&self) -> &[u8] {
        let slice = self.inner.as_ref();
        &slice[self.pos.min(slice.len())..]
    }

    /// Returns the number of bytes remaining in the cursor.
    #[inline]
    fn cur_len(&self) -> usize {
        self.inner.as_ref().len().saturating_sub(self.pos)
    }

    /// Split the cursor at `mid` and consume the left slice.
    #[inline]
    fn consume_slice_checked(&mut self, mid: usize) -> ReadResult<&[u8]> {
        let slice = self.inner.as_ref();
        let cur = &slice[self.pos.min(slice.len())..];
        let Some(left) = cur.get(..mid) else {
            return Err(read_size_limit(mid));
        };
        // SAFETY: We just created a slice of `pos..pos + mid` bytes from the cursor, so `pos + mid` is valid.
        self.pos = unsafe { self.pos.unchecked_add(mid) };
        Ok(left)
    }
}

impl<'a, T> Reader<'a> for Cursor<T>
where
    T: AsRef<[u8]>,
{
    type Trusted<'b>
        = TrustedSliceReader<'a, 'b>
    where
        Self: 'b;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        let src = self.cur_slice();
        Ok(&src[..n_bytes.min(src.len())])
    }

    #[inline]
    fn fill_exact(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        let Some(src) = self.cur_slice().get(..n_bytes) else {
            return Err(read_size_limit(n_bytes));
        };
        Ok(src)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        self.pos = unsafe { self.pos.unchecked_add(amt) };
    }

    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if self.cur_len() < amt {
            return Err(read_size_limit(amt));
        }
        // SAFETY: We just checked that `cur_len() >= amt`.
        unsafe { self.consume_unchecked(amt) };
        Ok(())
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        Ok(TrustedSliceReader::new(
            self.consume_slice_checked(n_bytes)?,
        ))
    }
}

/// Helper functions for writing to `Cursor<&mut [MaybeUninit<u8>]>` and `Cursor<&mut MaybeUninit<[u8; N]>>`.
mod uninit_slice {
    use super::*;

    /// Get a mutable slice of the remaining bytes in the cursor.
    #[inline]
    pub(super) fn cur_slice_mut(
        inner: &mut [MaybeUninit<u8>],
        pos: usize,
    ) -> &mut [MaybeUninit<u8>] {
        let len = inner.len();
        &mut inner[pos.min(len)..]
    }

    /// Get a mutable slice of `len` bytes from the cursor at the current position,
    /// returning an error if the slice does not have at least `len` bytes remaining.
    #[inline]
    pub(super) fn get_slice_mut_checked(
        inner: &mut [MaybeUninit<u8>],
        pos: usize,
        len: usize,
    ) -> WriteResult<&mut [MaybeUninit<u8>]> {
        let Some(dst) = cur_slice_mut(inner, pos).get_mut(..len) else {
            return Err(write_size_limit(len));
        };
        Ok(dst)
    }

    /// Write `src` to the cursor at the current position and advance the position by `src.len()`.
    pub(super) fn write(
        inner: &mut [MaybeUninit<u8>],
        pos: &mut usize,
        src: &[u8],
    ) -> WriteResult<()> {
        let len = src.len();
        let dst = get_slice_mut_checked(inner, *pos, len)?;
        // SAFETY: dst is a valid slice of `len` bytes.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), len) };
        // SAFETY: We just wrote `len` bytes to the slice of `pos..pos + len`, so `pos + len` is valid.
        *pos = unsafe { pos.unchecked_add(len) };
        Ok(())
    }

    #[inline]
    pub(super) fn as_trusted_for<'a>(
        inner: &'a mut [MaybeUninit<u8>],
        pos: &mut usize,
        n_bytes: usize,
    ) -> WriteResult<TrustedSliceWriter<'a>> {
        let dst = get_slice_mut_checked(inner, *pos, n_bytes)?;
        // SAFETY: We just created a slice of `pos..pos + n_bytes`, so `pos + n_bytes` is valid.
        *pos = unsafe { pos.unchecked_add(n_bytes) };
        Ok(TrustedSliceWriter::new(dst))
    }
}

impl Writer for Cursor<&mut [MaybeUninit<u8>]> {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        uninit_slice::write(self.inner, &mut self.pos, src)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        uninit_slice::as_trusted_for(self.inner, &mut self.pos, n_bytes)
    }
}

impl<const N: usize> Cursor<&mut MaybeUninit<[u8; N]>> {
    #[inline(always)]
    // `core::mem::transpose` is not yet stabilized.
    pub(super) const fn transpose(inner: &mut MaybeUninit<[u8; N]>) -> &mut [MaybeUninit<u8>; N] {
        // SAFETY: MaybeUninit<[u8; N]> is equivalent to [MaybeUninit<u8>; N].
        unsafe { transmute::<&mut MaybeUninit<[u8; N]>, &mut [MaybeUninit<u8>; N]>(inner) }
    }
}

impl<const N: usize> Writer for Cursor<&mut MaybeUninit<[u8; N]>> {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        uninit_slice::write(Self::transpose(self.inner), &mut self.pos, src)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        uninit_slice::as_trusted_for(Self::transpose(self.inner), &mut self.pos, n_bytes)
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

    /// Advance the position by `n_bytes` and return a [`TrustedSliceWriter`] that can elide bounds
    /// checking within that `n_bytes` window.
    #[inline]
    pub(super) fn as_trusted_for<'a>(
        inner: &'a mut Vec<u8>,
        pos: &'a mut usize,
        n_bytes: usize,
    ) -> WriteResult<TrustedVecWriter<'a>> {
        maybe_grow(inner, *pos, n_bytes)?;
        let buf = unsafe {
            from_raw_parts_mut(
                inner.as_mut_ptr().cast::<MaybeUninit<u8>>(),
                inner.capacity(),
            )
        };
        Ok(TrustedVecWriter::new(buf, pos))
    }

    #[inline]
    pub(super) fn finish(inner: &mut Vec<u8>, pos: usize) {
        if pos > inner.len() {
            unsafe {
                inner.set_len(pos);
            }
        }
    }
}

/// Trusted writer for `Cursor<&mut Vec<u8>>` or `Cursor<Vec<u8>>` that continues
/// overwriting the vector's memory.
///
/// Generally this should not be constructed directly, but rather by calling [`Writer::as_trusted_for`]
/// on a trusted [`Writer`]. This will ensure that the safety invariants are upheld.
///
/// Note that this does *not* update the length of the vector, as it only contains a reference to the
/// vector's memory via `&mut [MaybeUninit<u8>]`, but it will update the _position_ of the cursor.
/// Vec implementations will synchronize the length and position on subsequent writes or when the
/// writer is finished. Benchmarks showed a roughly 2x performance improvement using this method
/// rather than taking a `&mut Vec<u8>` directly.
///
/// # Safety
///
/// - This will _not_ grow the vector, as it assumes the caller has already reserved enough capacity.
///   The `inner` buffer must have sufficient capacity for all writes. It is UB if this is not upheld.
#[cfg(feature = "alloc")]
pub struct TrustedVecWriter<'a> {
    inner: &'a mut [MaybeUninit<u8>],
    pos: &'a mut usize,
}

#[cfg(feature = "alloc")]
impl<'a> TrustedVecWriter<'a> {
    pub fn new(inner: &'a mut [MaybeUninit<u8>], pos: &'a mut usize) -> Self {
        Self { inner, pos }
    }
}

#[cfg(feature = "alloc")]
impl Writer for TrustedVecWriter<'_> {
    type Trusted<'b>
        = TrustedVecWriter<'b>
    where
        Self: 'b;

    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        // SAFETY: Creator of this writer ensures we have sufficient capacity for all writes.
        unsafe {
            ptr::copy_nonoverlapping(
                src.as_ptr().cast(),
                self.inner.as_mut_ptr().add(*self.pos),
                src.len(),
            )
        };

        *self.pos = unsafe { self.pos.unchecked_add(src.len()) };
        Ok(())
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, _n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        Ok(TrustedVecWriter::new(self.inner, self.pos))
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
    type Trusted<'b>
        = TrustedVecWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        vec::write(self.inner, &mut self.pos, src)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        vec::finish(self.inner, self.pos);
        Ok(())
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        vec::as_trusted_for(self.inner, &mut self.pos, n_bytes)
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
    type Trusted<'b>
        = TrustedVecWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        vec::write(&mut self.inner, &mut self.pos, src)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        vec::finish(&mut self.inner, self.pos);
        Ok(())
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        vec::as_trusted_for(&mut self.inner, &mut self.pos, n_bytes)
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
            let buf = cursor.fill_buf(bytes.len()).unwrap();
            if pos > bytes.len() {
                // fill-buf should return an empty slice if the position
                // is greater than the length of the bytes.
                prop_assert_eq!(buf, &[]);
            } else {
                prop_assert_eq!(buf, &bytes[pos..]);
            }

            let res = cursor.fill_exact(bytes.len());
            if pos > bytes.len() && !bytes.is_empty() {
                prop_assert!(matches!(res, Err(ReadError::ReadSizeLimit(x)) if x == bytes.len()));
            } else {
                prop_assert_eq!(res.unwrap(), &bytes[pos.min(bytes.len())..]);
            }
        }

        #[test]
        fn cursor_zero_len_ops_ok(bytes in any::<Vec<u8>>(), pos in any::<usize>()) {
            let mut cursor = Cursor::new_at(&bytes, pos);
            let start = cursor.position();

            // fill_exact(0) is always Ok and does not advance.
            let fe = cursor.fill_exact(0).unwrap();
            prop_assert_eq!(fe.len(), 0);
            prop_assert_eq!(cursor.position(), start);

            // consume(0) is always Ok and does not advance.
            prop_assert!(cursor.consume(0).is_ok());
            prop_assert_eq!(cursor.position(), start);

            // as_trusted_for(0) is always Ok and does not advance.
            let start2 = cursor.position();
            let mut trusted = unsafe { <Cursor<_> as Reader>::as_trusted_for(&mut cursor, 0) }.unwrap();
            // Trusted reader on a 0-window should behave like EOF for >0, but allow zero-length reads.
            prop_assert_eq!(trusted.fill_buf(1).unwrap(), &[]);
            prop_assert_eq!(trusted.fill_exact(0).unwrap().len(), 0);
            prop_assert_eq!(cursor.position(), start2);
        }

        #[test]
        fn cursor_as_trusted_for_remaining_advances_to_len(bytes in any::<Vec<u8>>(), pos in any::<usize>()) {
            // Clamp pos to be within [0, len] so the request is valid.
            let len = bytes.len();
            let pos = if len == 0 { 0 } else { pos % (len + 1) };
            let mut cursor = Cursor::new_at(&bytes, pos);
            let remaining = len.saturating_sub(pos);

            let _trusted = unsafe { <Cursor<_> as Reader>::as_trusted_for(&mut cursor, remaining) }.unwrap();
            // After consuming the exact remaining, position should be exactly len.
            prop_assert_eq!(cursor.position(), len);
        }

        #[test]
        fn cursor_extremal_pos_max_zero_len_ok(bytes in any::<Vec<u8>>()) {
            let mut cursor = Cursor::new_at(&bytes, usize::MAX);
            // With extremal position, fill_buf should be empty and peek should error.
            prop_assert_eq!(cursor.fill_buf(1).unwrap(), &[]);
            prop_assert!(matches!(cursor.peek(), Err(ReadError::ReadSizeLimit(1))));

            // Zero-length ops still succeed and do not advance.
            let start = cursor.position();
            prop_assert!(cursor.fill_exact(0).is_ok());
            prop_assert!(cursor.consume(0).is_ok());
            let _trusted = unsafe { <Cursor<_> as Reader>::as_trusted_for(&mut cursor, 0) }.unwrap();
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
    }
}
