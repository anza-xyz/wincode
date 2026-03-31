use {
    crate::io::{WriteResult, Writer, slice::SliceMutUnchecked, write_size_limit},
    core::mem::MaybeUninit,
    std::io::{BufWriter, Cursor, Write},
};

/// [`Writer`] adapter over any [`std::io::Write`] sink.
///
/// Wraps any `W: std::io::Write` and exposes it as a wincode [`Writer`], allowing
/// serialization into files, network streams, or other I/O sinks.
///
/// # Examples
///
/// Serialize a tuple into a `Vec<u8>` via `WriteAdapter`:
///
/// ```
/// use wincode::{Serialize, io::{Writer, std_write::WriteAdapter}};
///
/// let tuple = (42u32, true, 1234567890i64);
/// let mut buf = Vec::new();
/// let mut writer = WriteAdapter::new(&mut buf);
/// <(u32, bool, i64)>::serialize_into(&mut writer, &tuple).unwrap();
/// writer.finish().unwrap();
/// assert_eq!(buf, wincode::serialize(&tuple).unwrap());
/// ```
#[derive(Debug)]
pub struct WriteAdapter<W: ?Sized>(W);

impl<W: Write> WriteAdapter<W> {
    pub fn new(writer: W) -> Self {
        Self(writer)
    }
}

impl<W: Write + ?Sized> Writer for WriteAdapter<W> {
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.0.write_all(src)?)
    }

    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.0.flush()?)
    }
}

impl<W: Write + ?Sized> Writer for BufWriter<W> {
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.write_all(src)?)
    }

    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.flush()?)
    }
}

#[inline]
fn cursor_slice_as_trusted_for(
    cursor: &mut Cursor<impl AsMut<[u8]>>,
    n_bytes: usize,
) -> WriteResult<impl Writer> {
    let Ok(pos) = usize::try_from(cursor.position()) else {
        return Err(write_size_limit(usize::MAX));
    };

    let inner = cursor.get_mut().as_mut();
    let next_pos = pos.saturating_add(n_bytes);
    if next_pos > inner.len() {
        return Err(write_size_limit(n_bytes));
    }

    cursor.set_position(next_pos as u64);
    let slice = &mut cursor.get_mut().as_mut()[pos..next_pos];
    // SAFETY: by calling `as_trusted_for`, caller guarantees they
    // will fully initialize `n_bytes` of memory and will not write
    // beyond the bounds of the slice.
    Ok(unsafe { SliceMutUnchecked::new(slice) })
}

impl Writer for Cursor<&mut [u8]> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.write_all(src)?)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.flush()?)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        cursor_slice_as_trusted_for(self, n_bytes)
    }
}

impl<const N: usize> Writer for Cursor<[u8; N]> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.write_all(src)?)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.flush()?)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        cursor_slice_as_trusted_for(self, n_bytes)
    }
}

impl Writer for Cursor<Box<[u8]>> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.write_all(src)?)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.flush()?)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        cursor_slice_as_trusted_for(self, n_bytes)
    }
}

#[inline]
fn cursor_vec_as_trusted_for(
    cursor: &mut Cursor<impl AsMut<Vec<u8>>>,
    n_bytes: usize,
) -> WriteResult<impl Writer> {
    let Ok(pos) = usize::try_from(cursor.position()) else {
        return Err(write_size_limit(usize::MAX));
    };
    let Some(next_pos) = pos.checked_add(n_bytes) else {
        return Err(write_size_limit(n_bytes));
    };

    let vec = cursor.get_mut().as_mut();
    let cur_len = vec.len();
    // Ensure total capacity is at least `next_pos`, so the reserved
    // trusted window `[pos..next_pos)` is backed by the vector.
    if next_pos > vec.capacity() {
        #[expect(clippy::arithmetic_side_effects)]
        // `next_pos > capacity && cur_len <= capacity` by invariant
        vec.reserve(next_pos - cur_len);
    }

    // Zero-fill the gap between `cur_len` and `pos` (if any).
    //
    // Behaviorally consistent with `std::io::Write::write_all` for
    // `Cursor<Vec<u8>>`.
    if let Some(init_gap) = pos.checked_sub(cur_len) {
        let spare = vec.spare_capacity_mut();
        debug_assert!(spare.len() >= init_gap);
        // SAFETY: after the optional reserve above, `capacity >= next_pos`.
        // When `init_gap` exists, `init_gap = pos - cur_len` and `pos <= next_pos`,
        // so `init_gap <= capacity - cur_len == spare.len()`.
        unsafe {
            spare
                .get_unchecked_mut(..init_gap)
                .fill(MaybeUninit::new(0))
        }
    }

    if next_pos > cur_len {
        // SAFETY:
        // - The contract of `as_trusted_for` requires that the caller initialize the
        //   entire reserved window `[pos..next_pos)` before using the parent writer again.
        // - The buffer contains only bytes (Vec<u8>), so there is no drop implementation
        //   that must be considered.
        unsafe { vec.set_len(next_pos) }
    }
    cursor.set_position(next_pos as u64);

    // SAFETY: `vec.reserve` above ensures that at least `pos + n_bytes`
    // (`next_pos`) capacity is available.
    let slice = unsafe {
        core::slice::from_raw_parts_mut(
            cursor
                .get_mut()
                .as_mut()
                .as_mut_ptr()
                .cast::<MaybeUninit<u8>>()
                .add(pos),
            n_bytes,
        )
    };
    // SAFETY: by calling `as_trusted_for`, caller guarantees they
    // will fully initialize `n_bytes` of memory and will not write
    // beyond the bounds of the slice.
    Ok(unsafe { SliceMutUnchecked::new(slice) })
}

impl Writer for Cursor<Vec<u8>> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.write_all(src)?)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.flush()?)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        cursor_vec_as_trusted_for(self, n_bytes)
    }
}

impl Writer for Cursor<&mut Vec<u8>> {
    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        Ok(self.write_all(src)?)
    }

    #[inline]
    fn finish(&mut self) -> WriteResult<()> {
        Ok(self.flush()?)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<impl Writer> {
        cursor_vec_as_trusted_for(self, n_bytes)
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{
            io::WriteError,
            serde::{Serialize, serialize, serialized_size},
        },
    };

    const MAGIC: u64 = 0xdeadbeef_cafebabe;
    const DATA: &[(u32, bool, &u64)] = &[
        (1u32, false, &MAGIC),
        (2u32, true, &MAGIC),
        (3u32, false, &MAGIC),
    ];

    fn assert_serializes_data(mut writer: impl Writer) {
        <[(u32, bool, &u64)]>::serialize_into(writer.by_ref(), DATA).unwrap();
        writer.finish().unwrap();
    }

    #[test]
    fn write_adapter_serialize_tuples() {
        let mut buf = Vec::new();
        assert_serializes_data(WriteAdapter::new(&mut buf));
        assert_eq!(buf, serialize(DATA).unwrap());
    }

    #[test]
    fn buf_writer_serialize_tuples() {
        let mut buf = Vec::new();
        assert_serializes_data(BufWriter::new(&mut buf));
        assert_eq!(buf, serialize(DATA).unwrap());
    }

    #[test]
    fn cursor_vec_writer_serialize_tuples() {
        let mut buf = Cursor::new(Vec::new());
        assert_serializes_data(&mut buf);
        assert_eq!(buf.into_inner(), serialize(DATA).unwrap());
    }

    #[test]
    fn cursor_slice_writer_serialize_tuples() {
        let size = serialized_size(DATA).unwrap() as usize;
        let mut buf = Cursor::new(vec![0; size].into_boxed_slice());
        assert_serializes_data(&mut buf);
        assert_eq!(buf.into_inner().as_ref(), serialize(DATA).unwrap());
    }

    fn write_trusted(writer: &mut impl Writer, bytes: &[u8]) {
        let mut trusted = unsafe { writer.as_trusted_for(bytes.len()) }.unwrap();
        trusted.write(bytes).unwrap();
        trusted.finish().unwrap();
    }

    macro_rules! with_vec_cursors {
        ($inner:expr, |$reader: ident| $body: block) => {{
            {
                let mut $reader = Cursor::new($inner.clone());
                $body
            }
            {
                let mut $reader = Cursor::new(&mut $inner);
                $body
            }
        }};
    }

    #[test]
    fn cursor_vec_trusted_append_with_spare_capacity() {
        let mut inner = Vec::with_capacity(8);
        with_vec_cursors!(inner, |cursor| {
            cursor.write_all(&[1, 2, 3]).unwrap();

            write_trusted(&mut cursor, &[4, 5]);
            cursor.finish().unwrap();

            assert_eq!(&*cursor.into_inner(), &vec![1, 2, 3, 4, 5]);
        });
    }

    #[test]
    fn cursor_vec_trusted_overwrite_then_extend() {
        let mut inner = vec![1, 2, 3, 4];
        with_vec_cursors!(inner, |cursor| {
            cursor.set_position(2);

            write_trusted(&mut cursor, &[9, 8, 7, 6]);
            cursor.finish().unwrap();

            assert_eq!(&cursor.into_inner()[..], &vec![1, 2, 9, 8, 7, 6]);
        });
    }

    #[test]
    fn cursor_vec_trusted_overwrite_preserves_tail() {
        let mut inner = vec![1, 2, 3, 4, 5, 6];
        with_vec_cursors!(inner, |cursor| {
            cursor.set_position(2);

            write_trusted(&mut cursor, &[9, 8]);
            cursor.finish().unwrap();

            assert_eq!(&cursor.into_inner()[..], &vec![1, 2, 9, 8, 5, 6]);
        });
    }

    #[test]
    fn cursor_vec_trusted_zero_fills_gap() {
        let mut inner = Vec::with_capacity(16);
        inner.extend_from_slice(&[1, 2, 3]);
        with_vec_cursors!(inner, |cursor| {
            cursor.set_position(6);

            write_trusted(&mut cursor, &[9, 10]);
            cursor.finish().unwrap();

            assert_eq!(&cursor.into_inner()[..], &vec![1, 2, 3, 0, 0, 0, 9, 10]);
        });
    }

    macro_rules! with_slice_cursors {
        ($inner:expr, |$reader: ident| $body: block) => {{
            {
                let mut $reader = Cursor::new($inner);
                $body
            }
            {
                let mut inner = $inner;
                let mut $reader = Cursor::new(&mut inner[..]);
                $body
            }
            {
                let mut $reader = Cursor::new(Box::from($inner));
                $body
            }
        }};
    }

    #[test]
    fn cursor_mut_slice_trusted_writes_in_bounds() {
        with_slice_cursors!([1, 2, 3, 4, 5], |cursor| {
            let pos = {
                cursor.set_position(1);

                write_trusted(&mut cursor, &[9, 8, 7]);
                cursor.finish().unwrap();
                cursor.position()
            };
            assert_eq!(&cursor.get_ref()[..], &[1, 9, 8, 7, 5]);
            assert_eq!(pos, 4);
        });
    }

    #[test]
    fn cursor_slice_trusted_out_of_bounds_errors() {
        with_slice_cursors!([1, 2, 3], |cursor| {
            cursor.set_position(2);
            let result = unsafe { cursor.as_trusted_for(2) };
            assert!(matches!(result, Err(WriteError::WriteSizeLimit(2))));
        });
    }
}
