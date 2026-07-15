use {
    crate::io::{BorrowKind, ReadResult, Reader, read_size_limit, slice::SliceScopedUnchecked},
    core::{mem::MaybeUninit, ptr::copy_nonoverlapping},
    std::io::{self, BufReader, Cursor, Read},
};

/// [`Reader`] adapter over any [`std::io::Read`] source.
///
/// Wraps any `R: std::io::Read` and exposes it as a wincode [`Reader`], allowing
/// deserialization from files, network streams, or other I/O sources.
///
/// # Examples
///
/// Deserialize a tuple via [`ReadAdapter`]:
///
/// ```
/// use wincode::io::std_read::ReadAdapter;
///
/// let tuple = (42u32, true, 1234567890i64);
/// let buf = wincode::serialize(&tuple).unwrap();
/// let reader = ReadAdapter::new(&buf[..]);
/// let out: (u32, bool, i64) = wincode::deserialize_from(reader).unwrap();
/// assert_eq!(out, tuple);
/// ```
pub struct ReadAdapter<R: ?Sized>(R);

impl<R: Read> ReadAdapter<R> {
    pub fn new(inner: R) -> Self {
        Self(inner)
    }
}

#[inline]
fn copy_into_slice<R: Read + ?Sized>(reader: &mut R, dst: &mut [u8]) -> ReadResult<()> {
    #[cold]
    fn maybe_eof_to_read_size_limit(err: io::Error, len: usize) -> ReadResult<()> {
        if err.kind() == io::ErrorKind::UnexpectedEof {
            Err(read_size_limit(len))
        } else {
            Err(err.into())
        }
    }
    if let Err(e) = reader.read_exact(dst) {
        return maybe_eof_to_read_size_limit(e, dst.len());
    };
    Ok(())
}

unsafe impl<R: Read + ?Sized> Reader<'_> for ReadAdapter<R> {
    #[inline(always)]
    fn copy_into_slice(&mut self, dst: &mut [u8]) -> ReadResult<()> {
        copy_into_slice(&mut self.0, dst)
    }
}

unsafe impl<R: Read + ?Sized> Reader<'_> for BufReader<R> {
    #[inline(always)]
    fn copy_into_slice(&mut self, dst: &mut [u8]) -> ReadResult<()> {
        copy_into_slice(self, dst)
    }
}

#[inline]
fn cursor_advance(cursor: &mut Cursor<impl AsRef<[u8]>>, n: usize) -> ReadResult<&[u8]> {
    let Ok(pos) = usize::try_from(cursor.position()) else {
        return Err(read_size_limit(usize::MAX));
    };

    let inner = cursor.get_ref().as_ref();
    let next_pos = pos.saturating_add(n);
    if next_pos > inner.len() {
        return Err(read_size_limit(n));
    }

    cursor.set_position(next_pos as u64);
    let inner = cursor.get_ref().as_ref();
    Ok(&inner[pos..next_pos])
}

unsafe impl<'a, T> Reader<'a> for Cursor<T>
where
    T: AsRef<[u8]>,
{
    const BORROW_KINDS: u8 = BorrowKind::CallSite.mask();

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [u8]) -> ReadResult<()> {
        let src = cursor_advance(self, dst.len())?;
        // SAFETY:
        // - `cursor_advance` guarantees that `src` is exactly `dst.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `dst` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), dst.len()) };
        Ok(())
    }

    #[inline]
    fn copy_into_uninit_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = cursor_advance(self, dst.len())?;
        // SAFETY:
        // - `cursor_advance` guarantees that `src` is exactly `dst.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `dst` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), dst.len()) };
        Ok(())
    }

    #[inline(always)]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        let src = cursor_advance(self, N)?;
        // SAFETY:
        // - `cursor_advance` guarantees that `src` is exactly `dst.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `dst` does not overlap
        //   with the internal buffer.
        Ok(unsafe { *(src.as_ptr().cast::<[u8; N]>()) })
    }

    #[inline]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        cursor_advance(self, len)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'a>> {
        let buf = cursor_advance(self, n_bytes)?;
        // SAFETY: by calling `as_trusted_for`, caller guarantees they
        // will will not read beyond the bounds of the slice, `n_bytes`.
        Ok(unsafe { SliceScopedUnchecked::new(buf) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A safe `Read` implementation that inspects the destination before writing.
    ///
    /// This catches adapters passing uninitialized storage to `Read::read`: inspecting
    /// such storage would trigger undefined behavior under Miri.
    struct InspectingReader {
        data: Vec<u8>,
        pos: usize,
        observed: Vec<u8>,
    }

    impl InspectingReader {
        fn new(data: Vec<u8>) -> Self {
            Self {
                data,
                pos: 0,
                observed: Vec::new(),
            }
        }
    }

    impl Read for InspectingReader {
        fn read(&mut self, dst: &mut [u8]) -> io::Result<usize> {
            self.observed.extend_from_slice(dst);

            let remaining = &self.data[self.pos..];
            let len = dst.len().min(remaining.len());
            dst[..len].copy_from_slice(&remaining[..len]);
            self.pos = self.pos.checked_add(len).unwrap();
            Ok(len)
        }
    }

    #[test]
    fn read_adapter_initializes_destination_before_reading() {
        let expected = 0x0123_4567_89ab_cdef_u64;
        let data = crate::serialize(&expected).unwrap();
        let mut reader = InspectingReader::new(data.clone());

        let actual: u64 = crate::deserialize_from(ReadAdapter::new(&mut reader)).unwrap();

        assert_eq!(actual, expected);
        assert_eq!(reader.observed, vec![0; data.len()]);
    }

    #[test]
    fn buf_reader_initializes_destination_before_reading() {
        let expected = 0x0123_4567_89ab_cdef_u64;
        let data = crate::serialize(&expected).unwrap();
        let mut reader = InspectingReader::new(data.clone());

        let actual: u64 =
            crate::deserialize_from(BufReader::with_capacity(1, &mut reader)).unwrap();

        assert_eq!(actual, expected);
        assert_eq!(reader.observed, vec![0; data.len()]);
    }
}
