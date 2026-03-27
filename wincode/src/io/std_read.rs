use {
    crate::io::{BorrowKind, ReadResult, Reader, read_size_limit, slice::SliceScopedUnchecked},
    core::{
        mem::{MaybeUninit, transmute},
        ptr::copy_nonoverlapping,
    },
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
fn copy_into_slice<R: Read + ?Sized>(
    reader: &mut R,
    dst: &mut [MaybeUninit<u8>],
) -> ReadResult<()> {
    #[cold]
    fn maybe_eof_to_read_size_limit(err: io::Error, len: usize) -> ReadResult<()> {
        if err.kind() == io::ErrorKind::UnexpectedEof {
            Err(read_size_limit(len))
        } else {
            Err(err.into())
        }
    }

    // SAFETY: `read_exact` only writes to the buffer.
    let buf = unsafe { transmute::<&mut [MaybeUninit<u8>], &mut [u8]>(dst) };
    if let Err(e) = reader.read_exact(buf) {
        return maybe_eof_to_read_size_limit(e, buf.len());
    };
    Ok(())
}

impl<R: Read + ?Sized> Reader<'_> for ReadAdapter<R> {
    #[inline(always)]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        copy_into_slice(&mut self.0, dst)
    }
}

impl<R: Read + ?Sized> Reader<'_> for BufReader<R> {
    #[inline(always)]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
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

impl<'a, T> Reader<'a> for Cursor<T>
where
    T: AsRef<[u8]>,
{
    const BORROW_KINDS: u8 = BorrowKind::CallSite.mask();

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        let src = cursor_advance(self, dst.len())?;
        // SAFETY:
        // - `cursor_advance` guarantees that `src` is exactly `dst.len()` bytes.
        // - Given Rust's aliasing rules, we can assume that `dst` does not overlap
        //   with the internal buffer.
        unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) };
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
