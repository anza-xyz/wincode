use {
    crate::io::{ReadResult, Reader, read_size_limit},
    core::mem::{MaybeUninit, transmute},
    std::io::{self, BufReader, Read},
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
