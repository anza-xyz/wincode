use {
    crate::{
        error::read_length_encoding_overflow,
        io::{ReadResult, Reader, read_size_limit},
    },
    core::mem::MaybeUninit,
};

/// A [`Reader`] that limits the number of bytes reserved for reads from an inner [`Reader`].
///
/// Each operation reserves its full requested size before delegating to the inner reader. The
/// reservation is retained if the inner operation fails, because a [`Reader`] may consume some
/// bytes before returning an error without reporting how many it consumed. Trusted reader windows
/// reserve their entire window when they are created.
///
/// When a request exceeds the remaining limit,
/// [`ReadError::ReadSizeLimit`](crate::io::ReadError::ReadSizeLimit) contains the number of bytes by
/// which the request exceeds the available limit.
///
/// To limit an entire deserialization operation, construct one `LimitReader` at the outermost
/// boundary and pass or reborrow that same reader throughout the operation. Constructing fresh
/// `LimitReader`s inside nested [`SchemaRead`](crate::SchemaRead) implementations creates
/// independent limits and does not enforce one cumulative limit across the parent operation. A
/// nested wrapper is appropriate only when intentionally applying a separate limit to a particular
/// field or subtree.
///
/// # Examples
///
/// ```
/// # use wincode::io::LimitReader;
/// # use wincode::io::ReadError;
/// #
/// let mut bytes = [0u8; 8];
/// wincode::serialize_into(&mut bytes[..], &42u64);
/// let reader = LimitReader::new(&bytes[..], 4);
/// assert!(
///     matches!(wincode::deserialize_from::<u64>(reader),
///     Err(wincode::ReadError::Io(ReadError::ReadSizeLimit(4))))
/// );
/// ```
pub struct LimitReader<R> {
    inner: R,
    remaining: usize,
}

impl<R> LimitReader<R> {
    /// Wrap an inner reader with the given cumulative byte limit.
    ///
    /// For an operation-wide limit, call this once at the outermost deserialization boundary and
    /// reborrow the resulting reader with [`Reader::by_ref`] when necessary.
    pub const fn new(inner: R, limit: usize) -> Self {
        Self {
            inner,
            remaining: limit,
        }
    }

    #[inline]
    const fn reserve_limit(&mut self, needed: usize) -> ReadResult<()> {
        if needed > self.remaining {
            #[expect(clippy::arithmetic_side_effects)]
            return Err(read_size_limit(needed - self.remaining));
        }

        #[expect(clippy::arithmetic_side_effects)]
        {
            self.remaining -= needed;
        }

        Ok(())
    }
}

unsafe impl<'de, R: Reader<'de>> Reader<'de> for LimitReader<R> {
    const BORROW_KINDS: u8 = R::BORROW_KINDS;

    #[inline]
    fn take_array<const N: usize>(&mut self) -> ReadResult<[u8; N]> {
        self.reserve_limit(N)?;
        self.inner.take_array()
    }

    #[inline]
    fn take_byte(&mut self) -> ReadResult<u8> {
        self.reserve_limit(1)?;
        self.inner.take_byte()
    }

    #[inline]
    fn take_borrowed(&mut self, len: usize) -> ReadResult<&'de [u8]> {
        self.reserve_limit(len)?;
        self.inner.take_borrowed(len)
    }

    #[inline]
    fn take_borrowed_mut(&mut self, len: usize) -> ReadResult<&'de mut [u8]> {
        self.reserve_limit(len)?;
        self.inner.take_borrowed_mut(len)
    }

    #[inline]
    fn take_scoped(&mut self, len: usize) -> ReadResult<&[u8]> {
        self.reserve_limit(len)?;
        self.inner.take_scoped(len)
    }

    #[inline]
    unsafe fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<impl Reader<'de>> {
        self.reserve_limit(n_bytes)?;
        unsafe { self.inner.as_trusted_for(n_bytes) }
    }

    #[inline]
    unsafe fn as_trusted_for_seq(
        &mut self,
        len: usize,
        size: usize,
    ) -> Result<impl Reader<'de>, crate::error::ReadError> {
        let Some(window) = len.checked_mul(size) else {
            return Err(read_length_encoding_overflow("usize::MAX"));
        };
        self.reserve_limit(window)?;
        unsafe { self.inner.as_trusted_for_seq(len, size) }
    }

    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [u8]) -> ReadResult<()> {
        self.reserve_limit(dst.len())?;
        self.inner.copy_into_slice(dst)
    }

    #[inline]
    fn copy_into_uninit_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        self.reserve_limit(dst.len())?;
        self.inner.copy_into_uninit_slice(dst)
    }

    #[inline]
    unsafe fn copy_into_t<T>(&mut self, dst: &mut MaybeUninit<T>) -> ReadResult<()> {
        self.reserve_limit(size_of::<T>())?;
        unsafe { self.inner.copy_into_t(dst) }
    }

    #[inline]
    unsafe fn copy_into_slice_t<T>(&mut self, dst: &mut [MaybeUninit<T>]) -> ReadResult<()> {
        self.reserve_limit(size_of_val(dst))?;
        unsafe { self.inner.copy_into_slice_t(dst) }
    }
}

#[cfg(test)]
mod tests {
    use {super::*, crate::io::ReadError};

    #[test]
    fn cumulative_reads_respect_limit() {
        let bytes = [1, 2, 3, 4, 5];
        let mut reader = LimitReader::new(bytes.as_slice(), 4);

        assert_eq!(reader.take_array::<2>().unwrap(), [1, 2]);
        assert_eq!(reader.take_byte().unwrap(), 3);
        assert_eq!(reader.take_byte().unwrap(), 4);
        assert!(matches!(
            reader.take_byte(),
            Err(ReadError::ReadSizeLimit(1))
        ));
    }

    #[test]
    fn exact_limit_succeeds() {
        let bytes = [1, 2, 3, 4];
        let mut reader = LimitReader::new(bytes.as_slice(), bytes.len());

        assert_eq!(reader.take_array::<4>().unwrap(), bytes);
    }

    #[test]
    fn error_reports_shortfall() {
        let bytes = [0; 8];
        let mut reader = LimitReader::new(bytes.as_slice(), 3);

        assert!(matches!(
            reader.take_array::<8>(),
            Err(ReadError::ReadSizeLimit(5))
        ));
    }

    #[test]
    fn trusted_window_reserves_entire_window() {
        let bytes = [1, 2, 3, 4, 5];
        let mut reader = LimitReader::new(bytes.as_slice(), 4);

        {
            let mut trusted = unsafe { reader.as_trusted_for(3) }.unwrap();
            assert_eq!(trusted.take_byte().unwrap(), 1);
        }

        assert!(matches!(
            reader.take_array::<2>(),
            Err(ReadError::ReadSizeLimit(1))
        ));
    }
}
