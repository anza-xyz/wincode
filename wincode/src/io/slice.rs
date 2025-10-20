use {super::*, core::marker::PhantomData};

/// Helpers for trusted slice operations.
pub(crate) mod trusted_slice {
    use super::*;

    #[inline]
    pub(super) fn fill_buf(bytes: &[u8], n_bytes: usize) -> &[u8] {
        unsafe { bytes.get_unchecked(..n_bytes.min(bytes.len())) }
    }

    #[inline]
    pub(super) fn fill_exact(bytes: &[u8], n_bytes: usize) -> &[u8] {
        unsafe { bytes.get_unchecked(..n_bytes) }
    }

    #[inline]
    pub(super) unsafe fn consume_unchecked(bytes: &mut &[u8], amt: usize) {
        *bytes = unsafe { bytes.get_unchecked(amt..) };
    }

    #[inline]
    pub(super) fn consume(bytes: &mut &[u8], amt: usize) {
        unsafe { consume_unchecked(bytes, amt) };
    }

    /// Get a slice of `len` bytes for writing, advancing the writer by `len` bytes.
    #[inline]
    pub(super) fn get_slice_mut<'a>(
        buffer: &mut &'a mut [MaybeUninit<u8>],
        len: usize,
    ) -> &'a mut [MaybeUninit<u8>] {
        let (dst, rest) = unsafe { mem::take(buffer).split_at_mut_unchecked(len) };
        *buffer = rest;
        dst
    }
}

/// In-memory [`Reader`] that does not perform bounds checking, with zero-copy support.
///
/// Methods will panic if reads go out of bounds, so ensure that
/// the chain of [`SchemaRead`](crate::SchemaRead) implementations that
/// follow have statically known read requirements.
pub struct TrustedSliceReaderZeroCopy<'a> {
    cursor: &'a [u8],
}

impl<'a> TrustedSliceReaderZeroCopy<'a> {
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self { cursor: bytes }
    }
}

impl<'a> Reader<'a> for TrustedSliceReaderZeroCopy<'a> {
    type Trusted<'b>
        = Self
    where
        Self: 'b;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        Ok(trusted_slice::fill_buf(self.cursor, n_bytes))
    }

    #[inline]
    fn fill_exact(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        Ok(trusted_slice::fill_exact(self.cursor, n_bytes))
    }

    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let (src, rest) = unsafe { self.cursor.split_at_unchecked(len) };
        self.cursor = rest;
        Ok(src)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        trusted_slice::consume_unchecked(&mut self.cursor, amt);
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        trusted_slice::consume(&mut self.cursor, amt);
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        Ok(TrustedSliceReaderZeroCopy::new(self.borrow_exact(n_bytes)?))
    }
}

/// In-memory [`Reader`] that does not perform bounds checking.
///
/// Use [`TrustedSliceReaderZeroCopy`] for zero-copy support.
///
/// Methods will panic if reads go out of bounds, so ensure that
/// the chain of [`SchemaRead`](crate::SchemaRead) implementations that
/// follow have statically known read requirements.
pub struct TrustedSliceReader<'a, 'b> {
    cursor: &'b [u8],
    _marker: PhantomData<&'a ()>,
}

impl<'a, 'b> TrustedSliceReader<'a, 'b> {
    pub const fn new(bytes: &'b [u8]) -> Self {
        Self {
            cursor: bytes,
            _marker: PhantomData,
        }
    }
}

impl<'a, 'b> Reader<'a> for TrustedSliceReader<'a, 'b> {
    type Trusted<'c>
        = Self
    where
        Self: 'c;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        Ok(trusted_slice::fill_buf(self.cursor, n_bytes))
    }

    #[inline]
    fn fill_exact(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        Ok(trusted_slice::fill_exact(self.cursor, n_bytes))
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        trusted_slice::consume_unchecked(&mut self.cursor, amt);
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        trusted_slice::consume(&mut self.cursor, amt);
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> ReadResult<Self::Trusted<'_>> {
        let (src, rest) = unsafe { self.cursor.split_at_unchecked(n_bytes) };
        self.cursor = rest;
        Ok(TrustedSliceReader::new(src))
    }
}

impl<'a> Reader<'a> for &'a [u8] {
    type Trusted<'b>
        = TrustedSliceReaderZeroCopy<'a>
    where
        Self: 'b;

    #[inline]
    fn fill_buf(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        // SAFETY: we clamp the end bound to the length of the slice.
        Ok(unsafe { self.get_unchecked(..n_bytes.min(self.len())) })
    }

    fn fill_exact(&mut self, n_bytes: usize) -> ReadResult<&[u8]> {
        let Some(src) = self.get(..n_bytes) else {
            return Err(read_size_limit(n_bytes));
        };
        Ok(src)
    }

    #[inline]
    fn borrow_exact(&mut self, len: usize) -> ReadResult<&'a [u8]> {
        let Some((src, rest)) = self.split_at_checked(len) else {
            return Err(read_size_limit(len));
        };
        *self = rest;
        Ok(src)
    }

    #[inline]
    unsafe fn consume_unchecked(&mut self, amt: usize) {
        *self = unsafe { self.get_unchecked(amt..) };
    }

    #[inline]
    fn consume(&mut self, amt: usize) -> ReadResult<()> {
        if self.len() < amt {
            return Err(read_size_limit(amt));
        }
        // SAFETY: we just checked that self.len() >= amt.
        unsafe { self.consume_unchecked(amt) };
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n: usize) -> ReadResult<Self::Trusted<'_>> {
        Ok(TrustedSliceReaderZeroCopy::new(self.borrow_exact(n)?))
    }
}

/// In-memory [`Writer`] that does not perform bounds checking.
///
/// Methods will panic if writes go out of bounds, so ensure that
/// the chain of [`SchemaWrite`](crate::SchemaWrite) implementations that
/// follow have statically known size requirements.
pub struct TrustedSliceWriter<'a> {
    buffer: &'a mut [MaybeUninit<u8>],
}

#[cfg(test)]
impl core::ops::Deref for TrustedSliceWriter<'_> {
    type Target = [MaybeUninit<u8>];

    fn deref(&self) -> &Self::Target {
        self.buffer
    }
}

impl<'a> TrustedSliceWriter<'a> {
    #[inline(always)]
    pub const fn new(buffer: &'a mut [MaybeUninit<u8>]) -> Self {
        Self { buffer }
    }
}

impl<'a> Writer for TrustedSliceWriter<'a> {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = trusted_slice::get_slice_mut(&mut self.buffer, src.len());
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) };
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        Ok(TrustedSliceWriter::new(trusted_slice::get_slice_mut(
            &mut self.buffer,
            n_bytes,
        )))
    }
}

/// Get a slice of `len` bytes for writing, advancing the writer by `len` bytes, or
/// returning an error if the input slice does not have at least `len` bytes remaining.
#[inline]
fn get_slice_mut_checked<'a, T>(input: &mut &'a mut [T], len: usize) -> WriteResult<&'a mut [T]> {
    let Some((dst, rest)) = mem::take(input).split_at_mut_checked(len) else {
        return Err(write_size_limit(len));
    };
    *input = rest;
    Ok(dst)
}

impl Writer for &mut [MaybeUninit<u8>] {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = get_slice_mut_checked(self, src.len())?;
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), src.len()) };
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        Ok(TrustedSliceWriter::new(get_slice_mut_checked(
            self, n_bytes,
        )?))
    }
}

impl Writer for &mut [u8] {
    type Trusted<'b>
        = TrustedSliceWriter<'b>
    where
        Self: 'b;

    #[inline]
    fn write(&mut self, src: &[u8]) -> WriteResult<()> {
        let dst = get_slice_mut_checked(self, src.len())?;
        // Avoid the bounds check of `copy_from_slice` by using `copy_nonoverlapping`,
        // since we already bounds check in `get_slice_mut`.
        unsafe { ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len()) };
        Ok(())
    }

    #[inline]
    fn as_trusted_for(&mut self, n_bytes: usize) -> WriteResult<Self::Trusted<'_>> {
        let buf = get_slice_mut_checked(self, n_bytes)?;
        // SAFETY: we just created a slice of `n_bytes` initialized bytes, so casting to
        // `&mut [MaybeUninit<u8>]` is safe.
        let buf = unsafe { transmute::<&mut [u8], &mut [MaybeUninit<u8>]>(buf) };
        Ok(TrustedSliceWriter::new(buf))
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]
    use {super::*, crate::proptest_config::proptest_cfg, proptest::prelude::*};

    #[test]
    fn test_reader_peek() {
        let mut reader = b"hello" as &[u8];
        assert!(matches!(reader.peek(), Ok(&b'h')));
    }

    #[test]
    fn test_reader_peek_empty() {
        let mut reader = b"" as &[u8];
        assert!(matches!(reader.peek(), Err(ReadError::ReadSizeLimit(1))));
    }

    /// Execute the given block with supported readers.
    macro_rules! with_readers {
        ($bytes:expr, |$reader:ident| $body:block) => {{
            {
                let mut $reader = $bytes.as_slice();
                $body
            }
            {
                let mut $reader = TrustedSliceReaderZeroCopy::new($bytes);
                $body
            }
        }};
    }

    /// Execute the given block with readers that will bounds check (and thus not panic).
    macro_rules! with_untrusted_readers {
        ($bytes:expr, |$reader:ident| $body:block) => {{
            {
                let mut $reader = $bytes.as_slice();
                $body
            }
        }};
    }

    /// Execute the given block with slice writer and trusted slice writer for the given buffer.
    macro_rules! with_writers {
        ($buffer:expr, |$writer:ident| $body:block) => {{
            {
                let mut $writer = $buffer.spare_capacity_mut();
                $body
                $buffer.clear();
            }
            {
                let mut $writer = TrustedSliceWriter::new($buffer.spare_capacity_mut());
                $body
                $buffer.clear();
            }
            {
                let _capacity = $buffer.capacity();
                $buffer.resize(_capacity, 0);
                let mut $writer = $buffer.as_mut_slice();
                $body
                $buffer.clear();
            }
        }};
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_reader_copy_into_slice(bytes in any::<Vec<u8>>()) {
            with_readers!(&bytes, |reader| {
                let mut vec = Vec::with_capacity(bytes.len());
                let half = bytes.len() / 2;
                let dst = vec.spare_capacity_mut();
                reader.copy_into_slice(&mut dst[..half]).unwrap();
                reader
                    .as_trusted_for(bytes.len() - half)
                    .unwrap()
                    .copy_into_slice(&mut dst[half..])
                    .unwrap();
                unsafe { vec.set_len(bytes.len()) };
                prop_assert_eq!(&vec, &bytes);
            });
        }

        #[test]
        fn test_reader_fill_exact(bytes in any::<Vec<u8>>()) {
            with_readers!(&bytes, |reader| {
                let read = reader.fill_exact(bytes.len()).unwrap();
                prop_assert_eq!(&read, &bytes);
            });
        }

        #[test]
        fn slice_reader_fill_exact_input_too_large(bytes in any::<Vec<u8>>()) {
            with_untrusted_readers!(&bytes, |reader| {
                prop_assert!(matches!(reader.fill_exact(bytes.len() + 1), Err(ReadError::ReadSizeLimit(x)) if x == bytes.len() + 1));
            });
        }

        #[test]
        fn test_reader_copy_into_slice_input_too_large(bytes in any::<Vec<u8>>()) {
            with_untrusted_readers!(&bytes, |reader| {
                let mut vec = Vec::with_capacity(bytes.len() + 1);
                let dst = vec.spare_capacity_mut();
                prop_assert!(matches!(reader.copy_into_slice(dst), Err(ReadError::ReadSizeLimit(x)) if x == bytes.len() + 1));
            });
        }

        #[test]
        fn test_reader_consume(bytes in any::<Vec<u8>>()) {
            with_readers!(&bytes, |reader| {
                reader.consume(bytes.len()).unwrap();
                prop_assert!(matches!(reader.fill_buf(1), Ok(&[])));
            });
        }

        #[test]
        fn test_reader_consume_input_too_large(bytes in any::<Vec<u8>>()) {
            let mut reader = bytes.as_slice();
            prop_assert!(matches!(reader.consume(bytes.len() + 1), Err(ReadError::ReadSizeLimit(x)) if x == bytes.len() + 1));
        }

        #[test]
        fn test_reader_copy_into_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_readers!(&bytes, |reader| {
                for int in &ints {
                    let mut val = MaybeUninit::<u64>::uninit();
                    unsafe { reader.copy_into_t(&mut val).unwrap() };
                    unsafe { prop_assert_eq!(val.assume_init(), *int) };
                }
            });
        }

        #[test]
        fn test_reader_copy_into_slice_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            with_readers!(&bytes, |reader| {
                let mut vals: Vec<u64> = Vec::with_capacity(ints.len());
                let dst = vals.spare_capacity_mut();
                unsafe { reader.copy_into_slice_t(dst).unwrap() };
                unsafe { vals.set_len(ints.len()) };
                prop_assert_eq!(&vals, &ints);
            });
        }

        #[test]
        fn test_writer_write(bytes in any::<Vec<u8>>()) {
            let capacity = bytes.len();
            let mut buffer = Vec::with_capacity(capacity);
            with_writers!(&mut buffer, |writer| {
                writer.write(&bytes).unwrap();
                let written = capacity - writer.len();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &bytes);
            });
        }

        #[test]
        fn test_writer_write_input_too_large(bytes in proptest::collection::vec(any::<u8>(), 1..=100)) {
            let mut buffer = Vec::with_capacity(bytes.len() - 1);
            let mut writer = buffer.spare_capacity_mut();
            prop_assert!(matches!(writer.write(&bytes), Err(WriteError::WriteSizeLimit(x)) if x == bytes.len()));
        }

        #[test]
        fn test_writer_write_t(int in any::<u64>()) {
            let capacity = 8;
            let mut buffer = Vec::with_capacity(capacity);
            with_writers!(&mut buffer, |writer| {
                unsafe { writer.write_t(&int).unwrap() };
                let written = capacity - writer.len();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &int.to_le_bytes());
            });
        }

        #[test]
        fn test_writer_write_slice_t(ints in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let bytes = ints.iter().flat_map(|int| int.to_le_bytes()).collect::<Vec<u8>>();
            let capacity = bytes.len();
            let mut buffer = Vec::with_capacity(capacity);
            with_writers!(&mut buffer, |writer| {
                unsafe { writer.write_slice_t(&ints).unwrap() };
                let written = capacity - writer.len();
                unsafe { buffer.set_len(written) };
                prop_assert_eq!(&buffer, &bytes);
            });
        }
    }
}
