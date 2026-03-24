use {
    super::{ReadResult, Reader},
    core::mem::MaybeUninit,
};

/// Slice reader that doesn't implement `take_borrowed` or `take_scoped`.
///
/// Useful for tests that exercise `SchemaRead` implementations that utilize
/// `reader.supports_borrow()`.
pub(crate) struct NoBorrowReader<'a> {
    inner: &'a [u8],
}

impl<'a> NoBorrowReader<'a> {
    pub(crate) fn new(inner: &'a [u8]) -> Self {
        Self { inner }
    }
}

impl Reader<'_> for NoBorrowReader<'_> {
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        self.inner.copy_into_slice(dst)
    }
}
