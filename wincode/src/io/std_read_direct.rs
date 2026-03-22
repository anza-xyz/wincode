use {
    crate::io::{ReadResult, Reader},
    std::{
        io::{BufReader, Read},
        mem::{MaybeUninit, transmute},
    },
};

pub struct ReadAdapter<R: ?Sized> {
    inner: R,
}

impl<R: Read + ?Sized> Reader<'_> for ReadAdapter<R> {
    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        Ok(self
            .inner
            .read_exact(unsafe { transmute::<&mut [MaybeUninit<u8>], &mut [u8]>(dst) })?)
    }
}

impl<R: Read + ?Sized> Reader<'_> for BufReader<R> {
    #[inline]
    fn copy_into_slice(&mut self, dst: &mut [MaybeUninit<u8>]) -> ReadResult<()> {
        Ok(self.read_exact(unsafe { transmute::<&mut [MaybeUninit<u8>], &mut [u8]>(dst) })?)
    }
}
