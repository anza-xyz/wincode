use {
    std::{
        io::{BufRead as _, BufReader, Read as _},
        mem::MaybeUninit,
    },
    wincode::io::ReadError,
};

pub trait ReaderNonBorrowing {
    fn read_byte(&mut self) -> Result<u8, ReadError>;
    fn read_chunks(&mut self, chunk_size: usize) -> Result<impl Iterator<Item = &[u8]>, ReadError>;
}

impl<T: ReaderNonBorrowing> ReaderNonBorrowing for &mut T {
    fn read_byte(&mut self) -> Result<u8, ReadError> {
        (*self).read_byte()
    }

    fn read_chunks(&mut self, chunk_size: usize) -> Result<impl Iterator<Item = &[u8]>, ReadError> {
        (*self).read_chunks(chunk_size)
    }
}

pub trait ReaderBorrowing<'de>: ReaderNonBorrowing {
    fn borrow_bytes(&mut self, size: usize) -> Result<&'de [u8], ReadError>;
    fn borrow_chunks(
        &mut self,
        chunk_size: usize,
    ) -> Result<impl Iterator<Item = &'de [u8]>, ReadError>;
}

impl<'de, T: ReaderBorrowing<'de>> ReaderBorrowing<'de> for &mut T {
    fn borrow_bytes(&mut self, size: usize) -> Result<&'de [u8], ReadError> {
        (*self).borrow_bytes(size)
    }

    fn borrow_chunks(
        &mut self,
        chunk_size: usize,
    ) -> Result<impl Iterator<Item = &'de [u8]>, ReadError> {
        (*self).borrow_chunks(chunk_size)
    }
}

pub trait SchemaDecode
where
    Self: Sized,
{
    fn decode(reader: impl ReaderNonBorrowing) -> Result<Self, ReadError>;

    fn decode_borrowed<'de>(reader: impl ReaderBorrowing<'de>) -> Result<Self, ReadError> {
        Self::decode(reader)
    }
}
pub trait SchemaDecodeBorrowing<'de>
where
    Self: Sized,
{
    fn decode_borrowed(reader: impl ReaderBorrowing<'de>) -> Result<Self, ReadError>;
}

impl<'de, T> SchemaDecodeBorrowing<'de> for &'de T
// TODO: constrain T to ZeroCopy
{
    fn decode_borrowed(mut reader: impl ReaderBorrowing<'de>) -> Result<Self, ReadError> {
        let bytes = reader.borrow_bytes(size_of::<T>())?;
        Ok(unsafe { &*(bytes.as_ptr() as *const T) })
    }
}

impl<R: std::io::Read> ReaderNonBorrowing for BufReader<R> {
    fn read_byte(&mut self) -> Result<u8, ReadError> {
        let mut buf = [0u8; 1];
        self.read_exact(&mut buf).map_err(|e| ReadError::Io(e))?;
        Ok(buf[0])
    }

    fn read_chunks(&mut self, chunk_size: usize) -> Result<impl Iterator<Item = &[u8]>, ReadError> {
        struct ChunksIter<'a, R> {
            reader: &'a mut BufReader<R>,
            aux: Box<[u8]>,
            done: bool,
        }
        impl<'a, R: std::io::Read> Iterator for ChunksIter<'a, R> {
            type Item = &'a [u8];
            fn next(&mut self) -> Option<&'a [u8]> {
                if self.done {
                    return None;
                }
                let chunk_size = self.aux.len();
                let available = self.reader.fill_buf().ok()?;
                if available.len() >= chunk_size {
                    // SAFETY: we consume exactly chunk_size bytes after taking the
                    // pointer, and BufReader's internal buffer is stable for the
                    // duration of this borrow since we don't refill until next().
                    let ptr = available[..chunk_size].as_ptr();
                    self.reader.consume(chunk_size);
                    Some(unsafe { std::slice::from_raw_parts(ptr, chunk_size) })
                } else if available.is_empty() {
                    self.done = true;
                    None
                } else {
                    match self.reader.read_exact(&mut self.aux) {
                        Ok(()) => {
                            let ptr = self.aux.as_ptr();
                            Some(unsafe { std::slice::from_raw_parts(ptr, chunk_size) })
                        }
                        Err(_) => {
                            self.done = true;
                            None
                        }
                    }
                }
            }
        }
        Ok(ChunksIter {
            reader: self,
            aux: vec![0u8; chunk_size].into_boxed_slice(),
            done: false,
        })
    }
}

impl ReaderNonBorrowing for &[u8] {
    fn read_byte(&mut self) -> Result<u8, ReadError> {
        let byte = self.first().copied().ok_or(ReadError::ReadSizeLimit(1))?;
        *self = &self[1..];
        Ok(byte)
    }

    fn read_chunks(&mut self, chunk_size: usize) -> Result<impl Iterator<Item = &[u8]>, ReadError> {
        let chunks = self.chunks_exact(chunk_size);
        *self = chunks.remainder();
        Ok(chunks)
    }
}

impl<'a> ReaderBorrowing<'a> for &'a [u8] {
    fn borrow_bytes(&mut self, size: usize) -> Result<&'a [u8], ReadError> {
        let bytes = &self[..size];
        *self = &self[size..];
        Ok(bytes)
    }

    fn borrow_chunks(
        &mut self,
        chunk_size: usize,
    ) -> Result<impl Iterator<Item = &'a [u8]>, ReadError> {
        let chunks = self.chunks_exact(chunk_size);
        *self = chunks.remainder();
        Ok(chunks)
    }
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct Bar {
    pub foo: u32,
    pub waz: [u8; 6],
}
impl SchemaDecode for Bar {
    fn decode(mut reader: impl ReaderNonBorrowing) -> Result<Bar, ReadError> {
        let mut uninit = MaybeUninit::<Bar>::uninit();
        unsafe {
            let mut ptr_foo = (&raw mut (*uninit.as_mut_ptr()).foo).cast::<u8>();
            for _ in 0..size_of::<u32>() {
                ptr_foo.write(reader.read_byte()?);
                ptr_foo = ptr_foo.byte_add(1);
            }
            let mut ptr_waz = (&raw mut (*uninit.as_mut_ptr()).waz).cast::<u8>();
            for _ in 0..6 {
                ptr_waz.write(reader.read_byte()?);
                ptr_waz = ptr_waz.byte_add(1);
            }
            Ok(uninit.assume_init())
        }
    }
}

#[derive(Copy, Clone)]
pub struct BarRef<'a> {
    pub foo: u32,
    pub waz: &'a [u8; 6],
}
impl<'a> SchemaDecodeBorrowing<'a> for BarRef<'a> {
    fn decode_borrowed(mut reader: impl ReaderBorrowing<'a>) -> Result<BarRef<'a>, ReadError> {
        let mut uninit = MaybeUninit::<BarRef>::uninit();
        unsafe {
            let mut ptr_foo = (&raw mut (*uninit.as_mut_ptr()).foo).cast::<u8>();
            for _ in 0..size_of::<u32>() {
                ptr_foo.write(reader.read_byte()?);
                ptr_foo = ptr_foo.byte_add(1);
            }
            let ptr_waz = &raw mut (*uninit.as_mut_ptr()).waz;
            ptr_waz.write(<&'a [u8; 6]>::decode_borrowed(reader)?);
            Ok(uninit.assume_init())
        }
    }
}

struct BarBar {
    one: Bar,
    two: Bar,
    three: Bar,
}

impl SchemaDecode for BarBar {
    fn decode(mut reader: impl ReaderNonBorrowing) -> Result<BarBar, ReadError> {
        let mut chunks = reader.read_chunks(size_of::<Bar>())?;
        let one = Bar::decode(chunks.next().unwrap())?;
        let two = Bar::decode(chunks.next().unwrap())?;
        let three = Bar::decode(chunks.next().unwrap())?;
        Ok(BarBar { one, two, three })
    }
}

struct BarBarRef<'a> {
    one: Bar,
    two: BarRef<'a>,
    three: BarRef<'a>,
}

impl<'a> SchemaDecodeBorrowing<'a> for BarBarRef<'a> {
    fn decode_borrowed(mut reader: impl ReaderBorrowing<'a>) -> Result<BarBarRef<'a>, ReadError> {
        let mut chunks = reader.borrow_chunks(size_of::<Bar>())?;
        // TODO: this is cheating - we call function with the same name from two different trait
        // actually SchemaDecodeBorrowing can have blanket impl for T: SchemaDecode, but we already use
        // blanket for &'a T
        let one = Bar::decode_borrowed(chunks.next().unwrap())?;
        let two = BarRef::decode_borrowed(chunks.next().unwrap())?;
        let three = BarRef::decode_borrowed(chunks.next().unwrap())?;
        Ok(BarBarRef { one, two, three })
    }
}

pub fn main() {
    let data = [1u8; size_of::<Bar>()];

    let buf = BufReader::new(&data[..]);
    let bar = Bar::decode(buf).unwrap();
    assert_eq!(bar.foo, 0x01010101);
    assert_eq!(bar.waz, [1u8; 6]);

    let bar_ref = BarRef::decode_borrowed(&data[..]).unwrap();
    assert_eq!(bar_ref.foo, 0x01010101);
    assert_eq!(bar_ref.waz, &[1u8; 6]);
    let bar = Bar::decode_borrowed(&data[..]).unwrap();
    assert_eq!(bar.foo, 0x01010101);
    assert_eq!(bar.waz, [1u8; 6]);

    let data = [2u8; size_of::<BarBar>()];

    let buf = BufReader::with_capacity(15, &data[..]);
    let barbar = BarBar::decode(buf).unwrap();
    assert_eq!(barbar.one.foo, 0x02020202);
    assert_eq!(barbar.one.waz, [2u8; 6]);
    assert_eq!(barbar.two.foo, 0x02020202);
    assert_eq!(barbar.two.waz, [2u8; 6]);
    assert_eq!(barbar.three.foo, 0x02020202);
    assert_eq!(barbar.three.waz, [2u8; 6]);

    let barbar_ref = BarBarRef::decode_borrowed(&data[..]).unwrap();
    assert_eq!(barbar_ref.one.foo, 0x02020202);
    assert_eq!(barbar_ref.one.waz, [2u8; 6]);
    assert_eq!(barbar_ref.two.foo, 0x02020202);
    assert_eq!(barbar_ref.two.waz, &[2u8; 6]);
    assert_eq!(barbar_ref.three.foo, 0x02020202);
    assert_eq!(barbar_ref.three.waz, &[2u8; 6]);
}
