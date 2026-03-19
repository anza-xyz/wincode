use {
    crate::io::{WriteResult, Writer},
    std::io::{BufWriter, Write},
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

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::serde::{Serialize, serialize},
    };

    const MAGIC: u64 = 0xdeadbeef_cafebabe;
    const DATA: &[(u32, bool, &u64)] = &[
        (1u32, false, &MAGIC),
        (2u32, true, &MAGIC),
        (3u32, false, &MAGIC),
    ];

    fn assert_serializes_data(mut writer: impl Writer) {
        <[(u32, bool, &u64)]>::serialize_into(&mut writer, DATA).unwrap();
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
}
