#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use {
    crate::{
        error::{ReadResult, WriteResult},
        io::{Reader, SliceReader, SliceWriter, Writer},
        schema::{SchemaRead, SchemaWrite},
    },
    core::mem::MaybeUninit,
};

/// Helper over [`SchemaRead`] that automatically constructs a reader
/// and initializes a destination.
///
/// # Examples
///
/// Using containers (indirect deserialization):
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{Deserialize, containers::{self, Pod}};
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// // Use the optimized `Pod` container
/// type Dst = containers::Vec<Pod<u8>>;
/// let deserialized = Dst::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
///
/// Using direct deserialization (`T::Dst = T`) (non-optimized):
/// ```
/// # #[cfg(feature = "alloc")] {
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
pub trait Deserialize<'de>: SchemaRead<'de> {
    /// Deserialize `bytes` into a new `Self::Dst`.
    #[inline(always)]
    fn deserialize(src: &'de [u8]) -> ReadResult<Self::Dst> {
        let mut dst = MaybeUninit::uninit();
        let src = SliceReader::new(src);
        Self::deserialize_into(src, &mut dst)?;
        // SAFETY: Implementor ensures `SchemaRead` properly initializes the `Self::Dst`.
        Ok(unsafe { dst.assume_init() })
    }

    /// Deserialize `bytes` into `target`.
    #[inline]
    fn deserialize_into(
        mut src: impl Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> ReadResult<()> {
        Self::read(&mut src, dst)?;
        Ok(())
    }
}

impl<'de, T> Deserialize<'de> for T where T: SchemaRead<'de> {}

/// Helper over [`SchemaWrite`] that automatically constructs a writer
/// and serializes a source.
///
/// # Examples
///
/// Using containers (indirect serialization):
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{Serialize, containers::{self, Pod}};
/// let vec: Vec<u8> = vec![1, 2, 3];
/// // Use the optimized `Pod` container
/// type Src = containers::Vec<Pod<u8>>;
/// let bytes = Src::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
///
/// Using direct serialization (`T::Src = T`) (non-optimized):
/// ```
/// # #[cfg(feature = "alloc")] {
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
pub trait Serialize: SchemaWrite {
    /// Serialize a serializable type into a `Vec` of bytes.
    #[cfg(feature = "alloc")]
    fn serialize(src: &Self::Src) -> WriteResult<Vec<u8>> {
        let mut buffer = Vec::with_capacity(Self::size_of(src)?);
        let writer = SliceWriter::new(buffer.spare_capacity_mut());
        let len = Self::serialize_into(src, writer)?;
        unsafe {
            buffer.set_len(len);
        }
        Ok(buffer)
    }

    /// Serialize a serializable type into the given byte buffer.
    ///
    /// Returns the number of bytes written to the buffer.
    #[inline]
    fn serialize_into(src: &Self::Src, mut dst: impl Writer) -> WriteResult<usize> {
        Self::write(&mut dst, src)?;
        Ok(dst.finish())
    }

    /// Get the size in bytes of the type when serialized.
    #[inline]
    fn serialized_size(src: &Self::Src) -> WriteResult<u64> {
        Self::size_of(src).map(|size| size as u64)
    }
}

impl<T> Serialize for T where T: SchemaWrite + ?Sized {}

/// Deserialize a type from the given bytes.
///
/// This is a "simplified" version of [`Deserialize::deserialize`] that
/// requires the `T::Dst` to be `T`. In other words, a schema type
/// that deserializes to itself.
///
/// This helper exists to match the expected signature of `serde`'s
/// `Deserialize`, where types that implement `Deserialize` deserialize
/// into themselves. This will be true of a large number of schema types,
/// but wont, for example, for specialized container structures.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
#[inline(always)]
pub fn deserialize<'de, T>(src: &'de [u8]) -> ReadResult<T>
where
    T: SchemaRead<'de, Dst = T>,
{
    T::deserialize(src)
}

/// Deserialize a type from the given bytes into the given target.
///
/// Like [`deserialize`], but allows the caller to provide their own reader and target.
#[inline]
pub fn deserialize_into<'de, T>(src: impl Reader<'de>, dst: &mut MaybeUninit<T>) -> ReadResult<()>
where
    T: SchemaRead<'de, Dst = T>,
{
    T::deserialize_into(src, dst)
}

/// Serialize a type into a `Vec` of bytes.
///
/// This is a "simplified" version of [`Serialize::serialize`] that
/// requires the `T::Src` to be `T`. In other words, a schema type
/// that serializes to itself.
///
/// This helper exists to match the expected signature of `serde`'s
/// `Serialize`, where types that implement `Serialize` serialize
/// themselves. This will be true of a large number of schema types,
/// but wont, for example, for specialized container structures.
///
/// # Examples
///
/// ```
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// ```
#[inline(always)]
#[cfg(feature = "alloc")]
pub fn serialize<T>(src: &T) -> WriteResult<Vec<u8>>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialize(src)
}

/// Serialize a type into the given writer.
///
/// Like [`serialize`], but allows the caller to provide their own writer.
#[inline]
pub fn serialize_into<T>(src: &T, dst: impl Writer) -> WriteResult<usize>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialize_into(src, dst)
}

/// Get the size in bytes of the type when serialized.
#[inline(always)]
pub fn serialized_size<T>(src: &T) -> WriteResult<u64>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialized_size(src)
}
