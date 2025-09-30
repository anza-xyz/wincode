#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use {
    crate::{
        error::Result,
        io::{Reader, Writer},
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
/// # use wincode::{Deserialize, containers::{self, Pod}};
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// // Use the optimized `Pod` container
/// type Dst = containers::Vec<Pod<u8>>;
/// let deserialized = Dst::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// ```
///
/// Using direct deserialization (`T::Dst = T`) (non-optimized):
/// ```
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// ```
pub trait Deserialize: SchemaRead {
    /// Deserialize `bytes` into a new `Self::Dst`.
    #[inline(always)]
    fn deserialize(bytes: &[u8]) -> Result<Self::Dst> {
        let mut dst = MaybeUninit::uninit();
        Self::deserialize_into(bytes, &mut dst)?;
        // SAFETY: Implementor ensures `SchemaRead` properly initializes the `Self::Dst`.
        Ok(unsafe { dst.assume_init() })
    }

    /// Deserialize `bytes` into `target`.
    #[inline]
    fn deserialize_into(bytes: &[u8], target: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let mut cursor = Reader::new(bytes);
        Self::read(&mut cursor, target)?;
        Ok(())
    }
}

impl<T> Deserialize for T where T: SchemaRead {}

/// Helper over [`SchemaWrite`] that automatically constructs a writer
/// and serializes a source.
///
/// # Examples
///
/// Using containers (indirect serialization):
/// ```
/// # use wincode::{Serialize, containers::{self, Pod}};
/// let vec: Vec<u8> = vec![1, 2, 3];
/// // Use the optimized `Pod` container
/// type Src = containers::Vec<Pod<u8>>;
/// let bytes = Src::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// ```
///
/// Using direct serialization (`T::Src = T`) (non-optimized):
/// ```
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// ```
pub trait Serialize: SchemaWrite {
    /// Serialize a serializable type into a `Vec` of bytes.
    #[cfg(feature = "alloc")]
    fn serialize(src: &Self::Src) -> Result<Vec<u8>> {
        let mut buffer = Vec::with_capacity(Self::size_of(src)?);
        let len = Self::serialize_into(src, buffer.spare_capacity_mut())?;
        unsafe {
            buffer.set_len(len);
        }
        Ok(buffer)
    }

    /// Serialize a serializable type into the given byte buffer.
    ///
    /// Returns the number of bytes written to the buffer.
    #[inline]
    fn serialize_into(src: &Self::Src, target: &mut [MaybeUninit<u8>]) -> Result<usize> {
        let mut writer = Writer::new(target);
        Self::write(&mut writer, src)?;
        Ok(writer.finish())
    }

    /// Get the size in bytes of the type when serialized.
    #[inline]
    fn serialized_size(src: &Self::Src) -> Result<u64> {
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
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// ```
#[inline(always)]
pub fn deserialize<T>(bytes: &[u8]) -> Result<T>
where
    T: SchemaRead<Dst = T>,
{
    T::deserialize(bytes)
}

/// Deserialize a type from the given bytes into the given target.
///
/// Like [`deserialize`], but allows the caller to provide their own target.
#[inline]
pub fn deserialize_into<T>(bytes: &[u8], target: &mut MaybeUninit<T>) -> Result<()>
where
    T: SchemaRead<Dst = T>,
{
    T::deserialize_into(bytes, target)
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
pub fn serialize<T>(value: &T) -> Result<Vec<u8>>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialize(value)
}

/// Serialize a type into the given byte buffer.
///
/// Like [`serialize`], but allows the caller to provide their own buffer.
#[inline]
pub fn serialize_into<T>(value: &T, target: &mut [MaybeUninit<u8>]) -> Result<usize>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialize_into(value, target)
}

/// Get the size in bytes of the type when serialized.
#[inline(always)]
pub fn serialized_size<T>(value: &T) -> Result<u64>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialized_size(value)
}
