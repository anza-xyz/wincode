#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use {
    crate::{
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
        SchemaReadOwned,
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
/// # use wincode::{Deserialize, containers};
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::serialize(&vec).unwrap();
/// type Dst = containers::Vec<u8>;
/// let deserialized = Dst::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
///
/// Using direct deserialization (`T::Dst = T`):
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
    fn deserialize(mut src: &'de [u8]) -> ReadResult<Self::Dst> {
        <Self as SchemaRead<'de>>::get(&mut src)
    }

    /// Deserialize `bytes` into `target`.
    #[inline]
    fn deserialize_into(mut src: &'de [u8], dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <Self as SchemaRead<'de>>::read(&mut src, dst)
    }
}

impl<'de, T> Deserialize<'de> for T where T: SchemaRead<'de> {}

/// A variant of [`Deserialize`] for types that can be deserialized without borrowing from the reader.
pub trait DeserializeOwned: SchemaReadOwned {
    /// Deserialize from the given [`Reader`] into a new `Self::Dst`.
    #[inline(always)]
    fn deserialize_from<'de>(
        src: &mut impl Reader<'de>,
    ) -> ReadResult<<Self as SchemaRead<'de>>::Dst> {
        <Self as SchemaRead<'de>>::get(src)
    }

    /// Deserialize from the given [`Reader`] into `dst`.
    #[inline]
    fn deserialize_from_into<'de>(
        src: &mut impl Reader<'de>,
        dst: &mut MaybeUninit<<Self as SchemaRead<'de>>::Dst>,
    ) -> ReadResult<()> {
        <Self as SchemaRead<'de>>::read(src, dst)
    }
}

impl<T> DeserializeOwned for T where T: SchemaReadOwned {}

/// Helper over [`SchemaWrite`] that automatically constructs a writer
/// and serializes a source.
///
/// # Examples
///
/// Using containers (indirect serialization):
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{Serialize, containers};
/// let vec: Vec<u8> = vec![1, 2, 3];
/// type Src = containers::Vec<u8>;
/// let bytes = Src::serialize(&vec).unwrap();
/// let deserialized: Vec<u8> = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(vec, deserialized);
/// # }
/// ```
///
/// Using direct serialization (`T::Src = T`):
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
        let capacity = Self::size_of(src)?;
        let mut buffer = Vec::with_capacity(capacity);
        let mut writer = buffer.spare_capacity_mut();
        Self::serialize_into(&mut writer, src)?;
        let len = writer.len();
        unsafe {
            #[allow(clippy::arithmetic_side_effects)]
            buffer.set_len(capacity - len);
        }
        Ok(buffer)
    }

    /// Serialize a serializable type into the given byte buffer.
    #[inline]
    fn serialize_into(dst: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        <Self as SchemaWrite>::write(dst, src)?;
        dst.finish()?;
        Ok(())
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

/// Deserialize a type from the given bytes, with the ability
/// to form mutable references for types that are [`ZeroCopy`](crate::ZeroCopy).
/// This can allow mutating the serialized data in place.
///
/// # Examples
///
/// ## Zero-copy types
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// # use wincode::{SchemaWrite, SchemaRead};
/// # #[derive(Debug, PartialEq, Eq)]
/// #[derive(SchemaWrite, SchemaRead)]
/// #[repr(C)]
/// struct Data {
///     bytes: [u8; 7],
///     the_answer: u8,
/// }
///
/// let data = Data { bytes: [0; 7], the_answer: 0 };
///
/// let mut serialized = wincode::serialize(&data).unwrap();
/// let data_mut: &mut Data = wincode::deserialize_mut(&mut serialized).unwrap();
/// data_mut.bytes = *b"wincode";
/// data_mut.the_answer = 42;
///
/// let deserialized: Data = wincode::deserialize(&serialized).unwrap();
/// assert_eq!(deserialized, Data { bytes: *b"wincode", the_answer: 42 });
/// # }
/// ```
///
/// ## Mutable zero-copy members
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// # use wincode::{SchemaWrite, SchemaRead};
/// # #[derive(Debug, PartialEq, Eq)]
/// #[derive(SchemaWrite, SchemaRead)]
/// struct Data {
///     bytes: [u8; 7],
///     the_answer: u8,
/// }
/// # #[derive(Debug, PartialEq, Eq)]
/// #[derive(SchemaRead)]
/// struct DataMut<'a> {
///     bytes: &'a mut [u8; 7],
///     the_answer: u8,
/// }
///
/// let data = Data { bytes: [0; 7], the_answer: 42 };
///
/// let mut serialized = wincode::serialize(&data).unwrap();
/// let data_mut: DataMut<'_> = wincode::deserialize_mut(&mut serialized).unwrap();
/// *data_mut.bytes = *b"wincode";
///
/// let deserialized: Data = wincode::deserialize(&serialized).unwrap();
/// assert_eq!(deserialized, Data { bytes: *b"wincode", the_answer: 42 });
/// # }
/// ```
#[inline(always)]
pub fn deserialize_mut<'de, T>(mut src: &'de mut [u8]) -> ReadResult<T>
where
    T: SchemaRead<'de, Dst = T>,
{
    <T as SchemaRead<'de>>::get(&mut src)
}

/// Deserialize a type from the given bytes into the given target.
///
/// Like [`deserialize`], but allows the caller to provide their own reader.
///
/// Because not all readers will support zero-copy deserialization, this function
/// requires [`SchemaReadOwned`] instead of [`SchemaRead`]. If you are deserializing
/// from raw bytes, always prefer [`deserialize`] for maximum flexibility.
#[inline]
pub fn deserialize_from<'de, T>(src: &mut impl Reader<'de>) -> ReadResult<T>
where
    T: SchemaReadOwned<Dst = T>,
{
    T::deserialize_from(src)
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
pub fn serialize_into<T>(dst: &mut impl Writer, src: &T) -> WriteResult<()>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialize_into(dst, src)
}

/// Get the size in bytes of the type when serialized.
#[inline(always)]
pub fn serialized_size<T>(src: &T) -> WriteResult<u64>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    T::serialized_size(src)
}
