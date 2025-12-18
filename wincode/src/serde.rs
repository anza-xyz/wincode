#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use {
    crate::{
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
        SchemaReadOwned, TypeMeta, ZeroCopy,
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
    fn deserialize(src: &'de [u8]) -> ReadResult<Self::Dst> {
        let mut dst = MaybeUninit::uninit();
        Self::deserialize_into(src, &mut dst)?;
        // SAFETY: Implementor ensures `SchemaRead` properly initializes the `Self::Dst`.
        Ok(unsafe { dst.assume_init() })
    }

    /// Deserialize `src` into a mutable reference to `Self::Dst`.
    ///
    /// This allows mutating the serialized data in place.
    ///
    /// Only available for types that are [`ZeroCopy`].
    #[inline(always)]
    fn deserialize_mut(mut src: &'de mut [u8]) -> ReadResult<&'de mut Self::Dst>
    where
        Self: ZeroCopy + Sized,
    {
        <&mut Self as SchemaRead<'de>>::get(&mut src)
    }

    /// Deserialize `src` into a mutable reference to `Self::Dst`.
    ///
    /// This allows mutating the serialized data in place.
    ///
    /// Only available for types that are [`ZeroCopy`].
    #[inline(always)]
    fn deserialize_ref(mut src: &'de [u8]) -> ReadResult<&'de Self::Dst>
    where
        Self: ZeroCopy + Sized,
    {
        <&Self as SchemaRead<'de>>::get(&mut src)
    }

    /// Deserialize `bytes` into `target`.
    #[inline]
    fn deserialize_into(mut src: &'de [u8], dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        match Self::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => {
                // SAFETY: `T` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                unsafe { src.copy_into_t(dst)? };
            }
            TypeMeta::Static {
                size,
                zero_copy: false,
            } => {
                // SAFETY: `Self::TYPE_META` specifies a static size, so a single read of `Self::Dst`
                // will consume `size` bytes, fully consuming the trusted window.
                let mut reader = unsafe { src.as_trusted_for(size) }?;
                Self::read(&mut reader, dst)?;
            }
            TypeMeta::Dynamic => {
                Self::read(&mut src, dst)?;
            }
        }
        Ok(())
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
        let mut dst = MaybeUninit::uninit();
        Self::deserialize_from_into(src, &mut dst)?;
        Ok(unsafe { dst.assume_init() })
    }

    /// Deserialize from the given [`Reader`] into `dst`.
    fn deserialize_from_into<'de>(
        src: &mut impl Reader<'de>,
        dst: &mut MaybeUninit<<Self as SchemaRead<'de>>::Dst>,
    ) -> ReadResult<()> {
        match Self::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => {
                // SAFETY: `T` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                unsafe { src.copy_into_t(dst)? };
            }
            TypeMeta::Static {
                size,
                zero_copy: false,
            } => {
                // SAFETY: `Self::TYPE_META` specifies a static size, so a single read of `Self::Dst`
                // will consume `size` bytes, fully consuming the trusted window.
                let mut reader = unsafe { src.as_trusted_for(size) }?;
                Self::read(&mut reader, dst)?;
            }
            TypeMeta::Dynamic => {
                Self::read(src, dst)?;
            }
        }
        Ok(())
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
        match Self::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => {
                // SAFETY: `T` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                unsafe { dst.write_t(src)? };
            }
            TypeMeta::Static {
                size,
                zero_copy: false,
            } => {
                // SAFETY: `Self::TYPE_META` specifies a static size, so a single write of `Self::Src`
                // will consume `size` bytes, fully consuming the trusted window.
                let mut writer = unsafe { dst.as_trusted_for(size) }?;
                Self::write(&mut writer, src)?;
                writer.finish()?;
            }
            TypeMeta::Dynamic => {
                Self::write(dst, src)?;
            }
        }

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

/// Deserialize a mutable reference to a type from the given bytes.
///
/// This allows mutating the serialized data in place.
///
/// Only available for types that are [`ZeroCopy`].
///
/// # Examples
///
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
#[inline(always)]
pub fn deserialize_mut<'de, T>(src: &'de mut [u8]) -> ReadResult<&'de mut T>
where
    T: SchemaRead<'de, Dst = T> + ZeroCopy + Sized,
{
    T::deserialize_mut(src)
}

/// Deserialize a reference to a type from the given bytes.
///
/// Only available for types that are [`ZeroCopy`].
///
/// # Examples
///
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
/// let data = Data { bytes: *b"wincode", the_answer: 42 };
///
/// let serialized = wincode::serialize(&data).unwrap();
/// let data_ref: &Data = wincode::deserialize_ref(&serialized).unwrap();
///
/// assert_eq!(data_ref, &data);
/// # }
/// ```
#[inline(always)]
pub fn deserialize_ref<'de, T>(src: &'de [u8]) -> ReadResult<&'de T>
where
    T: SchemaRead<'de, Dst = T> + ZeroCopy + Sized,
{
    T::deserialize_ref(src)
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
