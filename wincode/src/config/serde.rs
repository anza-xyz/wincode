//! Configuration-aware serialize / deserialize traits and functions.
use {
    crate::{
        config::{Config, ConfigCore},
        io::{Reader, Writer},
        ReadResult, SchemaRead, SchemaReadOwned, SchemaWrite, WriteResult,
    },
    core::mem::MaybeUninit,
};

/// Like [`crate::Serialize`], but allows the caller to provide a custom configuration.
pub trait Serialize<C: Config>: SchemaWrite<C> {
    /// Serialize a serializable type into a `Vec` of bytes.
    #[cfg(feature = "alloc")]
    fn serialize(src: &Self::Src, config: C) -> WriteResult<Vec<u8>> {
        let capacity = Self::size_of(src)?;
        let mut buffer = Vec::with_capacity(capacity);
        let mut writer = buffer.spare_capacity_mut();
        Self::serialize_into(&mut writer, src, config)?;
        let len = writer.len();
        unsafe {
            #[allow(clippy::arithmetic_side_effects)]
            buffer.set_len(capacity - len);
        }
        Ok(buffer)
    }

    /// Serialize a serializable type into the given [`Writer`].
    #[inline]
    #[expect(unused_variables)]
    fn serialize_into(dst: &mut impl Writer, src: &Self::Src, config: C) -> WriteResult<()> {
        Self::write(dst, src)?;
        dst.finish()?;
        Ok(())
    }

    /// Get the size in bytes of the type when serialized.
    #[inline]
    #[expect(unused_variables)]
    fn serialized_size(src: &Self::Src, config: C) -> WriteResult<u64> {
        Self::size_of(src).map(|size| size as u64)
    }
}

impl<T, C: Config> Serialize<C> for T where T: SchemaWrite<C> + ?Sized {}

/// Like [`crate::Deserialize`], but allows the caller to provide a custom configuration.
pub trait Deserialize<'de, C: Config>: SchemaRead<'de, C> {
    /// Deserialize the input bytes into a new `Self::Dst`.
    #[inline(always)]
    #[expect(unused_variables)]
    fn deserialize(mut src: &'de [u8], config: C) -> ReadResult<Self::Dst> {
        Self::get(&mut src)
    }

    /// Deserialize the input bytes into `dst`.
    #[inline]
    #[expect(unused_variables)]
    fn deserialize_into(
        mut src: &'de [u8],
        dst: &mut MaybeUninit<Self::Dst>,
        config: C,
    ) -> ReadResult<()> {
        Self::read(&mut src, dst)
    }
}

impl<'de, T, C: Config> Deserialize<'de, C> for T where T: SchemaRead<'de, C> {}

/// Like [`crate::DeserializeOwned`], but allows the caller to provide a custom configuration.
pub trait DeserializeOwned<C: Config>: SchemaReadOwned<C> {
    /// Deserialize from the given [`Reader`] into a new `Self::Dst`.
    #[inline(always)]
    fn deserialize_from<'de>(
        src: &mut impl Reader<'de>,
    ) -> ReadResult<<Self as SchemaRead<'de, C>>::Dst> {
        Self::get(src)
    }

    /// Deserialize from the given [`Reader`] into `dst`.
    #[inline]
    fn deserialize_from_into<'de>(
        src: &mut impl Reader<'de>,
        dst: &mut MaybeUninit<<Self as SchemaRead<'de, C>>::Dst>,
    ) -> ReadResult<()> {
        Self::read(src, dst)
    }
}

impl<T, C: Config> DeserializeOwned<C> for T where T: SchemaReadOwned<C> {}

/// Like [`crate::serialize`], but allows the caller to provide a custom configuration.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{config::Configuration, len::FixIntLen};
/// let config = Configuration::default().with_length_encoding::<FixIntLen<u32>>();
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::config::serialize(&vec, config).unwrap();
/// assert_eq!(vec.len(), u32::from_le_bytes(bytes[0..4].try_into().unwrap()) as usize);
/// # }
/// ```
#[cfg(feature = "alloc")]
pub fn serialize<T, C: Config>(src: &T, config: C) -> WriteResult<Vec<u8>>
where
    T: SchemaWrite<C, Src = T> + ?Sized,
{
    T::serialize(src, config)
}

/// Like [`crate::serialize_into`], but allows the caller to provide a custom configuration.
#[inline]
pub fn serialize_into<T, C: Config>(dst: &mut impl Writer, src: &T, config: C) -> WriteResult<()>
where
    T: SchemaWrite<C, Src = T> + ?Sized,
{
    T::serialize_into(dst, src, config)
}

/// Like [`crate::serialized_size`], but allows the caller to provide a custom configuration.
#[inline]
pub fn serialized_size<T, C: Config>(src: &T, config: C) -> WriteResult<u64>
where
    T: SchemaWrite<C, Src = T> + ?Sized,
{
    T::serialized_size(src, config)
}

/// Like [`crate::deserialize`], but allows the caller to provide a custom configuration.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{config::Configuration, len::FixIntLen};
/// let config = Configuration::default().with_length_encoding::<FixIntLen<u32>>();
/// let vec: Vec<u8> = vec![1, 2, 3];
/// let bytes = wincode::config::serialize(&vec, config).unwrap();
/// let deserialized: Vec<u8> = wincode::config::deserialize(&bytes, config).unwrap();
/// assert_eq!(vec.len(), u32::from_le_bytes(bytes[0..4].try_into().unwrap()) as usize);
/// assert_eq!(vec, deserialized);
/// # }
/// ```
#[inline(always)]
pub fn deserialize<'de, T, C: Config>(src: &'de [u8], config: C) -> ReadResult<T>
where
    T: SchemaRead<'de, C, Dst = T>,
{
    T::deserialize(src, config)
}

/// Like [`crate::deserialize_mut`], but allows the caller to provide a custom configuration.
#[inline(always)]
#[expect(unused_variables)]
pub fn deserialize_mut<'de, T, C: Config>(mut src: &'de mut [u8], config: C) -> ReadResult<T>
where
    T: SchemaRead<'de, C, Dst = T>,
{
    T::get(&mut src)
}

/// Like [`crate::deserialize_from`], but allows the caller to provide a custom configuration.
#[inline(always)]
#[expect(unused_variables)]
pub fn deserialize_from<'de, T, C: Config>(src: &mut impl Reader<'de>, config: C) -> ReadResult<T>
where
    T: SchemaReadOwned<C, Dst = T>,
{
    T::deserialize_from(src)
}

/// Marker trait for types that can be deserialized via direct borrows from a [`Reader`].
///
/// <div class="warning">
/// You should not manually implement this trait for your own type unless you absolutely
/// know what you're doing. The derive macros will automatically implement this trait for your type
/// if it is eligible for zero-copy deserialization.
/// </div>
///
/// # Safety
///
/// - The type must not have any invalid bit patterns, no layout requirements, no endianness checks, etc.
pub unsafe trait ZeroCopy<C: ConfigCore>: 'static {
    /// Like [`crate::ZeroCopy::from_bytes`], but allows the caller to provide a custom configuration.
    #[inline(always)]
    #[expect(unused_variables)]
    fn from_bytes<'de>(mut bytes: &'de [u8], config: C) -> ReadResult<&'de Self>
    where
        Self: SchemaRead<'de, C, Dst = Self> + Sized,
    {
        <&Self as SchemaRead<'de, C>>::get(&mut bytes)
    }

    /// Like [`crate::ZeroCopy::from_bytes_mut`], but allows the caller to provide a custom configuration.
    #[inline(always)]
    #[expect(unused_variables)]
    fn from_bytes_mut<'de>(mut bytes: &'de mut [u8], config: C) -> ReadResult<&'de mut Self>
    where
        Self: SchemaRead<'de, C, Dst = Self> + Sized,
    {
        <&mut Self as SchemaRead<'de, C>>::get(&mut bytes)
    }
}
