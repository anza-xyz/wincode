//! Configuration-aware serialize / deserialize traits and functions.
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use {
    crate::{
        ReadResult, SchemaRead, SchemaReadContext, SchemaReadOwned, SchemaWrite, WriteResult,
        config::{Config, ConfigCore},
        error,
        io::{Reader, Writer},
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
        Self::serialize_into(writer.by_ref(), src, config)?;
        let len = writer.len();
        unsafe {
            #[allow(clippy::arithmetic_side_effects)]
            buffer.set_len(capacity - len);
        }
        Ok(buffer)
    }

    /// Serialize a serializable type into the given [`Writer`].
    ///
    /// # Partial writes
    ///
    /// This operation is not transactional. If it returns an error, the writer
    /// may already contain a prefix of the serialized value. Dynamically sized
    /// values in particular may discover insufficient capacity only after
    /// preceding fields have been written.
    ///
    /// If the destination must remain unchanged on failure, serialize into a
    /// temporary buffer and copy the result only after serialization succeeds.
    /// For a fixed-size destination, callers can instead use
    /// [`Self::serialized_size`] with the same configuration to check that
    /// enough space is available first.
    #[inline]
    #[expect(unused_variables)]
    fn serialize_into(mut dst: impl Writer, src: &Self::Src, config: C) -> WriteResult<()> {
        Self::write(dst.by_ref(), src)?;
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

macro_rules! maybe_size_limit {
    ($config:ty, $src:expr, |$reader:ident| $body:expr $(,)?) => {{
        let mut src = $src;

        match <$config as $crate::config::ConfigCore>::DESERIALIZATION_SIZE_LIMIT {
            Some(limit) => {
                let $reader = src.as_limited_for(limit);
                $body
            }
            None => {
                let $reader = src;
                $body
            }
        }
    }};
}

/// Like [`crate::Deserialize`], but allows the caller to provide a custom configuration.
pub trait Deserialize<'de, C: Config>: SchemaRead<'de, C> {
    /// Deserialize the input bytes into a new `Self::Dst`.
    #[inline(always)]
    #[expect(unused_variables)]
    fn deserialize(src: &'de [u8], config: C) -> ReadResult<Self::Dst> {
        maybe_size_limit!(C, src, |reader| Self::get(reader))
    }

    /// Deserialize the input bytes into `dst`.
    #[inline]
    #[expect(unused_variables)]
    fn deserialize_into(
        src: &'de [u8],
        dst: &mut MaybeUninit<Self::Dst>,
        config: C,
    ) -> ReadResult<()> {
        maybe_size_limit!(C, src, |reader| Self::read(reader, dst))
    }
}

impl<'de, T, C: Config> Deserialize<'de, C> for T where T: SchemaRead<'de, C> {}

/// Like [`crate::DeserializeOwned`], but allows the caller to provide a custom configuration.
pub trait DeserializeOwned<C: Config>: SchemaReadOwned<C> {
    /// Deserialize from the given [`Reader`] into a new `Self::Dst`.
    #[inline(always)]
    fn deserialize_from<'de>(
        src: impl Reader<'de>,
    ) -> ReadResult<<Self as SchemaRead<'de, C>>::Dst> {
        maybe_size_limit!(C, src, |reader| Self::get(reader))
    }

    /// Deserialize from the given [`Reader`] into `dst`.
    #[inline]
    fn deserialize_from_into<'de>(
        src: impl Reader<'de>,
        dst: &mut MaybeUninit<<Self as SchemaRead<'de, C>>::Dst>,
    ) -> ReadResult<()> {
        maybe_size_limit!(C, src, |reader| Self::read(reader, dst))
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
///
/// This has the same non-transactional, partial-write behavior documented by
/// [`crate::serialize_into`].
#[inline]
pub fn serialize_into<T, C: Config>(dst: impl Writer, src: &T, config: C) -> WriteResult<()>
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

/// Like [`crate::deserialize_exact`], but with a custom configuration.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::config::Configuration;
/// let config = Configuration::default();
/// let bytes = wincode::config::serialize(&123u64, config).unwrap();
/// let value: u64 = wincode::config::deserialize_exact(&bytes, config).unwrap();
/// assert_eq!(value, 123);
///
/// let mut extra = bytes.clone();
/// extra.push(0xAA);
/// assert!(wincode::config::deserialize_exact::<u64, _>(&extra, config).is_err());
/// # }
/// ```
#[inline(always)]
#[expect(unused_variables)]
pub fn deserialize_exact<'de, T, C: Config>(mut src: &'de [u8], config: C) -> ReadResult<T>
where
    T: SchemaRead<'de, C, Dst = T>,
{
    let value = maybe_size_limit!(C, src.by_ref(), |reader| T::get(reader))?;
    if src.is_empty() {
        Ok(value)
    } else {
        Err(error::trailing_bytes())
    }
}

/// Like [`crate::deserialize_with_context`], but allows the caller to provide a custom configuration.
#[inline(always)]
#[expect(unused_variables)]
pub fn deserialize_with_context<'de, Ctx, T, C: Config>(
    ctx: Ctx,
    src: &'de [u8],
    config: C,
) -> ReadResult<T>
where
    T: SchemaReadContext<'de, C, Ctx, Dst = T>,
{
    maybe_size_limit!(C, src, |reader| T::get_with_context(ctx, reader))
}

/// Like [`crate::deserialize_mut`], but allows the caller to provide a custom configuration.
#[inline(always)]
#[expect(unused_variables)]
pub fn deserialize_mut<'de, T, C: Config>(src: &'de mut [u8], config: C) -> ReadResult<T>
where
    T: SchemaRead<'de, C, Dst = T>,
{
    maybe_size_limit!(C, src, |reader| T::get(reader))
}

/// Like [`crate::deserialize_from`], but allows the caller to provide a custom configuration.
#[inline(always)]
#[expect(unused_variables)]
pub fn deserialize_from<'de, T, C: Config>(src: impl Reader<'de>, config: C) -> ReadResult<T>
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
    fn from_bytes<'de>(bytes: &'de [u8], config: C) -> ReadResult<&'de Self>
    where
        Self: SchemaRead<'de, C, Dst = Self> + Sized,
    {
        maybe_size_limit!(C, bytes, |reader| <&Self as SchemaRead<'de, C>>::get(
            reader
        ))
    }

    /// Like [`crate::ZeroCopy::from_bytes_mut`], but allows the caller to provide a custom configuration.
    #[inline(always)]
    #[expect(unused_variables)]
    fn from_bytes_mut<'de>(bytes: &'de mut [u8], config: C) -> ReadResult<&'de mut Self>
    where
        Self: SchemaRead<'de, C, Dst = Self> + Sized,
    {
        maybe_size_limit!(C, bytes, |reader| <&mut Self as SchemaRead<'de, C>>::get(
            reader
        ))
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{ReadError, config::Configuration, io::ReadError as IoReadError},
    };

    #[test]
    fn configured_deserialization_limit_is_enforced() {
        let bytes = 42u64.to_le_bytes();
        let limited = Configuration::default().with_deserialization_size_limit::<4>();

        assert!(matches!(
            deserialize::<u64, _>(&bytes, limited),
            Err(ReadError::Io(IoReadError::ReadSizeLimit(8)))
        ));
        assert!(matches!(
            deserialize_from::<u64, _>(bytes.as_slice(), limited),
            Err(ReadError::Io(IoReadError::ReadSizeLimit(8)))
        ));

        let exact = Configuration::default().with_deserialization_size_limit::<8>();
        assert_eq!(deserialize::<u64, _>(&bytes, exact).unwrap(), 42);

        let disabled = limited.disable_deserialization_size_limit();
        assert_eq!(deserialize::<u64, _>(&bytes, disabled).unwrap(), 42);
    }

    #[test]
    fn zero_copy_deserialization_honors_limit() {
        let bytes = [42u8];
        let limited = Configuration::default().with_deserialization_size_limit::<0>();

        assert!(matches!(
            <u8 as ZeroCopy<_>>::from_bytes(&bytes, limited),
            Err(ReadError::Io(IoReadError::ReadSizeLimit(1)))
        ));

        let mut bytes = bytes;
        assert!(matches!(
            <u8 as ZeroCopy<_>>::from_bytes_mut(&mut bytes, limited),
            Err(ReadError::Io(IoReadError::ReadSizeLimit(1)))
        ));
    }
}
