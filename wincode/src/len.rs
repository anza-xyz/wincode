//! Support for heterogenous sequence length encoding.
use {
    crate::{
        SchemaRead, SchemaWrite, TypeMeta,
        config::{ConfigCore, PREALLOCATION_SIZE_LIMIT_DISABLED},
        error::{
            PreallocationError, ReadResult, WriteResult, pointer_sized_decode_error,
            preallocation_size_limit, write_length_encoding_overflow,
        },
        int_encoding::{ByteOrder, Endian},
        io::{Reader, Writer},
    },
    core::{any::type_name, marker::PhantomData},
};

pub const PREALLOCATION_SIZE_LIMIT_USE_CONFIG: usize = 0;

/// Cap a requested capacity at the `2^(8 * size_of::<K>())` distinct values a
/// `K` can represent.
///
/// A collection that keys on a unique `K` cannot hold more entries than there
/// are `K` values, so a malicious length keyed on a tiny type (ZST, `u8`, ...)
/// can drive an oversized `with_capacity` the data can never fill, even within
/// the preallocation limit. The cap is an upper bound on distinct keys, so it
/// never under-allocates. `None` (representable count `>= usize::MAX`) means no
/// useful cap.
#[cfg(any(feature = "std", feature = "indexmap"))]
#[inline]
pub(crate) fn unique_key_capacity<K>(len: usize) -> usize {
    match u32::try_from(size_of::<K>())
        .ok()
        .and_then(|bytes| bytes.checked_mul(u8::BITS))
        .and_then(|bits| 1usize.checked_shl(bits))
    {
        Some(max_keys) => len.min(max_keys),
        None => len,
    }
}

/// [`SeqLen`] level override of configured preallocation size limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum PreallocationLimitOverride {
    /// Use the configuration's preallocation size limit.
    #[default]
    UseConfig,
    /// Override with no limit.
    NoLimit,
    /// Override with a specific limit, in bytes.
    Override(usize),
}

impl PreallocationLimitOverride {
    /// Convert the given [`PreallocationLimitOverride`] to an `Option<usize>`,
    /// reconciling with the given configuration.
    ///
    /// If the override is [`PreallocationLimitOverride::UseConfig`], then the
    /// configuration's preallocation size limit is returned.
    /// If the override is [`PreallocationLimitOverride::NoLimit`], then `None` is returned.
    /// Otherwise, the override is returned.
    #[inline]
    pub const fn to_opt_limit_with_config<C: ConfigCore>(self) -> Option<usize> {
        match self {
            PreallocationLimitOverride::UseConfig => C::PREALLOCATION_SIZE_LIMIT,
            PreallocationLimitOverride::NoLimit => None,
            PreallocationLimitOverride::Override(limit) => Some(limit),
        }
    }

    /// Convert a raw preallocation usize value to a [`PreallocationLimitOverride`].
    ///
    /// Handles special case values [`PREALLOCATION_SIZE_LIMIT_USE_CONFIG`] and
    /// [`PREALLOCATION_SIZE_LIMIT_DISABLED`].
    #[inline]
    pub const fn from_usize(limit: usize) -> Self {
        match limit {
            PREALLOCATION_SIZE_LIMIT_USE_CONFIG => PreallocationLimitOverride::UseConfig,
            PREALLOCATION_SIZE_LIMIT_DISABLED => PreallocationLimitOverride::NoLimit,
            _ => PreallocationLimitOverride::Override(limit),
        }
    }
}

/// Behavior to support heterogenous sequence length encoding.
///
/// It is possible for sequences to have different length encoding schemes.
/// This trait abstracts over that possibility, allowing users to specify
/// the length encoding scheme for a sequence.
///
/// # Safety
///
/// Implementors must adhere to the Safety section of the method `write_bytes_needed`.
pub unsafe trait SeqLen<C: ConfigCore> {
    /// [`SeqLen`] level override of configured preallocation size limit, in bytes.
    ///
    /// Allows specializing specific uses of a given [`SeqLen`] implementation
    /// to override any configured preallocation size limit.
    const PREALLOCATION_SIZE_LIMIT_OVERRIDE: PreallocationLimitOverride =
        PreallocationLimitOverride::UseConfig;

    #[inline]
    fn prealloc_check<T>(len: usize) -> Result<(), PreallocationError> {
        fn check(len: usize, type_size: usize, limit: usize) -> Result<(), PreallocationError> {
            let needed = len
                .checked_mul(type_size)
                .ok_or_else(|| preallocation_size_limit(usize::MAX, limit))?;
            if needed > limit {
                return Err(preallocation_size_limit(needed, limit));
            }
            Ok(())
        }
        // Everything here can be const-folded by the compiler.
        if let Some(prealloc_limit) =
            Self::PREALLOCATION_SIZE_LIMIT_OVERRIDE.to_opt_limit_with_config::<C>()
        {
            // ZSTs do not require element storage in Vec-like containers, but
            // user-controlled lengths still drive iteration and may allocate
            // collection metadata. Charge one byte per ZST element so the
            // preallocation limit also bounds sequence length.
            check(len, size_of::<T>().max(1), prealloc_limit)?;
        }
        Ok(())
    }

    /// Read the length of a sequence from the reader, where
    /// `T` is the type of the sequence elements. This can be used to
    /// enforce size constraints for preallocations.
    ///
    /// May return an error if some length condition is not met
    /// (e.g., size constraints, overflow, etc.).
    #[inline]
    fn read_prealloc_check<'de, T>(reader: impl Reader<'de>) -> ReadResult<usize> {
        let len = Self::read(reader)?;
        Self::prealloc_check::<T>(len)?;
        Ok(len)
    }
    /// Read the length of a sequence, without doing any preallocation size checks.
    ///
    /// Note this may still return typical read errors and there is no unsafety implied.
    fn read<'de>(reader: impl Reader<'de>) -> ReadResult<usize>;
    /// Write the length of a sequence to the writer.
    fn write(writer: impl Writer, len: usize) -> WriteResult<()>;
    /// Calculate the number of bytes needed to write the given length.
    ///
    /// Return an error if the written size would be larger than the
    /// corresponding allocation limit while reading.
    ///
    /// # Safety
    ///
    /// If `Ok(…)` is returned, it must contain the exact number of bytes
    /// written by the `write` function for this particular object instance.
    fn write_bytes_needed_prealloc_check<T>(len: usize) -> WriteResult<usize> {
        Self::prealloc_check::<T>(len)?;
        Self::write_bytes_needed(len)
    }
    /// Calculate the number of bytes needed to write the given length.
    ///
    /// Useful for variable length encoding schemes.
    ///
    /// # Safety
    ///
    /// If `Ok(…)` is returned, it must contain the exact number of bytes
    /// written by the `write` function for this particular object instance.
    fn write_bytes_needed(len: usize) -> WriteResult<usize>;
}

/// Use the configuration's integer encoding for sequence length encoding.
///
/// For example, if the configuration's integer encoding is `FixInt`, then `UseIntLen<u64>`
/// will use the fixed-width u64 encoding.
/// If the configuration's integer encoding is `VarInt`, then `UseIntLen<u64>` will use
/// the variable-width u64 encoding.
///
/// This is bincode's default behavior.
///
/// Allows overriding the preallocation size limit per individual use.
///
/// # Examples
///
/// Override the preallocation size limit to 8 bytes.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{containers, len::UseIntLen, SchemaRead, SchemaWrite};
/// type Max8Bytes = UseIntLen<u32, 8>;
///
/// #[derive(SchemaWrite, SchemaRead)]
/// struct OverrideLen {
///     #[wincode(with = "containers::Vec<u8, Max8Bytes>")]
///     bytes: Vec<u8>,
/// }
///
/// let data_ok = OverrideLen { bytes: vec![0; 8] };
/// let serialized = wincode::serialize(&data_ok).unwrap();
/// assert!(wincode::deserialize::<OverrideLen>(&serialized).is_ok());
///
/// let data_err = OverrideLen { bytes: vec![0; 9] };
/// assert!(wincode::serialize(&data_err).is_err());
/// let serialized = wincode::serialize(&vec![0; 9]).unwrap();
/// assert!(wincode::deserialize::<OverrideLen>(&serialized).is_err());
/// # }
/// ```
pub struct UseIntLen<T, const PREALLOCATION_SIZE_LIMIT: usize = PREALLOCATION_SIZE_LIMIT_USE_CONFIG>(
    PhantomData<T>,
);

unsafe impl<const PREALLOCATION_SIZE_LIMIT: usize, T, C: ConfigCore> SeqLen<C>
    for UseIntLen<T, PREALLOCATION_SIZE_LIMIT>
where
    T: SchemaWrite<C> + for<'de> SchemaRead<'de, C>,
    T::Src: TryFrom<usize>,
    usize: for<'de> TryFrom<<T as SchemaRead<'de, C>>::Dst>,
{
    const PREALLOCATION_SIZE_LIMIT_OVERRIDE: PreallocationLimitOverride =
        PreallocationLimitOverride::from_usize(PREALLOCATION_SIZE_LIMIT);

    #[inline(always)]
    fn read<'de>(reader: impl Reader<'de>) -> ReadResult<usize> {
        let len = T::get(reader)?;
        let Ok(len) = usize::try_from(len) else {
            return Err(pointer_sized_decode_error());
        };
        Ok(len)
    }

    #[inline(always)]
    fn write(writer: impl Writer, len: usize) -> WriteResult<()> {
        let Ok(len) = T::Src::try_from(len) else {
            return Err(write_length_encoding_overflow(type_name::<T::Src>()));
        };
        T::write(writer, &len)
    }

    #[inline(always)]
    fn write_bytes_needed(len: usize) -> WriteResult<usize> {
        if let TypeMeta::Static { size, .. } = <T as SchemaWrite<C>>::TYPE_META {
            return Ok(size);
        }
        let Ok(len) = T::Src::try_from(len) else {
            return Err(write_length_encoding_overflow(type_name::<T::Src>()));
        };
        T::size_of(&len)
    }
}

/// Allow using integer primitives directly as [`SeqLen`].
///
/// Will use the configuration's integer encoding.
macro_rules! impl_use_int_primitive {
    ($($type:ty),+) => {
        $(
            unsafe impl<C: ConfigCore> SeqLen<C> for $type {
                #[inline(always)]
                #[allow(irrefutable_let_patterns)]
                fn read<'de>(reader: impl Reader<'de>) -> ReadResult<usize> {
                    let len = <$type as SchemaRead<C>>::get(reader)?;
                    let Ok(len) = usize::try_from(len) else {
                        return Err(pointer_sized_decode_error());
                    };
                    Ok(len)
                }

                #[inline(always)]
                fn write(writer: impl Writer, len: usize) -> WriteResult<()> {
                    let Ok(len) = <$type>::try_from(len) else {
                        return Err(write_length_encoding_overflow(type_name::<$type>()));
                    };
                    <$type as SchemaWrite<C>>::write(writer, &len)
                }

                #[inline(always)]
                fn write_bytes_needed(len: usize) -> WriteResult<usize> {
                    if let TypeMeta::Static { size, .. } = <$type as SchemaWrite<C>>::TYPE_META {
                        return Ok(size);
                    }
                    let Ok(len) = <$type>::try_from(len) else {
                        return Err(write_length_encoding_overflow(type_name::<$type>()));
                    };
                    <$type as SchemaWrite<C>>::size_of(&len)
                }
            }
        )+
    };
}

impl_use_int_primitive!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

/// Fixed-width integer length encoding.
///
/// Integers respect the configured byte order.
///
/// Allows overriding the preallocation size limit per individual use.
///
/// # Examples
///
/// Override the preallocation size limit to 8 bytes.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{containers, len::FixIntLen, SchemaRead, SchemaWrite};
/// type Max8Bytes = FixIntLen<u32, 8>;
///
/// #[derive(SchemaWrite, SchemaRead)]
/// struct OverrideLen {
///     #[wincode(with = "containers::Vec<u8, Max8Bytes>")]
///     bytes: Vec<u8>,
/// }
///
/// let data_ok = OverrideLen { bytes: vec![0; 8] };
/// let serialized = wincode::serialize(&data_ok).unwrap();
/// assert!(wincode::deserialize::<OverrideLen>(&serialized).is_ok());
///
/// let data_err = OverrideLen { bytes: vec![0; 9] };
/// assert!(wincode::serialize(&data_err).is_err());
/// let serialized = wincode::serialize(&vec![0; 9]).unwrap();
/// assert!(wincode::deserialize::<OverrideLen>(&serialized).is_err());
/// # }
/// ```
pub struct FixIntLen<T, const PREALLOCATION_SIZE_LIMIT: usize = PREALLOCATION_SIZE_LIMIT_USE_CONFIG>(
    PhantomData<T>,
);

macro_rules! impl_fix_int {
    ($type:ty) => {
        unsafe impl<const PREALLOCATION_SIZE_LIMIT: usize, C: ConfigCore> SeqLen<C>
            for FixIntLen<$type, PREALLOCATION_SIZE_LIMIT>
        {
            const PREALLOCATION_SIZE_LIMIT_OVERRIDE: PreallocationLimitOverride =
                PreallocationLimitOverride::from_usize(PREALLOCATION_SIZE_LIMIT);

            #[inline(always)]
            #[allow(irrefutable_let_patterns)]
            fn read<'de>(mut reader: impl Reader<'de>) -> ReadResult<usize> {
                let bytes = reader.take_array::<{ size_of::<$type>() }>()?;
                let len = match C::ByteOrder::ENDIAN {
                    Endian::Big => <$type>::from_be_bytes(bytes),
                    Endian::Little => <$type>::from_le_bytes(bytes),
                };
                let Ok(len) = usize::try_from(len) else {
                    return Err(pointer_sized_decode_error());
                };
                Ok(len)
            }

            #[inline(always)]
            fn write(mut writer: impl Writer, len: usize) -> WriteResult<()> {
                let Ok(len) = <$type>::try_from(len) else {
                    return Err(write_length_encoding_overflow(type_name::<$type>()));
                };
                let bytes = match C::ByteOrder::ENDIAN {
                    Endian::Big => len.to_be_bytes(),
                    Endian::Little => len.to_le_bytes(),
                };
                writer.write(&bytes)?;
                Ok(())
            }

            #[inline(always)]
            fn write_bytes_needed(_: usize) -> WriteResult<usize> {
                Ok(size_of::<$type>())
            }
        }
    };
}

impl_fix_int!(u8);
impl_fix_int!(u16);
impl_fix_int!(u32);
impl_fix_int!(u64);
impl_fix_int!(u128);

impl_fix_int!(i8);
impl_fix_int!(i16);
impl_fix_int!(i32);
impl_fix_int!(i64);
impl_fix_int!(i128);

/// Bincode always uses a `u64` encoded with the configuration's integer encoding.
///
/// Allows overriding the preallocation size limit per individual use.
///
/// # Examples
///
/// Override the preallocation size limit to 8 bytes.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::{containers, len::BincodeLen, SchemaRead, SchemaWrite};
/// type Max8Bytes = BincodeLen<8>;
///
/// #[derive(SchemaWrite, SchemaRead)]
/// struct OverrideLen {
///     #[wincode(with = "containers::Vec<u8, Max8Bytes>")]
///     bytes: Vec<u8>,
/// }
///
/// let data_ok = OverrideLen { bytes: vec![0; 8] };
/// let serialized = wincode::serialize(&data_ok).unwrap();
/// assert!(wincode::deserialize::<OverrideLen>(&serialized).is_ok());
///
/// let data_err = OverrideLen { bytes: vec![0; 9] };
/// assert!(wincode::serialize(&data_err).is_err());
/// let serialized = wincode::serialize(&vec![0; 9]).unwrap();
/// assert!(wincode::deserialize::<OverrideLen>(&serialized).is_err());
/// # }
/// ```
pub type BincodeLen<const PREALLOCATION_SIZE_LIMIT: usize = PREALLOCATION_SIZE_LIMIT_USE_CONFIG> =
    UseIntLen<u64, PREALLOCATION_SIZE_LIMIT>;

#[cfg(all(test, any(feature = "std", feature = "indexmap")))]
mod tests {
    use super::unique_key_capacity;

    #[test]
    fn caps_at_representable_key_count() {
        // ZST: 1 value; u8: 256; u16: 65536. `len` below the cap is untouched;
        // 8+ byte keys represent >= usize::MAX values, so no cap applies.
        assert_eq!(unique_key_capacity::<()>(usize::MAX), 1);
        assert_eq!(unique_key_capacity::<()>(0), 0);
        assert_eq!(unique_key_capacity::<u8>(usize::MAX), 256);
        assert_eq!(unique_key_capacity::<u8>(10), 10);
        assert_eq!(unique_key_capacity::<u16>(usize::MAX), 1 << 16);
        assert_eq!(unique_key_capacity::<u64>(usize::MAX), usize::MAX);
        assert_eq!(unique_key_capacity::<[u8; 32]>(12_345), 12_345);
    }
}
