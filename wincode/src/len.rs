//! Support for heterogenous sequence length encoding.
use {
    crate::{
        config::{ConfigCore, PREALLOCATION_SIZE_LIMIT_DISABLED},
        error::{
            pointer_sized_decode_error, preallocation_size_limit, write_length_encoding_overflow,
            PreallocationError, ReadResult, WriteResult,
        },
        int_encoding::{ByteOrder, Endian},
        io::{Reader, Writer},
        SchemaRead, SchemaWrite, TypeMeta,
    },
    core::{any::type_name, marker::PhantomData},
};

pub const PREALLOCATION_SIZE_LIMIT_USE_CONFIG: usize = 0;

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
            check(len, size_of::<T>(), prealloc_limit)?;
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
    fn read_prealloc_check<'de, T>(reader: &mut impl Reader<'de>) -> ReadResult<usize> {
        let len = Self::read(reader)?;
        Self::prealloc_check::<T>(len)?;
        Ok(len)
    }
    /// Read the length of a sequence, without doing any preallocation size checks.
    ///
    /// Note this may still return typical read errors and there is no unsafety implied.
    fn read<'de>(reader: &mut impl Reader<'de>) -> ReadResult<usize>;
    /// Write the length of a sequence to the writer.
    fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()>;
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
    fn read<'de>(reader: &mut impl Reader<'de>) -> ReadResult<usize> {
        let len = T::get(reader)?;
        let Ok(len) = usize::try_from(len) else {
            return Err(pointer_sized_decode_error());
        };
        Ok(len)
    }

    #[inline(always)]
    fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()> {
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
            fn read<'de>(reader: &mut impl Reader<'de>) -> ReadResult<usize> {
                let bytes = reader.fill_array::<{ size_of::<$type>() }>()?;
                let len = match C::ByteOrder::ENDIAN {
                    Endian::Big => <$type>::from_be_bytes(*bytes),
                    Endian::Little => <$type>::from_le_bytes(*bytes),
                };
                // SAFETY: `fill_array` ensures we read exactly `size_of::<$type>()` bytes.
                unsafe { reader.consume_unchecked(size_of::<$type>()) };
                let Ok(len) = usize::try_from(len) else {
                    return Err(pointer_sized_decode_error());
                };
                Ok(len)
            }

            #[inline(always)]
            fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()> {
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
/// ```
pub type BincodeLen<const PREALLOCATION_SIZE_LIMIT: usize = PREALLOCATION_SIZE_LIMIT_USE_CONFIG> =
    UseIntLen<u64, PREALLOCATION_SIZE_LIMIT>;

#[cfg(feature = "solana-short-vec")]
pub mod short_vec {
    pub use solana_short_vec::ShortU16;
    use {
        super::*,
        crate::error::write_length_encoding_overflow,
        core::{
            mem::{transmute, MaybeUninit},
            ptr,
        },
    };

    unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for ShortU16 {
        type Dst = Self;

        #[inline]
        fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
            let len = decode_short_u16_from_reader(reader)?;
            // SAFETY: `dst` is a valid pointer to a `MaybeUninit<ShortU16>`.
            let slot = unsafe { &mut *(&raw mut (*dst.as_mut_ptr()).0).cast::<MaybeUninit<u16>>() };
            slot.write(len);
            Ok(())
        }
    }

    unsafe impl<C: ConfigCore> SchemaWrite<C> for ShortU16 {
        type Src = Self;

        fn size_of(src: &Self::Src) -> WriteResult<usize> {
            Ok(short_u16_bytes_needed(src.0))
        }

        fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
            let val = src.0;
            let needed = short_u16_bytes_needed(val);
            let mut buf = [MaybeUninit::<u8>::uninit(); 3];
            // SAFETY: short_u16 uses a maximum of 3 bytes, so the buffer is always large enough.
            unsafe { encode_short_u16(buf.as_mut_ptr().cast::<u8>(), needed, val) };
            // SAFETY: encode_short_u16 writes exactly `needed` bytes.
            let buf =
                unsafe { transmute::<&[MaybeUninit<u8>], &[u8]>(buf.get_unchecked(..needed)) };
            writer.write(buf)?;
            Ok(())
        }
    }

    /// Branchless computation of the number of bytes needed to encode a short u16.
    ///
    /// See [`solana_short_vec::ShortU16`] for more details.
    #[inline(always)]
    #[allow(clippy::arithmetic_side_effects)]
    fn short_u16_bytes_needed(len: u16) -> usize {
        1 + (len >= 0x80) as usize + (len >= 0x4000) as usize
    }

    #[inline(always)]
    fn try_short_u16_bytes_needed<T: TryInto<u16>>(len: T) -> WriteResult<usize> {
        match len.try_into() {
            Ok(len) => Ok(short_u16_bytes_needed(len)),
            Err(_) => Err(write_length_encoding_overflow("u16::MAX")),
        }
    }

    /// Encode a short u16 into the given buffer.
    ///
    /// See [`solana_short_vec::ShortU16`] for more details.
    ///
    /// # Safety
    ///
    /// - `dst` must be a valid for writes.
    /// - `dst` must be valid for `needed` bytes.
    #[inline(always)]
    unsafe fn encode_short_u16(dst: *mut u8, needed: usize, len: u16) {
        // From `solana_short_vec`:
        //
        // u16 serialized with 1 to 3 bytes. If the value is above
        // 0x7f, the top bit is set and the remaining value is stored in the next
        // bytes. Each byte follows the same pattern until the 3rd byte. The 3rd
        // byte may only have the 2 least-significant bits set, otherwise the encoded
        // value will overflow the u16.
        match needed {
            1 => ptr::write(dst, len as u8),
            2 => {
                ptr::write(dst, ((len & 0x7f) as u8) | 0x80);
                ptr::write(dst.add(1), (len >> 7) as u8);
            }
            3 => {
                ptr::write(dst, ((len & 0x7f) as u8) | 0x80);
                ptr::write(dst.add(1), (((len >> 7) & 0x7f) as u8) | 0x80);
                ptr::write(dst.add(2), (len >> 14) as u8);
            }
            _ => unreachable!(),
        }
    }

    /// Decodes a ShortU16 from a byte slice, returning the decoded u16 and the number of bytes read.
    ///
    /// This implementation is bit-for-bit compatible with Solana's encoding rules (strict canonical form,
    /// max 3 bytes, overflow checks).
    ///
    /// # Examples
    ///
    /// ```
    /// use wincode::len::decode_short_u16;
    ///
    /// let bytes = [0x7f];
    /// let (len, read) = decode_short_u16(&bytes).unwrap();
    /// assert_eq!(len, 127);
    /// assert_eq!(read, 1);
    /// ```
    ///
    /// ```
    /// use wincode::len::decode_short_u16;
    ///
    /// let bytes = [0x80, 0x01];
    /// let (len, read) = decode_short_u16(&bytes).unwrap();
    /// assert_eq!(len, 128);
    /// assert_eq!(read, 2);
    /// ```
    ///
    /// ```
    /// use wincode::len::decode_short_u16;
    ///
    /// let bytes = [0x80, 0x80, 0x01];
    /// let (len, read) = decode_short_u16(&bytes).unwrap();
    /// assert_eq!(len, 16384);
    /// assert_eq!(read, 3);
    /// ```
    #[inline]
    pub const fn decode_short_u16(bytes: &[u8]) -> ReadResult<(u16, usize)> {
        use crate::error::ReadError;

        #[cold]
        const fn overflow_err() -> ReadError {
            ReadError::LengthEncodingOverflow("u16::MAX")
        }

        #[cold]
        const fn non_canonical_err() -> ReadError {
            ReadError::InvalidValue("short u16: non-canonical encoding")
        }

        #[cold]
        const fn incomplete_err() -> ReadError {
            ReadError::InvalidValue("short u16: unexpected end of input")
        }

        // Byte 0
        if bytes.is_empty() {
            return Err(incomplete_err());
        }
        let b0 = bytes[0];
        if b0 < 0x80 {
            return Ok((b0 as u16, 1));
        }

        // Byte 1
        if bytes.len() < 2 {
            return Err(incomplete_err());
        }
        let b1 = bytes[1];
        if b1 == 0 {
            return Err(non_canonical_err());
        }
        if b1 < 0x80 {
            let val = ((b0 & 0x7f) as u16) | ((b1 as u16) << 7);
            return Ok((val, 2));
        }

        // Byte 2
        if bytes.len() < 3 {
            return Err(incomplete_err());
        }
        let b2 = bytes[2];
        if b2 == 0 {
            return Err(non_canonical_err());
        }
        if b2 > 3 {
            return Err(overflow_err());
        }
        let val = ((b0 & 0x7f) as u16) | (((b1 & 0x7f) as u16) << 7) | ((b2 as u16) << 14);
        Ok((val, 3))
    }

    #[inline]
    fn decode_short_u16_from_reader<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u16> {
        let (len, read) = decode_short_u16(reader.fill_buf(3)?)?;
        // SAFETY: `read` is the number of bytes visited by `decode_shortu16` to decode the length,
        // which implies the reader had at least `read` bytes available.
        unsafe { reader.consume_unchecked(read) };
        Ok(len)
    }

    unsafe impl<C: ConfigCore> SeqLen<C> for ShortU16 {
        #[inline(always)]
        fn read<'de>(reader: &mut impl Reader<'de>) -> ReadResult<usize> {
            Ok(decode_short_u16_from_reader(reader)? as usize)
        }

        #[inline(always)]
        fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()> {
            if len > u16::MAX as usize {
                return Err(write_length_encoding_overflow("u16::MAX"));
            }

            <ShortU16 as SchemaWrite<C>>::write(writer, &ShortU16(len as u16))
        }

        #[inline(always)]
        fn write_bytes_needed(len: usize) -> WriteResult<usize> {
            try_short_u16_bytes_needed(len)
        }
    }

    #[cfg(all(test, feature = "alloc", feature = "derive"))]
    mod tests {
        use {
            super::*,
            crate::{
                containers::{self, Pod},
                proptest_config::proptest_cfg,
            },
            alloc::vec::Vec,
            proptest::prelude::*,
            solana_short_vec::ShortU16,
            wincode_derive::{SchemaRead, SchemaWrite},
        };

        fn our_short_u16_encode(len: u16) -> Vec<u8> {
            let needed = short_u16_bytes_needed(len);
            let mut buf = Vec::with_capacity(needed);
            unsafe {
                encode_short_u16(buf.as_mut_ptr(), needed, len);
                buf.set_len(needed);
            }
            buf
        }

        #[derive(
            serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq, SchemaWrite, SchemaRead,
        )]
        #[wincode(internal)]
        struct ShortVecStruct {
            #[serde(with = "solana_short_vec")]
            #[wincode(with = "containers::Vec<Pod<u8>, ShortU16>")]
            bytes: Vec<u8>,
            #[serde(with = "solana_short_vec")]
            #[wincode(with = "containers::Vec<Pod<[u8; 32]>, ShortU16>")]
            ar: Vec<[u8; 32]>,
        }

        #[derive(SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize)]
        #[wincode(internal)]
        struct ShortVecAsSchema {
            short_u16: ShortU16,
        }

        fn strat_short_vec_struct() -> impl Strategy<Value = ShortVecStruct> {
            (
                proptest::collection::vec(any::<u8>(), 0..=100),
                proptest::collection::vec(any::<[u8; 32]>(), 0..=16),
            )
                .prop_map(|(bytes, ar)| ShortVecStruct { bytes, ar })
        }

        proptest! {
            #![proptest_config(proptest_cfg())]

            #[test]
            fn encode_u16_equivalence(len in 0..=u16::MAX) {
                let our = our_short_u16_encode(len);
                let bincode = bincode::serialize(&ShortU16(len)).unwrap();
                prop_assert_eq!(our, bincode);
            }

            #[test]
            fn test_short_vec_struct(short_vec_struct in strat_short_vec_struct()) {
                let bincode_serialized = bincode::serialize(&short_vec_struct).unwrap();
                let schema_serialized = crate::serialize(&short_vec_struct).unwrap();
                prop_assert_eq!(&bincode_serialized, &schema_serialized);
                let bincode_deserialized: ShortVecStruct = bincode::deserialize(&bincode_serialized).unwrap();
                let schema_deserialized: ShortVecStruct = crate::deserialize(&schema_serialized).unwrap();
                prop_assert_eq!(&short_vec_struct, &bincode_deserialized);
                prop_assert_eq!(short_vec_struct, schema_deserialized);
            }

            #[test]
            fn encode_decode_short_u16_roundtrip(len in 0..=u16::MAX) {
                let our = our_short_u16_encode(len);
                let (decoded_len, read) = decode_short_u16(&our).unwrap();
                let (sdk_decoded_len, sdk_read) = solana_short_vec::decode_shortu16_len(&our).unwrap();
                let sdk_decoded_len = sdk_decoded_len as u16;
                prop_assert_eq!(len, decoded_len);
                prop_assert_eq!(len, sdk_decoded_len);
                prop_assert_eq!(read, sdk_read);
            }

            #[test]
            fn decode_short_u16_err_equivalence(bytes in prop::collection::vec(any::<u8>(), 0..=3)) {
                let our_decode = decode_short_u16(&bytes);
                let sdk_decode = solana_short_vec::decode_shortu16_len(&bytes);
                prop_assert_eq!(our_decode.is_err(), sdk_decode.is_err());
                prop_assert_eq!(our_decode.is_ok(), sdk_decode.is_ok());
            }

            #[test]
            fn test_short_vec_as_schema(sv in any::<u16>()) {
                let val = ShortVecAsSchema { short_u16: ShortU16(sv) };
                let bincode_serialized = bincode::serialize(&val).unwrap();
                let wincode_serialized = crate::serialize(&val).unwrap();
                prop_assert_eq!(&bincode_serialized, &wincode_serialized);
                let bincode_deserialized: ShortVecAsSchema = bincode::deserialize(&bincode_serialized).unwrap();
                let wincode_deserialized: ShortVecAsSchema = crate::deserialize(&wincode_serialized).unwrap();
                prop_assert_eq!(val.short_u16.0, bincode_deserialized.short_u16.0);
                prop_assert_eq!(val.short_u16.0, wincode_deserialized.short_u16.0);
            }
        }
    }
}

#[cfg(feature = "solana-short-vec")]
pub use short_vec::*;
