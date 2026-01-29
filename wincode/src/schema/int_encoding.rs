//! Integer encoding and byte order configuration.
//!
//! This module defines the [`ByteOrder`] markers and the [`IntEncoding`] trait used
//! by configuration types to control how integers are serialized.
use {
    crate::{
        config::{ConfigCore, ZeroCopy},
        error::invalid_tag_encoding,
        io::{read_size_limit, Reader, Writer},
        ReadResult, WriteResult,
    },
    pastey::paste,
};

/// Byte order trait.
///
/// Used for constraining byte order configuration in type bounds.
pub trait ByteOrder: 'static {
    const ENDIAN: Endian;
}

/// Endianness enum.
///
/// Used for term-level evaluation of byte order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian {
    Big,
    Little,
}

/// Big-endian [`ByteOrder`] marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BigEndian;

/// Marker trait for constraining by platform endianness.
///
/// For example, [`LittleEndian`] only satisfies [`PlatformEndian`] on little-endian platforms.
/// This can be used to, for example, constrain [`ZeroCopy`] implementations only when the
/// configured byte order matches the platform endianness.
///
/// # Safety
///
/// Implementations must ensure that implementations are gated by the correct platform endianness.
pub unsafe trait PlatformEndian {}

#[cfg(target_endian = "big")]
unsafe impl PlatformEndian for BigEndian {}

/// Little-endian [`ByteOrder`] marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LittleEndian;

#[cfg(target_endian = "little")]
unsafe impl PlatformEndian for LittleEndian {}

impl ByteOrder for BigEndian {
    const ENDIAN: Endian = Endian::Big;
}

impl ByteOrder for LittleEndian {
    const ENDIAN: Endian = Endian::Little;
}

/// Implement encoding and decoding using a fixed-width implementation.
///
/// This will use the configured byte order and call the associated
/// `to_be_bytes`, `from_be_bytes`, `to_le_bytes` or `from_le_bytes` method.
macro_rules! impl_fix_int {
    ($byte_order:ty => $($ty:ty),*) => {
        paste! {
            $(
                #[inline(always)]
                fn [<encode_ $ty>] (val: $ty, writer: &mut impl Writer) -> WriteResult<()> {
                    let bytes = match <$byte_order>::ENDIAN {
                        Endian::Big => val.to_be_bytes(),
                        Endian::Little => val.to_le_bytes(),
                    };
                    Ok(writer.write(&bytes)?)
                }

                #[inline(always)]
                fn [<decode_ $ty>] <'de>(reader: &mut impl Reader<'de>) -> ReadResult<$ty> {
                    let bytes = *reader.fill_array::<{ size_of::<$ty>() }>()?;
                    // SAFETY: fill_array is guaranteed to consume `size_of::<$ty>()` bytes.
                    unsafe { reader.consume_unchecked(size_of::<$ty>()) };

                    let val = match <$byte_order>::ENDIAN {
                        Endian::Big => <$ty>::from_be_bytes(bytes),
                        Endian::Little => <$ty>::from_le_bytes(bytes),
                    };

                    Ok(val)
                }

                #[inline(always)]
                fn [<size_of_ $ty>](_val: $ty) -> usize {
                    size_of::<$ty>()
                }
            )*
        }
    };
}

/// Integer encoding trait.
///
/// This trait provides encoding, decoding, and sizing for all integer types.
///
/// # Safety
///
/// Implementors must adhere to the Safety section of the associated constants
/// `STATIC` and `ZERO_COPY`.
///
/// `size_of_*` implementations must always correspond to the number of bytes read by the
/// corresponding `decode_*` and bytes written by the corresponding `encode_*`.
pub unsafe trait IntEncoding<B: ByteOrder>: 'static {
    /// Whether the encoded length for all integer types `T` is constant and equal
    /// to `size_of::<T>()`.
    ///
    /// # SAFETY
    ///
    /// If `STATIC` is `true`, for all integer types `T`, the encoded size must be
    /// constant for all values of `T` and equal to `size_of::<T>()`.
    const STATIC: bool;

    /// Whether the encoding format for integer types `T` matches their in-memory representation.
    ///
    /// # SAFETY
    ///
    /// If `ZERO_COPY` is `true`, for all integer types `T`, the in-memory representation
    /// must correspond exactly to the serialized form, and all byte sequences must
    /// be valid in-memory representations of `T`. This must respect both the
    /// configured byte order and the platform endianness, and any direct reads must
    /// uphold `T`'s alignment requirements.
    const ZERO_COPY: bool;

    /// Encode the given `u16` value and write it to the writer.
    fn encode_u16(val: u16, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u16` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_u16`] function
    /// and read by the [`Self::decode_u16`] function for this particular u16 instance.
    fn size_of_u16(val: u16) -> usize;

    /// Decode a `u16` value from the reader.
    fn decode_u16<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u16>;

    /// Encode a `u32` value and write it to the writer.
    fn encode_u32(val: u32, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u32` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_u32`] function
    /// and read by the [`Self::decode_u32`] function for this particular u32 instance.
    fn size_of_u32(val: u32) -> usize;

    /// Decode a `u32` value from the reader.
    fn decode_u32<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u32>;

    /// Encode a `u64` value and write it to the writer.
    fn encode_u64(val: u64, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u64` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_u64`] function
    /// and read by the [`Self::decode_u64`] function for this particular u64 instance.
    fn size_of_u64(val: u64) -> usize;

    /// Decode a `u64` value from the reader.
    fn decode_u64<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u64>;

    /// Encode a `u128` value and write it to the writer.
    fn encode_u128(val: u128, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u128` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_u128`] function
    /// and read by the [`Self::decode_u128`] function for this particular u128 instance.
    fn size_of_u128(val: u128) -> usize;

    /// Decode a `u128` value from the reader.
    fn decode_u128<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u128>;

    /// Encode a `i16` value and write it to the writer.
    fn encode_i16(val: i16, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i16` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_i16`] function
    /// and read by the [`Self::decode_i16`] function for this particular i16 instance.
    fn size_of_i16(val: i16) -> usize;

    /// Decode a `i16` value from the reader.
    fn decode_i16<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i16>;

    /// Encode a `i32` value and write it to the writer.
    fn encode_i32(val: i32, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i32` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_i32`] function
    /// and read by the [`Self::decode_i32`] function for this particular i32 instance.
    fn size_of_i32(val: i32) -> usize;

    /// Decode a `i32` value from the reader.
    fn decode_i32<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i32>;

    /// Encode a `i64` value and write it to the writer.
    fn encode_i64(val: i64, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i64` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_i64`] function
    /// and read by the [`Self::decode_i64`] function for this particular i64 instance.
    fn size_of_i64(val: i64) -> usize;

    /// Decode a `i64` value from the reader.
    fn decode_i64<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i64>;

    /// Encode a `i128` value and write it to the writer.
    fn encode_i128(val: i128, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i128` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`Self::encode_i128`] function
    /// and read by the [`Self::decode_i128`] function for this particular i128 instance.
    fn size_of_i128(val: i128) -> usize;

    /// Decode a `i128` value from the reader.
    fn decode_i128<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i128>;
}

/// Fixed width integer encoding.
///
/// For all integer types, will encode `to_<byte_order>_bytes` and decode
/// using the corresponding `from_<byte_order>_bytes` method.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FixInt;

unsafe impl IntEncoding<BigEndian> for FixInt {
    const STATIC: bool = true;
    #[cfg(target_endian = "big")]
    const ZERO_COPY: bool = true;
    #[cfg(target_endian = "little")]
    const ZERO_COPY: bool = false;

    impl_fix_int!(BigEndian => u16, u32, u64, u128, i16, i32, i64, i128);
}

unsafe impl IntEncoding<LittleEndian> for FixInt {
    const STATIC: bool = true;
    #[cfg(target_endian = "big")]
    const ZERO_COPY: bool = false;
    #[cfg(target_endian = "little")]
    const ZERO_COPY: bool = true;

    impl_fix_int!(LittleEndian => u16, u32, u64, u128, i16, i32, i64, i128);
}

/// Convenience to allow trait implementations to hook into the configured
/// [`IntEncoding`] and conditionally enable [`ZeroCopy`].
///
/// For example, if a [`SchemaRead`](crate::SchemaRead) / [`SchemaWrite`](crate::SchemaWrite)
/// implementation delegates its integer encoding to the configuration's
/// [`IntEncoding`], it can constrain its [`ZeroCopy`] bound by that encoding.
unsafe impl<C: ConfigCore> ZeroCopy<C> for FixInt where C::ByteOrder: PlatformEndian {}

/// Variable length integer encoding.
///
/// Performance note: variable length integer encoding will hurt serialization and deserialization
/// performance significantly relative to fixed width integer encoding. Additionally, all zero-copy
/// capabilities on integers will be lost. Variable length integer encoding may be beneficial if
/// reducing the resulting size of serialized data is important, but if serialization / deserialization
/// performance is important, fixed width integer encoding is highly recommended.
///
/// Encoding an unsigned integer v (of any type excepting u8) works as follows:
///
/// 1. If `u < 251`, encode it as a single byte with that value.
/// 2. If `251 <= u < 2**16`, encode it as a literal byte 251, followed by a u16 with value `u`.
/// 3. If `2**16 <= u < 2**32`, encode it as a literal byte 252, followed by a u32 with value `u`.
/// 4. If `2**32 <= u < 2**64`, encode it as a literal byte 253, followed by a u64 with value `u`.
/// 5. If `2**64 <= u < 2**128`, encode it as a literal byte 254, followed by a u128 with value `u`.
///
/// Then, for signed integers, we first convert to unsigned using the zigzag algorithm,
/// and then encode them as we do for unsigned integers generally. The reason we use this
/// algorithm is that it encodes those values which are close to zero in less bytes; the
/// obvious algorithm, where we encode the cast values, gives a very large encoding for all
/// negative values.
///
/// The zigzag algorithm is defined as follows:
///
/// ```
/// # type Signed = i32;
/// # type Unsigned = u32;
/// fn zigzag(v: Signed) -> Unsigned {
///     match v {
///         0 => 0,
///         // To avoid the edge case of Signed::min_value()
///         // !n is equal to `-n - 1`, so this is:
///         // !n * 2 + 1 = 2(-n - 1) + 1 = -2n - 2 + 1 = -2n - 1
///         v if v < 0 => !(v as Unsigned) * 2 + 1,
///         v if v > 0 => (v as Unsigned) * 2,
/// #       _ => unreachable!()
///     }
/// }
/// ```
///
/// And works such that:
///
/// ```
/// # let zigzag = |n: i64| -> u64 {
/// #     match n {
/// #         0 => 0,
/// #         v if v < 0 => !(v as u64) * 2 + 1,
/// #         v if v > 0 => (v as u64) * 2,
/// #         _ => unreachable!(),
/// #     }
/// # };
/// assert_eq!(zigzag(0), 0);
/// assert_eq!(zigzag(-1), 1);
/// assert_eq!(zigzag(1), 2);
/// assert_eq!(zigzag(-2), 3);
/// assert_eq!(zigzag(2), 4);
/// // etc
/// assert_eq!(zigzag(i64::min_value()), u64::max_value());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VarInt;

impl VarInt {
    /// Returns the byte discriminant and subsequent byte slice needed to read the value.
    ///
    /// Soft requests (i.e., can return fewer) `size_of::<T>() + 1` bytes with `fill_buf`.
    #[inline]
    fn get_discriminant_and_bytes<'de, T>(
        reader: &mut impl Reader<'de>,
    ) -> ReadResult<(u8, &[u8])> {
        // Fill the buffer with enough bytes to read the discriminant and the value.
        //
        // `fill_buf` returns _up to_ the given number of bytes, so will return fewer at EOF,
        // and wont error if it returns fewer than requested.
        #[expect(clippy::arithmetic_side_effects)]
        let bytes = reader.fill_buf(size_of::<T>() + 1)?;
        let Some((discriminant, bytes)) = bytes.split_at_checked(1) else {
            return Err(read_size_limit(1).into());
        };
        Ok((discriminant[0], bytes))
    }
}

/// Attempt to convert the given byte slice into the target type using configured endianess.
///
/// Errors if the byte slice does not contain enough bytes.
macro_rules! try_from_endian_bytes {
    ($bytes:ident => $ty:ty as $target:ty) => {{
        #[expect(clippy::arithmetic_side_effects)]
        let needed = size_of::<$ty>() + 1;
        let Some(bytes) = $bytes.get(..size_of::<$ty>()) else {
            return Err(read_size_limit(needed).into());
        };
        let Ok(ar) = bytes.try_into() else {
            return Err(read_size_limit(needed).into());
        };
        let val = match B::ENDIAN {
            Endian::Big => <$ty>::from_be_bytes(ar),
            Endian::Little => <$ty>::from_le_bytes(ar),
        };
        (val as $target, needed)
    }};
    ($bytes:ident => $ty:ty) => {{
        try_from_endian_bytes!($bytes => $ty as $ty)
    }};
}

/// Decode zigzag-encoded signed integers using the underlying unsigned VarInt decoder.
macro_rules! varint_decode_signed {
    ($ty:ty => $target:ty) => {
        paste! {
            #[inline]
            fn [<decode_ $ty>]<'de>(reader: &mut impl Reader<'de>) -> ReadResult<$ty> {
                let n = <VarInt as IntEncoding<B>>::[<decode_ $target>](reader)?;
                Ok(if n % 2 == 0 {
                    // positive number
                    (n / 2) as _
                } else {
                    // negative number
                    // !m * 2 + 1 = n
                    // !m * 2 = n - 1
                    // !m = (n - 1) / 2
                    // m = !((n - 1) / 2)
                    // since we have n is odd, we have floor(n / 2) = floor((n - 1) / 2)
                    !(n / 2) as _
                })
            }
        }
    };
}

/// Return the encoded length of zigzag-encoded signed integers.
macro_rules! varint_size_of_signed {
    ($ty:ty => $target:ty) => {
        paste! {
            #[inline]
            #[expect(clippy::arithmetic_side_effects)]
            fn [<size_of_ $ty>](val: $ty) -> usize {
                let n: $target = if val < 0 {
                    (!(val as $target)) * 2 + 1
                } else {
                    (val as $target) * 2
                };
                <VarInt as IntEncoding<B>>::[<size_of_ $target>](n)
            }
        }
    };
}

/// Encode signed integers by zigzag-mapping to the corresponding unsigned [`VarInt`] encoder.
macro_rules! varint_encode_signed {
    ($ty:ty => $target:ty) => {
        paste! {
            #[inline]
            #[expect(clippy::arithmetic_side_effects)]
            fn [<encode_ $ty>](val: $ty, writer: &mut impl Writer) -> WriteResult<()> {
                let n: $target = if val < 0 {
                    (!(val as $target)) * 2 + 1
                } else {
                    (val as $target) * 2
                };
                <VarInt as IntEncoding<B>>::[<encode_ $target>](n, writer)
            }
        }
    };
}

/// Emit tag+payload for unsigned values based on the first matching cast width.
macro_rules! varint_encode_unsigned_impl {
    ($val:ident, $writer:ident, $ty:ty, $tag:ident => $cast:ty) => {{
        let needed = size_of::<$cast>() + 1;
        // SAFETY: tag (1 byte) + payload (`size_of::<$cast>()`) fully initialize the trusted
        // window, so all writes stay within `needed` bytes.
        let writer = &mut unsafe { $writer.as_trusted_for(needed) }?;
        writer.write(&[$tag])?;
        let encoded = $val as $cast;
        let bytes = match B::ENDIAN {
            Endian::Big => encoded.to_be_bytes(),
            Endian::Little => encoded.to_le_bytes(),
        };
        writer.write(&bytes)?;
        writer.finish()?;
        Ok(())
    }};
    ($val:ident, $writer:ident, $ty:ty, $tag:ident => $cast:ty, $($rest_tag:ident => $rest_cast:ty),+ $(,)?) => {{
        if $val <= <$cast>::MAX as $ty {
            let needed = size_of::<$cast>() + 1;
            // SAFETY: tag (1 byte) + payload (`size_of::<$cast>()`) fully initialize the trusted
            // window, so all writes stay within `needed` bytes.
            let writer = &mut unsafe { $writer.as_trusted_for(needed) }?;
            writer.write(&[$tag])?;
            let encoded = $val as $cast;
            let bytes = match B::ENDIAN {
                Endian::Big => encoded.to_be_bytes(),
                Endian::Little => encoded.to_le_bytes(),
            };
            writer.write(&bytes)?;
            writer.finish()?;
            Ok(())
        } else {
            varint_encode_unsigned_impl!($val, $writer, $ty, $($rest_tag => $rest_cast),+)
        }
    }};
}

/// Generate `encode_*` functions for unsigned VarInt encodings using a tag->cast list.
macro_rules! varint_encode_unsigned {
    ($ty:ty, $($tag:ident => $cast:ty),+ $(,)?) => {
        paste! {
            #[inline]
            #[expect(clippy::arithmetic_side_effects)]
            fn [<encode_ $ty>](val: $ty, writer: &mut impl Writer) -> WriteResult<()> {
                if val <= SINGLE_BYTE_MAX as $ty {
                    writer.write(&[val as u8])?;
                    return Ok(());
                }
                varint_encode_unsigned_impl!(val, writer, $ty, $($tag => $cast),+)
            }
        }
    };
}

const SINGLE_BYTE_MAX: u8 = 250;
const U16_BYTE: u8 = 251;
const U32_BYTE: u8 = 252;
const U64_BYTE: u8 = 253;
const U128_BYTE: u8 = 254;

unsafe impl<B: ByteOrder> IntEncoding<B> for VarInt {
    const STATIC: bool = false;

    const ZERO_COPY: bool = false;

    #[inline]
    fn size_of_u16(val: u16) -> usize {
        if val <= SINGLE_BYTE_MAX as u16 {
            1
        } else {
            3
        }
    }

    fn decode_u16<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u16> {
        let (discriminant, bytes) = VarInt::get_discriminant_and_bytes::<u16>(reader)?;
        let (out, used) = match discriminant {
            byte @ 0..=SINGLE_BYTE_MAX => (byte as u16, 1),
            U16_BYTE => try_from_endian_bytes!(bytes => u16),
            byte => return Err(invalid_tag_encoding(byte as usize)),
        };
        // SAFETY: `used` represents the full number of bytes consumed.
        unsafe { reader.consume_unchecked(used) };
        Ok(out)
    }

    varint_encode_unsigned!(u16, U16_BYTE => u16);

    #[inline]
    fn size_of_u32(val: u32) -> usize {
        if val <= SINGLE_BYTE_MAX as u32 {
            1
        } else if val <= u16::MAX as u32 {
            3
        } else {
            5
        }
    }

    fn decode_u32<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u32> {
        let (discriminant, bytes) = VarInt::get_discriminant_and_bytes::<u32>(reader)?;
        let (out, used) = match discriminant {
            byte @ 0..=SINGLE_BYTE_MAX => (byte as u32, 1),
            U16_BYTE => try_from_endian_bytes!(bytes => u16 as u32),
            U32_BYTE => try_from_endian_bytes!(bytes => u32),
            byte => return Err(invalid_tag_encoding(byte as usize)),
        };
        // SAFETY: `used` represents the full number of bytes consumed.
        unsafe { reader.consume_unchecked(used) };
        Ok(out)
    }

    varint_encode_unsigned!(u32, U16_BYTE => u16, U32_BYTE => u32);

    #[inline]
    fn size_of_u64(val: u64) -> usize {
        if val <= SINGLE_BYTE_MAX as u64 {
            1
        } else if val <= u16::MAX as u64 {
            3
        } else if val <= u32::MAX as u64 {
            5
        } else {
            9
        }
    }

    fn decode_u64<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u64> {
        let (discriminant, bytes) = VarInt::get_discriminant_and_bytes::<u64>(reader)?;
        let (out, used) = match discriminant {
            byte @ 0..=SINGLE_BYTE_MAX => (byte as u64, 1),
            U16_BYTE => try_from_endian_bytes!(bytes => u16 as u64),
            U32_BYTE => try_from_endian_bytes!(bytes => u32 as u64),
            U64_BYTE => try_from_endian_bytes!(bytes => u64),
            byte => return Err(invalid_tag_encoding(byte as usize)),
        };
        // SAFETY: `used` represents the full number of bytes consumed.
        unsafe { reader.consume_unchecked(used) };
        Ok(out)
    }

    varint_encode_unsigned!(u64, U16_BYTE => u16, U32_BYTE => u32, U64_BYTE => u64);

    #[inline]
    fn size_of_u128(val: u128) -> usize {
        if val <= SINGLE_BYTE_MAX as u128 {
            1
        } else if val <= u16::MAX as u128 {
            3
        } else if val <= u32::MAX as u128 {
            5
        } else if val <= u64::MAX as u128 {
            9
        } else {
            17
        }
    }

    fn decode_u128<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u128> {
        let (discriminant, bytes) = VarInt::get_discriminant_and_bytes::<u128>(reader)?;
        let (out, used) = match discriminant {
            byte @ 0..=SINGLE_BYTE_MAX => (byte as u128, 1),
            U16_BYTE => try_from_endian_bytes!(bytes => u16 as u128),
            U32_BYTE => try_from_endian_bytes!(bytes => u32 as u128),
            U64_BYTE => try_from_endian_bytes!(bytes => u64 as u128),
            U128_BYTE => try_from_endian_bytes!(bytes => u128),
            byte => return Err(invalid_tag_encoding(byte as usize)),
        };
        // SAFETY: `used` represents the full number of bytes consumed.
        unsafe { reader.consume_unchecked(used) };
        Ok(out)
    }

    varint_encode_unsigned!(
        u128,
        U16_BYTE => u16,
        U32_BYTE => u32,
        U64_BYTE => u64,
        U128_BYTE => u128,
    );

    varint_size_of_signed!(i16 => u16);
    varint_size_of_signed!(i32 => u32);
    varint_size_of_signed!(i64 => u64);
    varint_size_of_signed!(i128 => u128);

    varint_encode_signed!(i16 => u16);
    varint_encode_signed!(i32 => u32);
    varint_encode_signed!(i64 => u64);
    varint_encode_signed!(i128 => u128);

    varint_decode_signed!(i16 => u16);
    varint_decode_signed!(i32 => u32);
    varint_decode_signed!(i64 => u64);
    varint_decode_signed!(i128 => u128);
}
