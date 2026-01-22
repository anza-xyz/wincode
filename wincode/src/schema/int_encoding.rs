//! Integer encoding and byte order configuration.
//!
//! This module defines the [`ByteOrder`] markers and the [`IntEncoding`] trait used
//! by configuration types to control how integers are serialized.
use {
    crate::{
        config::{ConfigCore, ZeroCopy},
        io::{Reader, Writer},
        ReadResult, WriteResult,
    },
    paste::paste,
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
/// # SAFETY
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
    /// Must return the exact number of bytes written by the [`encode_u16`] function
    /// and read by the [`decode_u16`] function for this particular u16 instance.
    fn size_of_u16(val: u16) -> usize;

    /// Decode a `u16` value from the reader.
    fn decode_u16<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u16>;

    /// Encode a `u32` value and write it to the writer.
    fn encode_u32(val: u32, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u32` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_u32`] function
    /// and read by the [`decode_u32`] function for this particular u32 instance.
    fn size_of_u32(val: u32) -> usize;

    /// Decode a `u32` value from the reader.
    fn decode_u32<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u32>;

    /// Encode a `u64` value and write it to the writer.
    fn encode_u64(val: u64, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u64` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_u64`] function
    /// and read by the [`decode_u64`] function for this particular u64 instance.
    fn size_of_u64(val: u64) -> usize;

    /// Decode a `u64` value from the reader.
    fn decode_u64<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u64>;

    /// Encode a `u128` value and write it to the writer.
    fn encode_u128(val: u128, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `u128` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_u128`] function
    /// and read by the [`decode_u128`] function for this particular u128 instance.
    fn size_of_u128(val: u128) -> usize;

    /// Decode a `u128` value from the reader.
    fn decode_u128<'de>(reader: &mut impl Reader<'de>) -> ReadResult<u128>;

    /// Encode a `i16` value and write it to the writer.
    fn encode_i16(val: i16, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i16` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_i16`] function
    /// and read by the [`decode_i16`] function for this particular i16 instance.
    fn size_of_i16(val: i16) -> usize;

    /// Decode a `i16` value from the reader.
    fn decode_i16<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i16>;

    /// Encode a `i32` value and write it to the writer.
    fn encode_i32(val: i32, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i32` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_i32`] function
    /// and read by the [`decode_i32`] function for this particular i32 instance.
    fn size_of_i32(val: i32) -> usize;

    /// Decode a `i32` value from the reader.
    fn decode_i32<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i32>;

    /// Encode a `i64` value and write it to the writer.
    fn encode_i64(val: i64, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i64` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_i64`] function
    /// and read by the [`decode_i64`] function for this particular i64 instance.
    fn size_of_i64(val: i64) -> usize;

    /// Decode a `i64` value from the reader.
    fn decode_i64<'de>(reader: &mut impl Reader<'de>) -> ReadResult<i64>;

    /// Encode a `i128` value and write it to the writer.
    fn encode_i128(val: i128, writer: &mut impl Writer) -> WriteResult<()>;

    /// Get the encoded size of the given `i128` value.
    ///
    /// # SAFETY
    ///
    /// Must return the exact number of bytes written by the [`encode_i128`] function
    /// and read by the [`decode_i128`] function for this particular i128 instance.
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
