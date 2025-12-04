//! Support for heterogenous sequence length encoding.
use crate::{
    error::{pointer_sized_decode_error, preallocation_size_limit, ReadResult, WriteResult},
    io::{Reader, Writer},
    schema::{SchemaRead, SchemaWrite},
};

/// Behavior to support heterogenous sequence length encoding.
///
/// It is possible for sequences to have different length encoding schemes.
/// This trait abstracts over that possibility, allowing users to specify
/// the length encoding scheme for a sequence.
pub trait SeqLen {
    /// Read the length of a sequence from the reader, where
    /// `T` is the type of the sequence elements. This can be used to
    /// enforce size constraints for preallocations.
    ///
    /// May return an error if some length condition is not met
    /// (e.g., size constraints, overflow, etc.).
    fn read<'de, T>(reader: &mut impl Reader<'de>) -> ReadResult<usize>;
    /// Write the length of a sequence to the writer.
    fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()>;
    /// Calculate the number of bytes needed to write the given length.
    ///
    /// Useful for variable length encoding schemes.
    fn write_bytes_needed(len: usize) -> WriteResult<usize>;
}

const DEFAULT_BINCODE_LEN_MAX_SIZE: usize = 4 << 20; // 4 MiB
/// [`SeqLen`] implementation for bincode's default fixint encoding.
///
/// The `MAX_SIZE` constant is a limit on the maximum preallocation size
/// (in bytes) for heap allocated structures. This is a safety precaution
/// against malicious input causing OOM. The default is 4 MiB. Users are
/// free to override this limit by passing a different constant or by
/// implementing their own `SeqLen` implementation.
pub struct BincodeLen<const MAX_SIZE: usize = DEFAULT_BINCODE_LEN_MAX_SIZE>;

impl<const MAX_SIZE: usize> SeqLen for BincodeLen<MAX_SIZE> {
    #[inline(always)]
    fn read<'de, T>(reader: &mut impl Reader<'de>) -> ReadResult<usize> {
        // Bincode's default fixint encoding writes lengths as `u64`.
        let len = u64::get(reader)
            .and_then(|len| usize::try_from(len).map_err(|_| pointer_sized_decode_error()))?;
        let needed = len
            .checked_mul(size_of::<T>())
            .ok_or_else(|| preallocation_size_limit(usize::MAX, MAX_SIZE))?;
        if needed > MAX_SIZE {
            return Err(preallocation_size_limit(needed, MAX_SIZE));
        }
        Ok(len)
    }

    #[inline(always)]
    fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()> {
        u64::write(writer, &(len as u64))
    }

    #[inline(always)]
    fn write_bytes_needed(_len: usize) -> WriteResult<usize> {
        Ok(size_of::<u64>())
    }
}

#[cfg(feature = "solana-short-vec")]
pub mod short_vec {
    use {
        super::*,
        crate::error::{read_length_encoding_overflow, write_length_encoding_overflow},
        core::{
            mem::{transmute, MaybeUninit},
            ptr,
        },
        solana_short_vec::{decode_shortu16_len, ShortU16},
    };

    impl<'de> SchemaRead<'de> for ShortU16 {
        type Dst = Self;

        fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
            let Ok((len, read)) = decode_shortu16_len(reader.fill_buf(3)?) else {
                return Err(read_length_encoding_overflow("u16::MAX"));
            };

            // SAFETY: `read` is the number of bytes visited by `decode_shortu16_len` to decode the length,
            // which implies the reader had at least `read` bytes available.
            unsafe { reader.consume_unchecked(read) };

            // SAFETY: `dst` is a valid pointer to a `MaybeUninit<ShortU16>`.
            let slot = unsafe { &mut *(&raw mut (*dst.as_mut_ptr()).0).cast::<MaybeUninit<u16>>() };
            // SAFETY: `len` is always a valid u16. `decode_shortu16_len` casts it to a usize before returning,
            // so no risk of overflow.
            slot.write(len as u16);
            Ok(())
        }
    }

    impl SchemaWrite for ShortU16 {
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

    pub type ShortU16Len = ShortU16;

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

    impl SeqLen for ShortU16Len {
        #[inline(always)]
        fn read<'de, T>(reader: &mut impl Reader<'de>) -> ReadResult<usize> {
            let Ok((len, read)) = decode_shortu16_len(reader.fill_buf(3)?) else {
                return Err(read_length_encoding_overflow("u16::MAX"));
            };
            unsafe { reader.consume_unchecked(read) };
            Ok(len)
        }

        #[inline(always)]
        fn write(writer: &mut impl Writer, len: usize) -> WriteResult<()> {
            if len > u16::MAX as usize {
                return Err(write_length_encoding_overflow("u16::MAX"));
            }

            <ShortU16 as SchemaWrite>::write(writer, &ShortU16(len as u16))
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
            #[wincode(with = "containers::Vec<Pod<u8>, ShortU16Len>")]
            bytes: Vec<u8>,
            #[serde(with = "solana_short_vec")]
            #[wincode(with = "containers::Vec<Pod<[u8; 32]>, ShortU16Len>")]
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
