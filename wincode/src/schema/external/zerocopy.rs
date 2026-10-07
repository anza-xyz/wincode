//! Support for `zerocopy`'s byte-order-aware numeric types.
//!
//! Each type is encoded as its in-memory bytes, regardless of the configured
//! integer encoding or byte order: these types already fix their byte order, and
//! have alignment 1. They are therefore zero-copy under every configuration, and a
//! `#[repr(C)]` struct of them has no padding and can be borrowed from any offset.
//!
//! Under the default configuration on little-endian targets, `U64<LittleEndian>`
//! encodes exactly as `u64` does.
use {
    crate::{
        TypeMeta,
        config::{ConfigCore, ZeroCopy},
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
    },
    core::mem::MaybeUninit,
    zerocopy::byteorder::{ByteOrder, F32, F64, I16, I32, I64, I128, U16, U32, U64, U128},
};

macro_rules! impl_byteorder {
    ($($ty:ident),* $(,)?) => {$(
        // SAFETY:
        // - `$ty<O>` is a `#[repr(transparent)]` wrapper over `[u8; N]`: alignment 1, no
        //   padding, every bit pattern valid, and no pointers.
        // - Its in-memory bytes are exactly what `write` writes.
        unsafe impl<O: ByteOrder + 'static, C: ConfigCore> ZeroCopy<C> for $ty<O> {}

        unsafe impl<O: ByteOrder, C: ConfigCore> SchemaWrite<C> for $ty<O> {
            type Src = Self;

            const TYPE_META: TypeMeta = TypeMeta::Static {
                size: size_of::<Self>(),
                zero_copy: true,
            };

            #[inline]
            fn size_of(_src: &Self::Src) -> WriteResult<usize> {
                Ok(size_of::<Self>())
            }

            #[inline]
            fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
                writer.write(&src.to_bytes())?;
                Ok(())
            }
        }

        unsafe impl<'de, O: ByteOrder, C: ConfigCore> SchemaRead<'de, C> for $ty<O> {
            type Dst = Self;

            const TYPE_META: TypeMeta = TypeMeta::Static {
                size: size_of::<Self>(),
                zero_copy: true,
            };

            #[inline]
            fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                dst.write(Self::from_bytes(reader.take_array()?));
                Ok(())
            }
        }
    )*};
}

impl_byteorder!(U16, U32, U64, U128, I16, I32, I64, I128, F32, F64);

#[cfg(test)]
mod tests {
    use {
        crate::{
            SchemaRead, SchemaWrite, ZeroCopy, deserialize, proptest_config::proptest_cfg,
            serialize,
        },
        proptest::prelude::*,
        zerocopy::byteorder::{BE, F64, I128, LE, U16, U64},
    };

    #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
    #[wincode(internal, assert_zero_copy)]
    #[repr(C)]
    struct Unaligned {
        tag: u8,
        amount: U64<LE>,
        port: U16<BE>,
        delta: I128<LE>,
    }

    #[test]
    fn test_byteorder_roundtrip() {
        proptest!(proptest_cfg(), |(a: u64, b: u16, c: i128, d: f64)| {
            let value = (U64::<LE>::new(a), U16::<BE>::new(b), I128::<BE>::new(c), F64::<LE>::new(d));
            let serialized = serialize(&value).unwrap();
            prop_assert_eq!(serialized.len(), 8 + 2 + 16 + 8);
            let deserialized: (U64<LE>, U16<BE>, I128<BE>, F64<LE>) = deserialize(&serialized).unwrap();
            prop_assert_eq!(value.0, deserialized.0);
            prop_assert_eq!(value.1, deserialized.1);
            prop_assert_eq!(value.2, deserialized.2);
            prop_assert_eq!(value.3.get().to_bits(), deserialized.3.get().to_bits());
        });
    }

    #[test]
    fn test_byteorder_is_its_bytes() {
        proptest!(proptest_cfg(), |(value: u16)| {
            prop_assert_eq!(serialize(&U16::<BE>::new(value)).unwrap(), value.to_be_bytes());
            prop_assert_eq!(serialize(&U16::<LE>::new(value)).unwrap(), value.to_le_bytes());
        });
    }

    #[cfg(target_endian = "little")]
    #[test]
    fn test_byteorder_le_matches_native() {
        proptest!(proptest_cfg(), |(value: u64)| {
            prop_assert_eq!(serialize(&U64::<LE>::new(value)).unwrap(), serialize(&value).unwrap());
        });
    }

    #[test]
    fn test_byteorder_struct_zero_copy_unaligned() {
        proptest!(proptest_cfg(), |(tag: u8, amount: u64, port: u16, delta: i128)| {
            let value = Unaligned {
                tag,
                amount: U64::new(amount),
                port: U16::new(port),
                delta: I128::new(delta),
            };
            // Borrow from an odd offset: alignment 1 makes any offset valid.
            let mut bytes = vec![0];
            bytes.extend(serialize(&value).unwrap());
            prop_assert_eq!(Unaligned::from_bytes(&bytes[1..]).unwrap(), &value);

            let amount: &U64<LE> = deserialize(&bytes[2..]).unwrap();
            prop_assert_eq!(amount.get(), value.amount.get());
        });
    }
}
