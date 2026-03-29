use {
    crate::{
        SchemaRead, SchemaWrite, TypeMeta,
        config::Config,
        io::{Reader, Writer},
        len::SeqLen,
    },
    core::mem::MaybeUninit,
    smallvec::SmallVec,
};

unsafe impl<T, U, const N: usize, C: Config> SchemaWrite<C> for SmallVec<[T; N]>
where
    T: SchemaWrite<C, Src = U>,
    U: Sized,
{
    type Src = SmallVec<[U; N]>;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> crate::error::WriteResult<usize> {
        if let TypeMeta::Static { size, .. } = T::TYPE_META {
            return Ok(C::LengthEncoding::write_bytes_needed(src.len())? + size * src.len());
        }
        Ok(C::LengthEncoding::write_bytes_needed(src.len())?
            + src
                .iter()
                .map(T::size_of)
                .try_fold(0usize, |acc, item| item.map(|size| acc + size))?)
    }

    #[inline]
    fn write(
        mut writer: impl crate::io::Writer,
        src: &Self::Src,
    ) -> crate::error::WriteResult<()> {
        C::LengthEncoding::prealloc_check::<T>(src.len())?;
        if let TypeMeta::Static { size, .. } = T::TYPE_META {
            let len = src.len();
            #[allow(clippy::arithmetic_side_effects)]
            let needed = C::LengthEncoding::write_bytes_needed_prealloc_check::<T>(len)?
                + size * len;
            // SAFETY: `T::TYPE_META` specifies a static size, so `len` writes of `T::Src`
            // and `LengthEncoding::write` will write `needed` bytes.
            let mut writer = unsafe { writer.as_trusted_for(needed) }?;
            C::LengthEncoding::write(writer.by_ref(), len)?;
            for item in src.iter() {
                T::write(writer.by_ref(), item)?;
            }
            writer.finish()?;
            return Ok(());
        }
        C::LengthEncoding::write(writer.by_ref(), src.len())?;
        for item in src.iter() {
            T::write(writer.by_ref(), item)?;
        }
        Ok(())
    }
}

unsafe impl<'de, T, U, const N: usize, C: Config> SchemaRead<'de, C> for SmallVec<[T; N]>
where
    T: SchemaRead<'de, C, Dst = U>,
{
    type Dst = SmallVec<[U; N]>;

    #[inline]
    fn read(
        mut reader: impl crate::io::Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> crate::error::ReadResult<()> {
        let len = C::LengthEncoding::read_prealloc_check::<U>(reader.by_ref())?;
        let mut values = SmallVec::with_capacity(len);
        if let TypeMeta::Static { size, .. } = T::TYPE_META {
            #[allow(clippy::arithmetic_side_effects)]
            // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
            // fully consume the trusted window.
            let mut reader = unsafe { reader.as_trusted_for(size * len) }?;
            for _ in 0..len {
                values.push(T::get(reader.by_ref())?);
            }
        } else {
            for _ in 0..len {
                values.push(T::get(reader.by_ref())?);
            }
        }
        dst.write(values);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        crate::{deserialize, proptest_config::proptest_cfg, serialize},
        proptest::prelude::*,
        smallvec::{SmallVec, smallvec},
    };

    type SmallVec4<T> = SmallVec<[T; 4]>;

    #[test]
    fn test_smallvec_inline_roundtrip() {
        let value: SmallVec4<u8> = smallvec![1u8, 2, 3];
        let serialized = serialize(&value).unwrap();
        let deserialized: SmallVec4<u8> = deserialize(&serialized).unwrap();
        assert_eq!(deserialized, value);
    }

    #[test]
    fn test_smallvec_spilled_roundtrip() {
        let value: SmallVec4<u8> = smallvec![1u8, 2, 3, 4, 5];
        let serialized = serialize(&value).unwrap();
        let deserialized: SmallVec4<u8> = deserialize(&serialized).unwrap();
        assert_eq!(deserialized, value);
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_smallvec_static(value in proptest::collection::vec(any::<u64>(), 0..=100).prop_map(SmallVec4::from_vec)) {
            let bincode_serialized = bincode::serialize(&value).unwrap();
            let schema_serialized = serialize(&value).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: SmallVec4<u64> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: SmallVec4<u64> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&value, &bincode_deserialized);
            prop_assert_eq!(value, schema_deserialized);
        }

        #[test]
        fn test_smallvec_non_static(value in proptest::collection::vec(any::<String>(), 0..=16).prop_map(SmallVec4::from_vec)) {
            let bincode_serialized = bincode::serialize(&value).unwrap();
            let schema_serialized = serialize(&value).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: SmallVec4<String> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: SmallVec4<String> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&value, &bincode_deserialized);
            prop_assert_eq!(value, schema_deserialized);
        }
    }
}
