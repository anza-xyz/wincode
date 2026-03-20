use {
    crate::{
        ReadResult, SchemaRead, SchemaWrite, WriteResult,
        config::Config,
        error::invalid_utf8_encoding,
        io::{BorrowKind, Reader, Writer},
        len::SeqLen,
    },
    alloc::vec::Vec,
    core::{mem::MaybeUninit, str},
    ecow::EcoString,
};

unsafe impl<C: Config> SchemaWrite<C> for EcoString {
    type Src = Self;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <str as SchemaWrite<C>>::size_of(src.as_str())
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        C::LengthEncoding::prealloc_check::<u8>(src.len())?;
        <str as SchemaWrite<C>>::write(writer, src.as_str())
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for EcoString {
    type Dst = Self;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = C::LengthEncoding::read_prealloc_check::<u8>(reader.by_ref())?;

        if reader.supports_borrow(BorrowKind::CallSite) {
            let bytes = reader.take_scoped(len)?;
            let string = str::from_utf8(bytes).map_err(invalid_utf8_encoding)?;
            dst.write(EcoString::from(string));
            return Ok(());
        }

        if len <= EcoString::INLINE_LIMIT {
            let mut buf = [MaybeUninit::uninit(); EcoString::INLINE_LIMIT];
            reader.copy_into_slice(&mut buf[..len])?;
            // SAFETY: `copy_into_slice` initialized the first `len` bytes of `buf`.
            let bytes = unsafe { core::slice::from_raw_parts(buf.as_ptr().cast::<u8>(), len) };
            let string = str::from_utf8(bytes).map_err(invalid_utf8_encoding)?;
            dst.write(EcoString::from(string));
            Ok(())
        } else {
            let mut bytes = Vec::with_capacity(len);
            reader.copy_into_slice(&mut bytes.spare_capacity_mut()[..len])?;
            // SAFETY: `copy_into_slice` fills the entire spare-capacity slice.
            unsafe { bytes.set_len(len) };
            let string = str::from_utf8(&bytes).map_err(invalid_utf8_encoding)?;
            dst.write(EcoString::from(string));
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{
            deserialize, io::test_util::NoBorrowReader, proptest_config::proptest_cfg, serialize,
        },
        proptest::prelude::*,
    };

    #[test]
    fn test_small_string_roundtrip() {
        let value = EcoString::from("hello");
        let serialized = serialize(&value).unwrap();
        let deserialized = deserialize::<EcoString>(&serialized).unwrap();
        assert_eq!(deserialized, value);
    }

    #[test]
    fn test_same_encoding_as_string() {
        proptest!(proptest_cfg(), |(value: String)| {
            let eco = EcoString::from(value.as_str());
            let eco_serialized = serialize(&eco).unwrap();
            let string_serialized = serialize(&value).unwrap();
            prop_assert_eq!(&eco_serialized, &string_serialized);

            let deserialized = deserialize::<EcoString>(&eco_serialized).unwrap();
            prop_assert_eq!(deserialized, eco);
        });
    }

    #[test]
    fn test_bincode_compat() {
        proptest!(proptest_cfg(), |(value: String)| {
            let eco = EcoString::from(value.as_str());
            let bincode_serialized = bincode::serialize(&eco).unwrap();
            let wincode_serialized = serialize(&eco).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let bincode_deserialized: EcoString = bincode::deserialize(&bincode_serialized).unwrap();
            let wincode_deserialized: EcoString = deserialize(&wincode_serialized).unwrap();
            prop_assert_eq!(&wincode_deserialized, &eco);
            prop_assert_eq!(&wincode_deserialized, &bincode_deserialized);
        });
    }

    #[test]
    fn test_roundtrip_without_take_scoped_support() {
        proptest!(proptest_cfg(), |(value: String)| {
            let eco = EcoString::from(value.as_str());
            let serialized = serialize(&eco).unwrap();
            let reader = NoBorrowReader::new(&serialized);
            let deserialized: EcoString = crate::deserialize_from(reader).unwrap();
            prop_assert_eq!(deserialized, eco);
        });
    }
}
