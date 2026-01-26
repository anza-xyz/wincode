#[cfg(feature = "uuid-serde-compat")]
use crate::len::SeqLen;
#[cfg(not(feature = "uuid-serde-compat"))]
use crate::schema::TypeMeta;
use {
    crate::{
        config::Config,
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
    },
    core::mem::MaybeUninit,
    uuid::Uuid,
};

#[cfg(feature = "uuid")]
unsafe impl<'de, C: Config> SchemaRead<'de, C> for Uuid {
    type Dst = Uuid;

    // serde serializes byte slices as a length-prefixed array.
    // As such, it must fall back to TypeMeta::Dynamic when `uuid-serde-compat`
    // is enabled. Otherwise, we can enable static and zero-copy.
    #[cfg(not(feature = "uuid-serde-compat"))]
    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: size_of::<Uuid>(),
        zero_copy: true,
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // serde serializes byte slices as a length-prefixed array.
        #[cfg(feature = "uuid-serde-compat")]
        let _len = C::LengthEncoding::read(reader)?;
        let bytes = *reader.fill_array::<{ size_of::<Uuid>() }>()?;
        // SAFETY: `fill_array` guarantees we get exactly `size_of::<Uuid>()` bytes.
        unsafe { reader.consume_unchecked(size_of::<Uuid>()) };
        dst.write(Uuid::from_bytes(bytes));
        Ok(())
    }
}

#[cfg(feature = "uuid")]
unsafe impl<C: Config> SchemaWrite<C> for Uuid {
    type Src = Uuid;

    // serde serializes byte slices as a length-prefixed array.
    // As such, it must fall back to TypeMeta::Dynamic when `uuid-serde-compat`
    // is enabled. Otherwise we enable static and zero-copy.
    #[cfg(not(feature = "uuid-serde-compat"))]
    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: size_of::<Uuid>(),
        zero_copy: true,
    };

    #[cfg(feature = "uuid-serde-compat")]
    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        // serde serializes byte slices as a length-prefixed array.
        let len_bytes = C::LengthEncoding::write_bytes_needed(size_of::<Uuid>())?;
        Ok(len_bytes + size_of::<Uuid>())
    }

    #[cfg(not(feature = "uuid-serde-compat"))]
    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(size_of::<Uuid>())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        #[cfg(feature = "uuid-serde-compat")]
        C::LengthEncoding::write(writer, size_of::<Uuid>())?;
        writer.write(src.as_bytes())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        crate::{deserialize, proptest_config::proptest_cfg, serialize},
        proptest::prelude::*,
        uuid::{Bytes, Uuid},
    };

    // We can only compare against bincode's serialization if
    // serde compatibility is enabled due to length prefixing.
    #[cfg(feature = "uuid-serde-compat")]
    #[test]
    fn test_uuid_roundtrip_serde_compat() {
        proptest!(proptest_cfg(), |(value: Bytes)| {
            let uuid = uuid::Uuid::from_bytes(value);
            let bincode_serialized = bincode::serialize(&uuid).unwrap();
            let serialized = serialize(&uuid).unwrap();
            prop_assert_eq!(&bincode_serialized, &serialized);
            let deserialized: Uuid = deserialize(&serialized).unwrap();
            let bincode_deserialized: Uuid = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(uuid, deserialized);
            prop_assert_eq!(uuid, bincode_deserialized);
        });
    }

    // We can only compare against bincode's serialization if
    // serde compatibility is enabled due to length prefixing.
    #[cfg(all(feature = "uuid-serde-compat", feature = "alloc"))]
    #[test]
    fn test_uuid_roundtrip_in_sequence_serde_compat() {
        proptest!(proptest_cfg(), |(value: Vec<Bytes>)| {
            let uuids = value.into_iter().map(uuid::Uuid::from_bytes).collect::<Vec<_>>();
            let bincode_serialized = bincode::serialize(&uuids).unwrap();
            let serialized = serialize(&uuids).unwrap();
            prop_assert_eq!(&bincode_serialized, &serialized);
            let deserialized: Vec<Uuid> = deserialize(&serialized).unwrap();
            let bincode_deserialized: Vec<Uuid> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&uuids, &deserialized);
            prop_assert_eq!(uuids, bincode_deserialized);
        });
    }

    #[cfg(not(feature = "uuid-serde-compat"))]
    #[test]
    fn test_uuid_roundtrip() {
        proptest!(proptest_cfg(), |(value: Bytes)| {
            let uuid = uuid::Uuid::from_bytes(value);
            let serialized = serialize(&uuid).unwrap();
            let deserialized: Uuid = deserialize(&serialized).unwrap();
            prop_assert_eq!(uuid, deserialized);
        });
    }

    #[cfg(all(not(feature = "uuid-serde-compat"), feature = "alloc"))]
    #[test]
    fn test_uuid_roundtrip_in_sequence() {
        proptest!(proptest_cfg(), |(value: Vec<Bytes>)| {
            let uuids = value.into_iter().map(uuid::Uuid::from_bytes).collect::<Vec<_>>();
            let serialized = serialize(&uuids).unwrap();
            let deserialized: Vec<Uuid> = deserialize(&serialized).unwrap();
            prop_assert_eq!(uuids, deserialized);
        });
    }
}
