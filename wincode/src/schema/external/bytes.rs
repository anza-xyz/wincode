use {
    crate::{
        config::Config,
        io::{Reader, Writer},
        ReadResult, SchemaRead, SchemaWrite, WriteResult,
    },
    bytes::{Bytes, BytesMut},
    core::mem::MaybeUninit,
};

unsafe impl<'de, C: Config> SchemaRead<'de, C> for Bytes {
    type Dst = Self;

    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // Box<[u8]> is closest to native representation of Bytes and avoid data copy or allocs.
        let boxed_slice = <Box<[u8]> as SchemaRead<'de, C>>::get(reader)?;
        dst.write(Self::from(boxed_slice));
        Ok(())
    }
}

unsafe impl<C: Config> SchemaWrite<C> for Bytes {
    type Src = Self;

    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <[u8] as SchemaWrite<C>>::size_of(src.as_ref())
    }

    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        <[u8] as SchemaWrite<C>>::write(writer, src.as_ref())
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for BytesMut {
    type Dst = Self;

    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // BytesMut doesn't expose direct way to initialize from owned Vec even though it is
        // currently its internal representation, however it does detect that provided Bytes
        // is unique owner of original buffer, so this conversion doesn't allocate or copy.
        let bytes = <Bytes as SchemaRead<'de, C>>::get(reader)?;
        dst.write(Self::from(bytes));
        Ok(())
    }
}

unsafe impl<C: Config> SchemaWrite<C> for BytesMut {
    type Src = Self;

    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <[u8] as SchemaWrite<C>>::size_of(src.as_ref())
    }

    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        <[u8] as SchemaWrite<C>>::write(writer, src.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{deserialize, proptest_config::proptest_cfg, serialize},
        proptest::prelude::*,
    };

    #[test]
    fn test_static() {
        let bytes = Bytes::from_static(b"hello");
        let serialized = serialize(&bytes).unwrap();
        let deserialized = deserialize::<Bytes>(&serialized).unwrap();
        assert_eq!(deserialized, bytes);
    }

    #[test]
    fn test_dynamic() {
        proptest!(proptest_cfg(), |(data: Vec<u8>)| {
            let bytes_mut = BytesMut::from(data.as_slice());
            let bytes = Bytes::from_owner(data);

            let serialized_bytes = serialize(&bytes).unwrap();
            let deserialized_bytes = deserialize::<Bytes>(&serialized_bytes).unwrap();
            prop_assert_eq!(deserialized_bytes, bytes);

            let serialized_bytes_mut = serialize(&bytes_mut).unwrap();
            let deserialized_bytes_mut = deserialize::<BytesMut>(&serialized_bytes_mut).unwrap();
            prop_assert_eq!(deserialized_bytes_mut, bytes_mut);

            prop_assert_eq!(serialized_bytes, serialized_bytes_mut);
        })
    }
}
