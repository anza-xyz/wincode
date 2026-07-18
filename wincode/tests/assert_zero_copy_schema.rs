#![cfg(feature = "derive")]

use {
    core::mem::MaybeUninit,
    wincode::{
        ReadResult, SchemaRead, SchemaWrite, TypeMeta, WriteResult,
        config::{Config, ConfigCore, ZeroCopy},
        io::{Reader, Writer},
    },
};

#[repr(transparent)]
struct ReadStaticWriteDynamic(u8);

unsafe impl<C: ConfigCore> ZeroCopy<C> for ReadStaticWriteDynamic {}

unsafe impl<C: Config> SchemaWrite<C> for ReadStaticWriteDynamic {
    type Src = Self;

    const TYPE_META: TypeMeta = TypeMeta::Dynamic;

    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(1)
    }

    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        <u8 as SchemaWrite<C>>::write(writer, &src.0)
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for ReadStaticWriteDynamic {
    type Dst = Self;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 1,
        zero_copy: true,
    };

    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        dst.write(Self(<u8 as SchemaRead<'de, C>>::get(reader)?));
        Ok(())
    }
}

#[repr(transparent)]
#[derive(SchemaWrite, SchemaRead)]
#[wincode(assert_zero_copy(schema = "read"))]
struct ReadOnlyAssertion(ReadStaticWriteDynamic);

#[repr(transparent)]
struct ReadDynamicWriteStatic(u8);

unsafe impl<C: ConfigCore> ZeroCopy<C> for ReadDynamicWriteStatic {}

unsafe impl<C: Config> SchemaWrite<C> for ReadDynamicWriteStatic {
    type Src = Self;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 1,
        zero_copy: true,
    };

    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(1)
    }

    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        <u8 as SchemaWrite<C>>::write(writer, &src.0)
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for ReadDynamicWriteStatic {
    type Dst = Self;

    const TYPE_META: TypeMeta = TypeMeta::Dynamic;

    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        dst.write(Self(<u8 as SchemaRead<'de, C>>::get(reader)?));
        Ok(())
    }
}

#[repr(transparent)]
#[derive(SchemaWrite, SchemaRead)]
#[wincode(assert_zero_copy(schema = "write"))]
struct WriteOnlyAssertion(ReadDynamicWriteStatic);

#[test]
fn selected_schema_allows_asymmetric_metadata() {
    assert!(matches!(
        <ReadOnlyAssertion as SchemaRead<'_, wincode::config::DefaultConfig>>::TYPE_META,
        TypeMeta::Static { .. }
    ));
    assert!(matches!(
        <WriteOnlyAssertion as SchemaWrite<wincode::config::DefaultConfig>>::TYPE_META,
        TypeMeta::Static { .. }
    ));
}
