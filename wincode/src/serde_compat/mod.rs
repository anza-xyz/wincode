//! Serde compatibility

use {
    crate::{
        error::{ReadResult, WriteError, WriteResult},
        io::{Reader, Writer},
    },
    core::{marker::PhantomData, mem::MaybeUninit},
};

mod de;
mod ser;

pub use {de::Deserializer, ser::Serializer};

/// Wrapper struct that impls [`crate::SchemaRead`] and
/// [`crate::SchemaWrite`] for types that impl [`serde::Deserialize`] and
// [`serde::Serialize`], respectively.
#[repr(transparent)]
pub struct SerdeCompat<T> {
    _marker: PhantomData<T>,
}

unsafe impl<'de, C, T> crate::SchemaRead<'de, C> for SerdeCompat<T>
where
    C: crate::config::Config,
    T: serde::Deserialize<'de>,
{
    type Dst = T;

    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let deserializer = Deserializer::<_, C>::new(reader);
        let value = T::deserialize(deserializer)?;
        dst.write(value);
        Ok(())
    }
}

unsafe impl<'de, C, T> crate::SchemaWrite<C> for SerdeCompat<T>
where
    C: crate::config::Config,
    T: serde::Serialize,
{
    type Src = T;

    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        let mut serializer = ser::SizeOf::<C>::new();
        serializer = src.serialize(serializer)?;
        Ok(serializer.serialized_size())
    }

    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        let serializer = Serializer::<_, C>::new(writer);
        src.serialize(serializer).map_err(WriteError::from)
    }
}

#[cfg(test)]
mod tests {
    use super::SerdeCompat;

    #[test]
    fn test_flattened_roundtrip() -> Result<(), Box<dyn std::error::Error>> {
        #[derive(serde::Deserialize, serde::Serialize, Debug, Eq, PartialEq)]
        struct InnerMost<'a> {
            #[serde(borrow)]
            msg: &'a str,
            #[serde(borrow)]
            bytes: &'a [u8],
        }
        #[derive(serde::Deserialize, serde::Serialize, Debug, Eq, PartialEq)]
        struct InnerMore<'a> {
            u32_value: u32,
            #[serde(borrow)]
            inner: InnerMost<'a>,
        }
        #[derive(serde::Deserialize, serde::Serialize, Debug, Eq, PartialEq)]
        struct Outer<'a> {
            #[serde(borrow)]
            inner: InnerMore<'a>,
            bool_value: bool,
        }

        let value = Outer {
            inner: InnerMore {
                u32_value: 69_420,
                inner: InnerMost {
                    msg: "test msg",
                    bytes: b"test bytes",
                },
            },
            bool_value: true,
        };
        let value_serialized_bincode = bincode::serialize(&value)?;
        let value_serialized_wincode = <SerdeCompat<Outer> as crate::Serialize>::serialize(&value)?;
        assert_eq!(value_serialized_bincode, value_serialized_wincode);
        let value_deserialized =
            <SerdeCompat<Outer> as crate::Deserialize>::deserialize(&value_serialized_wincode)?;
        assert_eq!(value_deserialized, value);
        Ok(())
    }
}
