//! Deserializer

use {
    crate::{error::ReadError, io::Reader, SchemaRead},
    core::marker::PhantomData,
    serde::de::{DeserializeSeed, EnumAccess, MapAccess, SeqAccess, VariantAccess, Visitor},
    thiserror::Error,
};

const ANY_NOT_SUPPORTED: &str = "Wincode does not support serde's `any` decoding feature";
const IDENTIFIER_NOT_SUPPORTED: &str = "Wincode does not support serde identifiers";
const IGNORED_ANY_NOT_SUPPORTED: &str = "Wincode does not support serde's `ignored_any`";
const SERDE_ERROR: &str = "serde error";

#[cfg(not(feature = "alloc"))]
const CANNOT_ALLOCATE: &str =
    "Cannot allocate data like `String` and `Vec<u8>` without `alloc` feature";

#[derive(Debug, Error)]
pub enum Error {
    /// Bincode does not support serde's `any` decoding feature.
    #[error("{ANY_NOT_SUPPORTED}")]
    AnyNotSupported,
    /// Could not allocate data like `String` and `Vec<u8>`
    #[cfg(not(feature = "alloc"))]
    #[error("{CANNOT_ALLOCATE}")]
    CannotAllocate,
    #[cfg(feature = "alloc")]
    #[error("{msg}")]
    CustomSerde { msg: alloc::string::String },
    #[cfg(not(feature = "alloc"))]
    #[error("{SERDE_ERROR}")]
    CustomSerde,
    /// Wincode does not support serde identifiers.
    #[error("{IDENTIFIER_NOT_SUPPORTED}")]
    IdentifierNotSupported,
    /// Wincode does not support serde's `ignored_any`.
    #[error("{IGNORED_ANY_NOT_SUPPORTED}")]
    IgnoredAnyNotSupported,
    #[error(transparent)]
    Read(#[from] ReadError),
}

impl serde::de::Error for Error {
    #[cfg(feature = "alloc")]
    fn custom<T>(msg: T) -> Self
    where
        T: core::fmt::Display,
    {
        Self::CustomSerde {
            msg: alloc::string::ToString::to_string(&msg),
        }
    }

    #[cfg(not(feature = "alloc"))]
    fn custom<T>(_msg: T) -> Self
    where
        T: core::fmt::Display,
    {
        Self::CustomSerde
    }
}

impl From<Error> for ReadError {
    fn from(err: Error) -> Self {
        match err {
            Error::AnyNotSupported => Self::Custom(ANY_NOT_SUPPORTED),
            #[cfg(not(feature = "alloc"))]
            Error::CannotAllocate => Self::Custom(CANNOT_ALLOCATE),
            #[cfg(feature = "alloc")]
            Error::CustomSerde { msg: _ } => Self::Custom(SERDE_ERROR),
            #[cfg(not(feature = "alloc"))]
            Error::CustomSerde => Self::Custom(SERDE_ERROR),
            Error::IdentifierNotSupported => Self::Custom(IDENTIFIER_NOT_SUPPORTED),
            Error::IgnoredAnyNotSupported => Self::Custom(IGNORED_ANY_NOT_SUPPORTED),
            Error::Read(err) => err,
        }
    }
}

pub struct Deserializer<R, C = crate::config::Configuration> {
    inner: R,
    marker: PhantomData<C>,
}

impl<R, C> Deserializer<R, C> {
    pub fn new(reader: R) -> Self {
        Self {
            inner: reader,
            marker: PhantomData,
        }
    }
}

macro_rules! impl_fn {
    ($deserialize_method:ident, $visit_method:ident, $visit_ty:ty) => {
        fn $deserialize_method<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: Visitor<'de>,
        {
            visitor.$visit_method(<$visit_ty as SchemaRead<C>>::get(&mut self.inner)?)
        }
    };
}

impl<'de, C, R> serde::Deserializer<'de> for Deserializer<R, C>
where
    C: crate::config::Config,
    R: Reader<'de>,
{
    type Error = Error;

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(Self::Error::AnyNotSupported)
    }

    impl_fn!(deserialize_bool, visit_bool, bool);
    impl_fn!(deserialize_i8, visit_i8, i8);
    impl_fn!(deserialize_i16, visit_i16, i16);
    impl_fn!(deserialize_i32, visit_i32, i32);
    impl_fn!(deserialize_i64, visit_i64, i64);
    impl_fn!(deserialize_i128, visit_i128, i128);
    impl_fn!(deserialize_u8, visit_u8, u8);
    impl_fn!(deserialize_u16, visit_u16, u16);
    impl_fn!(deserialize_u32, visit_u32, u32);
    impl_fn!(deserialize_u64, visit_u64, u64);
    impl_fn!(deserialize_u128, visit_u128, u128);
    impl_fn!(deserialize_f32, visit_f32, f32);
    impl_fn!(deserialize_f64, visit_f64, f64);
    impl_fn!(deserialize_char, visit_char, char);
    impl_fn!(deserialize_str, visit_borrowed_str, &str);

    #[cfg(feature = "alloc")]
    impl_fn!(deserialize_string, visit_string, alloc::string::String);

    #[cfg(not(feature = "alloc"))]
    fn deserialize_string<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(Self::Error::CannotAllocate)
    }

    impl_fn!(deserialize_bytes, visit_borrowed_bytes, &[u8]);

    #[cfg(feature = "alloc")]
    impl_fn!(deserialize_byte_buf, visit_byte_buf, alloc::vec::Vec<u8>);

    #[cfg(not(feature = "alloc"))]
    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(Self::Error::CannotAllocate)
    }

    fn deserialize_option<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let discriminant = <u8 as SchemaRead<C>>::get(&mut self.inner)?;
        match discriminant {
            0 => visitor.visit_none(),
            1 => visitor.visit_some(self),
            d => Err(ReadError::InvalidTagEncoding(d.into()).into()),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        let len = <usize as SchemaRead<C>>::get(&mut self.inner)?;
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        struct Access<R, C> {
            deserializer: Deserializer<R, C>,
            len: usize,
        }

        impl<'de, C, R> SeqAccess<'de> for Access<R, C>
        where
            C: crate::config::Config,
            R: Reader<'de>,
        {
            type Error = Error;

            fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
            where
                T: DeserializeSeed<'de>,
            {
                if self.len > 0 {
                    self.len -= 1;
                    let value = DeserializeSeed::deserialize(
                        seed,
                        Deserializer {
                            inner: &mut self.deserializer.inner,
                            marker: self.deserializer.marker,
                        },
                    )?;
                    Ok(Some(value))
                } else {
                    Ok(None)
                }
            }

            fn size_hint(&self) -> Option<usize> {
                Some(self.len)
            }
        }

        visitor.visit_seq(Access {
            deserializer: self,
            len,
        })
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        struct Access<R, C> {
            deserializer: Deserializer<R, C>,
            len: usize,
        }

        impl<'de, C, R> MapAccess<'de> for Access<R, C>
        where
            C: crate::config::Config,
            R: Reader<'de>,
        {
            type Error = Error;

            fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
            where
                K: DeserializeSeed<'de>,
            {
                if self.len > 0 {
                    self.len -= 1;
                    let key = DeserializeSeed::deserialize(
                        seed,
                        Deserializer {
                            inner: &mut self.deserializer.inner,
                            marker: self.deserializer.marker,
                        },
                    )?;
                    Ok(Some(key))
                } else {
                    Ok(None)
                }
            }

            fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
            where
                V: DeserializeSeed<'de>,
            {
                let value = DeserializeSeed::deserialize(
                    seed,
                    Deserializer {
                        inner: &mut self.deserializer.inner,
                        marker: self.deserializer.marker,
                    },
                )?;
                Ok(value)
            }

            fn size_hint(&self) -> Option<usize> {
                Some(self.len)
            }
        }

        let len = <usize as SchemaRead<C>>::get(&mut self.inner)?;

        visitor.visit_map(Access {
            deserializer: self,
            len,
        })
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_tuple(fields.len(), visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_enum(self)
    }

    fn deserialize_identifier<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        Err(Self::Error::IdentifierNotSupported)
    }

    fn deserialize_ignored_any<V>(self, _: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        Err(Self::Error::IgnoredAnyNotSupported)
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}

impl<'de, C, R> EnumAccess<'de> for Deserializer<R, C>
where
    C: crate::config::Config,
    R: Reader<'de>,
{
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(mut self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        use serde::de::value::U32Deserializer;
        let idx = <u32 as SchemaRead<C>>::get(&mut self.inner)?;
        let val = seed.deserialize(U32Deserializer::<Self::Error>::new(idx))?;
        Ok((val, self))
    }
}

impl<'de, C, R> VariantAccess<'de> for Deserializer<R, C>
where
    C: crate::config::Config,
    R: Reader<'de>,
{
    type Error = Error;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        DeserializeSeed::deserialize(seed, self)
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        serde::Deserializer::deserialize_tuple(self, len, visitor)
    }

    fn struct_variant<V>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        serde::Deserializer::deserialize_tuple(self, fields.len(), visitor)
    }
}
