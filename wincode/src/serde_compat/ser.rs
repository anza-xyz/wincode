//! Serializer

use {
    crate::{error::WriteError, io::Writer, SchemaWrite},
    core::marker::PhantomData,
    serde::Serialize,
    thiserror::Error,
};

#[cfg(not(feature = "alloc"))]
const CANNOT_COLLECT_STR: &str =
    "`serde::Serializer::collect_str` got called but wincode was unable to allocate memory";

const SEQUENCE_MUST_HAVE_LENGTH: &str =
    "Serde provided wincode with a sequence without a length, which is not supported in wincode";

const SERDE_ERROR: &str = "serde error";

#[derive(Debug, Error)]
pub enum Error {
    /// [`serde::Serializer::collect_str`] got called but wincode was unable to allocate memory.
    #[cfg(not(feature = "alloc"))]
    #[error("{CANNOT_COLLECT_STR}")]
    CannotCollectStr,
    #[cfg(feature = "alloc")]
    #[error("{msg}")]
    CustomSerde { msg: alloc::string::String },
    #[cfg(not(feature = "alloc"))]
    #[error("{SERDE_ERROR}")]
    CustomSerde,
    /// Serde provided wincode with a sequence without a length, which is not
    /// supported in wincode.
    #[error("{SEQUENCE_MUST_HAVE_LENGTH}")]
    SequenceMustHaveLength,
    #[error(transparent)]
    Write(#[from] WriteError),
}

impl From<Error> for WriteError {
    fn from(err: Error) -> Self {
        match err {
            #[cfg(not(feature = "alloc"))]
            Error::CannotCollectStr => Self::Custom(CANNOT_COLLECT_STR),
            #[cfg(feature = "alloc")]
            Error::CustomSerde { msg: _ } => Self::Custom(SERDE_ERROR),
            #[cfg(not(feature = "alloc"))]
            Error::CustomSerde => Self::Custom(SERDE_ERROR),
            Error::SequenceMustHaveLength => Self::Custom(SEQUENCE_MUST_HAVE_LENGTH),
            Error::Write(err) => err,
        }
    }
}

impl serde::ser::Error for Error {
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

pub struct Serializer<W, C = crate::config::Configuration> {
    inner: W,
    marker: PhantomData<C>,
}

impl<W, C> Serializer<W, C> {
    pub fn new(writer: W) -> Self {
        Self {
            inner: writer,
            marker: PhantomData,
        }
    }

    fn as_mut(&mut self) -> Serializer<&mut W, C> {
        Serializer {
            inner: &mut self.inner,
            marker: self.marker,
        }
    }
}

macro_rules! impl_fn_serializer {
    ($serialize_method:ident, $serialize_ty:ty) => {
        fn $serialize_method(self, value: $serialize_ty) -> Result<Self::Ok, Self::Error> {
            <$serialize_ty as SchemaWrite<C>>::write(self.inner, &value).map_err(Self::Error::Write)
        }
    };
}

impl<W, C> serde::Serializer for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    impl_fn_serializer!(serialize_bool, bool);
    impl_fn_serializer!(serialize_i8, i8);
    impl_fn_serializer!(serialize_i16, i16);
    impl_fn_serializer!(serialize_i32, i32);
    impl_fn_serializer!(serialize_i64, i64);
    impl_fn_serializer!(serialize_u8, u8);
    impl_fn_serializer!(serialize_u16, u16);
    impl_fn_serializer!(serialize_u32, u32);
    impl_fn_serializer!(serialize_u64, u64);
    impl_fn_serializer!(serialize_f32, f32);
    impl_fn_serializer!(serialize_f64, f64);
    impl_fn_serializer!(serialize_char, char);
    impl_fn_serializer!(serialize_str, &str);
    impl_fn_serializer!(serialize_bytes, &[u8]);

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        <u8 as SchemaWrite<C>>::write(self.inner, &0u8).map_err(Self::Error::Write)
    }

    fn serialize_some<T>(mut self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize + ?Sized,
    {
        <u8 as SchemaWrite<C>>::write(&mut self.inner, &1u8)?;
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        <u32 as SchemaWrite<C>>::write(self.inner, &variant_index).map_err(Self::Error::Write)
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize + ?Sized,
    {
        <u32 as SchemaWrite<C>>::write(&mut self.inner, &variant_index)?;
        value.serialize(self)
    }

    fn serialize_seq(mut self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        let len = len.ok_or(Self::Error::SequenceMustHaveLength)?;
        <usize as SchemaWrite<C>>::write(&mut self.inner, &len)?;
        Ok(self)
    }

    fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple_variant(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        <u32 as SchemaWrite<C>>::write(&mut self.inner, &variant_index)?;
        Ok(self)
    }

    fn serialize_map(mut self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        let len = len.ok_or(Self::Error::SequenceMustHaveLength)?;
        <usize as SchemaWrite<C>>::write(&mut self.inner, &len)?;
        Ok(self)
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(self)
    }

    fn serialize_struct_variant(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        <u32 as SchemaWrite<C>>::write(&mut self.inner, &variant_index)?;
        Ok(self)
    }

    #[cfg(not(feature = "alloc"))]
    fn collect_str<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
    where
        T: core::fmt::Display + ?Sized,
    {
        Err(Self::Error::CannotCollectStr)
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}

impl<W, C> serde::ser::SerializeSeq for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<W, C> serde::ser::SerializeTuple for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<W, C> serde::ser::SerializeTupleStruct for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<W, C> serde::ser::SerializeTupleVariant for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<W, C> serde::ser::SerializeMap for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        key.serialize(self.as_mut())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<W, C> serde::ser::SerializeStruct for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, _key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<W, C> serde::ser::SerializeStructVariant for Serializer<W, C>
where
    C: crate::config::Config,
    W: Writer,
{
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, _key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self.as_mut())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

const SIZE_OVERFLOW: &str = "Overflow when calculating serialized size";

#[derive(Debug, Error)]
pub enum SizeOfError {
    #[error(transparent)]
    Serialize(Error),
    /// Overflow when calculating serialized size
    #[error("{SIZE_OVERFLOW}")]
    SizeOverflow,
}

impl<E> From<E> for SizeOfError
where
    Error: From<E>,
{
    fn from(err: E) -> Self {
        Self::Serialize(err.into())
    }
}

impl From<SizeOfError> for WriteError {
    fn from(err: SizeOfError) -> Self {
        match err {
            SizeOfError::Serialize(err) => err.into(),
            SizeOfError::SizeOverflow => Self::Custom(SIZE_OVERFLOW),
        }
    }
}

impl serde::ser::Error for SizeOfError {
    fn custom<T>(msg: T) -> Self
    where
        T: core::fmt::Display,
    {
        Self::Serialize(Error::custom(msg))
    }
}

/// Dummy serializer used to compute serialized size
#[repr(transparent)]
pub(in crate::serde_compat) struct SizeOf<C> {
    size: usize,
    marker: PhantomData<C>,
}

impl<C> SizeOf<C> {
    pub fn new() -> Self {
        Self {
            size: 0,
            marker: PhantomData,
        }
    }

    /// Returns the size in bytes that the serializer has already processed
    pub fn serialized_size(&self) -> usize {
        self.size
    }

    #[must_use]
    fn add_size(&mut self, size: usize) -> Result<(), SizeOfError> {
        self.size = self
            .size
            .checked_add(size)
            .ok_or(SizeOfError::SizeOverflow)?;
        Ok(())
    }
}

macro_rules! impl_fn_sizeof {
    ($serialize_method:ident, $serialize_ty:ty) => {
        fn $serialize_method(mut self, value: $serialize_ty) -> Result<Self::Ok, Self::Error> {
            let value_size = <$serialize_ty as SchemaWrite<C>>::size_of(&value)?;
            self.add_size(value_size)?;
            Ok(self)
        }
    };
}

impl<C> serde::Serializer for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    impl_fn_sizeof!(serialize_bool, bool);
    impl_fn_sizeof!(serialize_i8, i8);
    impl_fn_sizeof!(serialize_i16, i16);
    impl_fn_sizeof!(serialize_i32, i32);
    impl_fn_sizeof!(serialize_i64, i64);
    impl_fn_sizeof!(serialize_i128, i128);
    impl_fn_sizeof!(serialize_u8, u8);
    impl_fn_sizeof!(serialize_u16, u16);
    impl_fn_sizeof!(serialize_u32, u32);
    impl_fn_sizeof!(serialize_u64, u64);
    impl_fn_sizeof!(serialize_u128, u128);
    impl_fn_sizeof!(serialize_f32, f32);
    impl_fn_sizeof!(serialize_f64, f64);
    impl_fn_sizeof!(serialize_char, char);
    impl_fn_sizeof!(serialize_str, &str);
    impl_fn_sizeof!(serialize_bytes, &[u8]);

    fn serialize_none(mut self) -> Result<Self::Ok, Self::Error> {
        let discriminant_size = <u8 as SchemaWrite<C>>::size_of(&0u8)?;
        self.add_size(discriminant_size)?;
        Ok(self)
    }

    fn serialize_some<T>(mut self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let discriminant_size = <u8 as SchemaWrite<C>>::size_of(&1u8)?;
        self.add_size(discriminant_size)?;
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }

    fn serialize_unit_variant(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        let variant_index_size = <u32 as SchemaWrite<C>>::size_of(&variant_index)?;
        self.add_size(variant_index_size)?;
        Ok(self)
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize + ?Sized,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let variant_index_size = <u32 as SchemaWrite<C>>::size_of(&variant_index)?;
        self.add_size(variant_index_size)?;
        value.serialize(self)
    }

    fn serialize_seq(mut self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        let len = len.ok_or(Error::SequenceMustHaveLength)?;
        let len_size = <usize as SchemaWrite<C>>::size_of(&len)?;
        self.add_size(len_size)?;
        Ok(self)
    }

    fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Ok(self)
    }

    fn serialize_tuple_variant(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        let variant_index_size = <u32 as SchemaWrite<C>>::size_of(&variant_index)?;
        self.add_size(variant_index_size)?;
        Ok(self)
    }

    fn serialize_map(mut self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        let len = len.ok_or(Error::SequenceMustHaveLength)?;
        let len_size = <usize as SchemaWrite<C>>::size_of(&len)?;
        self.add_size(len_size)?;
        Ok(self)
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(self)
    }

    fn serialize_struct_variant(
        mut self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        let variant_index_size = <u32 as SchemaWrite<C>>::size_of(&variant_index)?;
        self.add_size(variant_index_size)?;
        Ok(self)
    }

    #[cfg(not(feature = "alloc"))]
    fn collect_str<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
    where
        T: core::fmt::Display + ?Sized,
    {
        Err(Error::CannotCollectStr.into())
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}

impl<C> serde::ser::SerializeSeq for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}

impl<C> serde::ser::SerializeTuple for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}

impl<C> serde::ser::SerializeTupleStruct for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}

impl<C> serde::ser::SerializeTupleVariant for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}

impl<C> serde::ser::SerializeMap for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = key.serialize(serializer)?;
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}

impl<C> serde::ser::SerializeStruct for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_field<T>(&mut self, _key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}

impl<C> serde::ser::SerializeStructVariant for SizeOf<C>
where
    C: crate::config::Config,
{
    type Ok = Self;
    type Error = SizeOfError;

    fn serialize_field<T>(&mut self, _key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize + ?Sized,
    {
        let serializer = SizeOf {
            size: self.size,
            marker: self.marker,
        };
        *self = value.serialize(serializer)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self)
    }
}
