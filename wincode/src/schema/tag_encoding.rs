//! Tag encoding configuration.
use {
    crate::{
        config::ConfigCore,
        error::{tag_encoding_overflow, TagEncodingOverflow},
        io::Writer,
        SchemaRead, SchemaWrite, WriteResult,
    },
    core::any::type_name,
};

/// Tag encoding trait.
///
/// This trait normalizes discriminant encodings to a common type, `u32`.
/// The reason for this is that `SchemaRead` and `SchemaWrite` implementations
/// for enums need to match on explicit integer literals.
///
/// For example,
/// ```compile_fail
/// # use wincode::{SchemaRead, SchemaWrite, config::Config, io::Reader, ReadResult};
/// # use core::mem::MaybeUninit;
/// enum Foo {
///     Bar,
///     Baz,
/// }
///
/// unsafe impl<'de, C: Config> SchemaRead<'de, C> for Foo {
///     type Dst = Self;
///
///     fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
///         let tag = C::TagEncoding::get(reader)?;
///         // Cannot match a generic type with an integer literal.
///         match tag {
///             0 => {}
///             1 => {}
///             // ...
///         }
///         Ok(())
///     }
/// }
/// ```
///
/// It is not possible to match on a generic type with an integer literal.
/// This is because we have no way of telling the compiler that a trait
/// is represented by a closed set of integer types.
///
/// By normalizing the discriminant encoding to a common type, we can
/// get around this limitation.
///
/// ```
/// # use wincode::{
/// #     SchemaRead, SchemaWrite,
/// #     config::Config,
/// #     io::Reader, ReadResult,
/// #     tag_encoding::TagEncoding,
/// #     error::invalid_tag_encoding,
/// # };
/// # use core::mem::MaybeUninit;
/// enum Foo {
///     Bar,
///     Baz,
/// }
///
/// unsafe impl<'de, C: Config> SchemaRead<'de, C> for Foo {
///     type Dst = Self;
///
///     fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
///         let tag = C::TagEncoding::try_into_u32(C::TagEncoding::get(reader)?)?;
///         // Now we can match on integer literals.
///         match tag {
///             0 => {
///                 // ...
///             }
///             1 => {
///                 // ...
///             }
///             _ => {
///                 return Err(invalid_tag_encoding(tag as usize));
///             }
///         }
///
///         Ok(())
///     }
/// }
/// ```
///
/// A note on performance: in release builds, the generated assembly for this scheme
/// typically elides conversions to and from the intermediate `u32` type.
/// Because `TagEncoding` is ultimately monomorphized into concrete integer targets,
/// the result of `try_from`/`try_into` calls are known at compile time.
/// All reads, matches, and writes on enums in the crate (including derive macros)
/// use compile-time integer literals, and in practice it was observed that tags are
/// loaded at their original width and compared directly to immediates.
pub trait TagEncoding<C: ConfigCore>:
    for<'de> SchemaRead<'de, C, Dst = Self::Target> + SchemaWrite<C, Src = Self::Target> + 'static
{
    type Target;

    /// Convert a `u32` to the encoding target.
    fn try_from_u32(value: u32) -> Result<Self::Target, TagEncodingOverflow>;

    /// Convert the encoding target to a `u32`.
    fn try_into_u32(x: Self::Target) -> Result<u32, TagEncodingOverflow>;

    /// Get the size of the encoding target from the given `u32`.
    ///
    /// The `u32` will be converted to the encoding target before calling
    /// [`SchemaWrite::size_of`] on the target implementation.
    #[inline(always)]
    fn size_of_from_u32(value: u32) -> WriteResult<usize> {
        Self::size_of(&Self::try_from_u32(value)?)
    }

    /// Write the encoding target from the given `u32` to the given [`Writer`].
    ///
    /// The `u32` will be converted to the encoding target before calling
    /// [`SchemaWrite::write`] on the target implementation.
    #[inline(always)]
    fn write_from_u32(writer: &mut impl Writer, value: u32) -> WriteResult<()> {
        Self::write(writer, &Self::try_from_u32(value)?)
    }
}

impl<T, Target, C: ConfigCore> TagEncoding<C> for T
where
    T: for<'de> SchemaRead<'de, C, Dst = Target> + SchemaWrite<C, Src = Target> + 'static,
    Target: TryFrom<u32>,
    u32: TryFrom<Target>,
{
    type Target = Target;

    #[inline(always)]
    fn try_from_u32(value: u32) -> Result<Self::Target, TagEncodingOverflow> {
        Target::try_from(value).map_err(|_| tag_encoding_overflow(type_name::<Target>()))
    }

    #[inline(always)]
    fn try_into_u32(x: Self::Target) -> Result<u32, TagEncodingOverflow> {
        u32::try_from(x).map_err(|_| tag_encoding_overflow(type_name::<Target>()))
    }
}
