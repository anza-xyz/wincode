//! Compile fail tests.
#![expect(unused)]

/// ```compile_fail
/// # #[cfg(all(feature = "derive", feature = "alloc"))] {
/// use wincode::{SchemaRead, SchemaWrite, deserialize, serialize};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// struct StaticStr {
///     value: Option<&'static str>,
/// }
///
/// let serialized = serialize(&StaticStr {
///     value: Some("actually static"),
/// })
/// .unwrap();
///
/// let _: StaticStr = deserialize(&serialized).unwrap();
/// # }
/// ```
///
/// ```
/// # #[cfg(all(feature = "derive"))] {
/// use wincode::{SchemaRead, SchemaWrite, deserialize};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// struct StaticStr {
///     value: Option<&'static str>,
/// }
///
/// let serialized = b"\x00".as_slice();
///
/// let _: StaticStr = deserialize(serialized).unwrap();
/// # }
/// ```
fn static_derive_requires_static_input() {}

/// ```compile_fail
/// # #[cfg(all(feature = "derive"))] {
/// use wincode::{SchemaRead, SchemaWrite};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// enum MyEnum {
///     #[wincode(tag = 1)]
///     Foo,
///     #[wincode(tag = 1)]
///     Bar,
/// }
/// # }
/// ```
fn derive_tag_uniqueness() {}

/// ```compile_fail
/// # #[cfg(all(feature = "derive"))] {
/// use wincode::{SchemaRead, SchemaWrite};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// enum MyEnum {
///     #[wincode(tag = 1)]
///     Foo,
///     #[wincode(tag = 0x1)]
///     Bar,
/// }
/// # }
/// ```
fn derive_tag_uniqueness_repr_normalization() {}

/// ```compile_fail
/// # #[cfg(all(feature = "derive"))] {
/// use wincode::{SchemaRead, SchemaWrite};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// enum MyEnum {
///     Foo,
///     #[wincode(tag = 0)]
///     Bar,
/// }
/// # }
/// ```
fn derive_tag_uniqueness_implicit_collision() {}

/// A `#[wincode(from = "T")]` schema whose fields do not cover the full layout of
/// the target `T` must not be classified zero-copy: the zero-copy slice readers
/// borrow `len * schema_size` bytes but form `&[T]` spanning `len * size_of::<T>()`,
/// which would read/write past the input buffer. Such a schema must fail to satisfy
/// `ZeroCopy`, so `&[Schema]` does not implement `SchemaRead`.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use wincode::{SchemaRead, config::DefaultConfig};
///
/// #[repr(C)]
/// pub struct Foreign {
///     pub a: u64,
///     pub b: u64,
///     pub c: u64, // <-- NOT represented in the schema below
/// }
///
/// #[derive(wincode::SchemaWrite, wincode::SchemaRead)]
/// #[wincode(from = "Foreign")]
/// #[repr(C)]
/// struct Schema {
///     a: u64,
///     b: u64,
/// }
///
/// let buf = [0u8; 8 + 2 * 16];
/// let _: &[Foreign] =
///     <&[Schema] as SchemaRead<'_, DefaultConfig>>::get(&buf[..]).unwrap();
/// # }
/// ```
fn from_mapping_layout_mismatch_is_not_zero_copy() {}
