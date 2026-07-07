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
