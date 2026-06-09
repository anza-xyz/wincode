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

/// A variant-level `with` requires the variant to have exactly one field.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use wincode::{SchemaRead, SchemaWrite};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// enum Foo {
///     #[wincode(with = "Bar")]
///     Bar(u32, u32),
/// }
/// # }
/// ```
fn variant_with_requires_single_field() {}

/// A `with` cannot be specified on both a variant and its field.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use wincode::{SchemaRead, SchemaWrite};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// enum Foo {
///     #[wincode(with = "Bar")]
///     Bar(#[wincode(with = "Baz")] u32),
/// }
/// # }
/// ```
fn variant_with_conflicts_with_field_with() {}
