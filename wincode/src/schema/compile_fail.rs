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

/// A `read_<field>` on an `UninitBuilder` must not launder the reader lifetime: reading
/// from a short-lived reader into a longer-lived borrowed field (here `'static`) would
/// leave a dangling reference after `assume_init`. The `'de: 'a` bound rejects it.
///
/// The matching positive case (a reader that outlives the borrowed field) is covered by
/// `test_uninit_builder_read_borrowed` in `schema::tests`.
///
/// ```compile_fail
/// # #[cfg(all(feature = "derive"))] {
/// use {core::mem::MaybeUninit, wincode::config::DefaultConfig};
///
/// #[derive(wincode::UninitBuilder)]
/// struct Borrowed<'a> {
///     data: &'a [u8],
/// }
///
/// fn launder() -> Borrowed<'static> {
///     let mut uninit = MaybeUninit::<Borrowed<'static>>::uninit();
///     {
///         let short_lived: Vec<u8> = vec![3, 0, 0, 0, 0, 0, 0, 0, 0xAA, 0xBB, 0xCC];
///         let mut builder =
///             BorrowedUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
///         builder.read_data(short_lived.as_slice()).unwrap();
///         builder.finish();
///     }
///     unsafe { uninit.assume_init() }
/// }
/// # }
/// ```
fn uninit_builder_read_forbids_lifetime_launder() {}
