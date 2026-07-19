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

/// A field-level context requires the derive's top-level context type.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use wincode::SchemaRead;
///
/// #[derive(SchemaRead)]
/// struct MissingContext {
///     #[wincode(context)]
///     value: u8,
/// }
/// # }
/// ```
fn derive_field_context_requires_top_level_context() {}

/// `UninitBuilder` does not generate contextual field readers.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// #[derive(wincode::UninitBuilder)]
/// #[wincode(context = "()")]
/// struct Contextual {
///     value: u8,
/// }
/// # }
/// ```
fn uninit_builder_rejects_context() {}

/// A lifetime supplied by the context still has to be tied to the input when an ordinary
/// field uses that same lifetime. Consequently, the derived value below cannot outlive the
/// serialized bytes borrowed by `borrowed`.
///
/// ```compile_fail
/// # #[cfg(all(feature = "derive", feature = "bumpalo"))] {
/// use {
///     bumpalo::{Bump, collections::String},
///     wincode::{SchemaRead, deserialize_with_context},
/// };
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "&'bump Bump")]
/// struct Mixed<'bump> {
///     #[wincode(context)]
///     owned: String<'bump>,
///     borrowed: &'bump u8,
/// }
///
/// fn deserialize_from_short_input<'bump>(bump: &'bump Bump) -> Mixed<'bump> {
///     let bytes = [0u8];
///     deserialize_with_context(bump, &bytes).unwrap()
/// }
/// # }
/// ```
fn context_lifetime_used_by_ordinary_field_remains_input_bound() {}

/// A contextual adapter must produce exactly the field type expected by the derived struct.
/// Otherwise, the struct's raw placement initialization could initialize the wrong type.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use {
///     core::mem::MaybeUninit,
///     wincode::{
///         ReadResult, SchemaRead, SchemaReadContext, config::ConfigCore, io::Reader,
///     },
/// };
///
/// struct Context;
/// struct Adapter;
///
/// unsafe impl<'de, C: ConfigCore> SchemaReadContext<'de, C, Context> for Adapter {
///     type Dst = u16;
///
///     fn read_with_context(
///         _ctx: Context,
///         _reader: impl Reader<'de>,
///         dst: &mut MaybeUninit<Self::Dst>,
///     ) -> ReadResult<()> {
///         dst.write(0);
///         Ok(())
///     }
/// }
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "Context")]
/// struct Contextual {
///     #[wincode(context, with = "Adapter")]
///     value: u8,
/// }
/// # }
/// ```
fn contextual_field_reader_requires_exact_destination_type() {}

/// Rewriting an input-backed field from `'ctx` to `'de` is only valid when the resulting value
/// can be safely shortened back to the field's declared type. An outlives bound alone is not
/// enough for contravariant or invariant types.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use {
///     core::mem::MaybeUninit,
///     wincode::{ReadResult, SchemaRead, config::ConfigCore, io::Reader},
/// };
///
/// struct Callback;
///
/// fn ignore(_: &u8) {}
///
/// unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for Callback {
///     type Dst = fn(&'de u8);
///
///     fn read(
///         _reader: impl Reader<'de>,
///         dst: &mut MaybeUninit<Self::Dst>,
///     ) -> ReadResult<()> {
///         dst.write(ignore);
///         Ok(())
///     }
/// }
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "&'ctx ()")]
/// struct Contextual<'ctx> {
///     #[wincode(with = "Callback")]
///     callback: fn(&'ctx u8),
/// }
/// # }
/// ```
fn rewritten_field_lifetime_requires_safe_shortening() {}

/// A contextual outer field cannot hide an ordinary input borrow made by its nested derived
/// reader. The nested reader's exact `Dst` bound carries the required `'de: 'ctx` relationship
/// even though the outer field itself is marked `context`.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use wincode::{SchemaRead, deserialize_with_context};
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "&'ctx ()")]
/// struct Inner<'ctx> {
///     borrowed: &'ctx u8,
/// }
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "&'ctx ()")]
/// struct Outer<'ctx> {
///     #[wincode(context)]
///     inner: Inner<'ctx>,
/// }
///
/// fn deserialize_from_short_input<'ctx>(ctx: &'ctx ()) -> Outer<'ctx> {
///     let bytes = [0u8];
///     deserialize_with_context(ctx, &bytes).unwrap()
/// }
/// # }
/// ```
fn nested_contextual_reader_preserves_ordinary_input_borrow() {}

/// An ordinary input borrow hidden behind an associated type cannot evade the destination-type
/// constraint merely because the derive's syntactic lifetime scan cannot see it.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use {
///     core::marker::PhantomData,
///     wincode::{SchemaRead, deserialize_with_context},
/// };
///
/// trait HasValue {
///     type Value;
/// }
///
/// struct Borrowed<'a>(PhantomData<&'a ()>);
///
/// impl<'a> HasValue for Borrowed<'a> {
///     type Value = &'a u8;
/// }
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "&'ctx ()")]
/// struct Associated<'ctx, T: HasValue> {
///     value: T::Value,
///     #[wincode(skip)]
///     lifetime: PhantomData<&'ctx ()>,
/// }
///
/// fn deserialize_from_short_input<'ctx>(ctx: &'ctx ()) -> Associated<'ctx, Borrowed<'ctx>> {
///     let bytes = [0u8];
///     deserialize_with_context(ctx, &bytes).unwrap()
/// }
/// # }
/// ```
fn associated_type_cannot_hide_ordinary_input_borrow() {}

/// A contextual derive cannot request the ordinary `ZeroCopy` marker because that marker does
/// not identify the context or destination type.
///
/// ```compile_fail
/// # #[cfg(feature = "derive")] {
/// use wincode::SchemaRead;
///
/// #[derive(SchemaRead)]
/// #[wincode(context = "()", assert_zero_copy)]
/// #[repr(transparent)]
/// struct Contextual(u8);
/// # }
/// ```
fn context_assert_zero_copy_is_unsupported() {}

/// A `read_<field>` on an `UninitBuilder` must not launder the reader lifetime: reading
/// from a short-lived reader into a longer-lived borrowed field (here `'static`) would
/// leave a dangling reference after `assume_init`.
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

/// An `UninitBuilder` reader must write exactly the field type, even when the field's
/// `SchemaRead` implementation declares a different `Dst`.
///
/// ```compile_fail
/// # #[cfg(all(feature = "derive"))] {
/// use {
///     core::mem::MaybeUninit,
///     wincode::{
///         ReadResult, SchemaRead,
///         config::{ConfigCore, DefaultConfig},
///         io::Reader,
///     },
/// };
///
/// struct Field;
/// struct DifferentDst(u64);
///
/// unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for Field {
///     type Dst = DifferentDst;
///
///     fn read(
///         _reader: impl Reader<'de>,
///         dst: &mut MaybeUninit<Self::Dst>,
///     ) -> ReadResult<()> {
///         dst.write(DifferentDst(0));
///         Ok(())
///     }
/// }
///
/// #[derive(wincode::UninitBuilder)]
/// struct HasField {
///     field: Field,
/// }
///
/// let mut uninit = MaybeUninit::<HasField>::uninit();
/// let mut builder =
///     HasFieldUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
/// builder.read_field([].as_slice()).unwrap();
/// # }
/// ```
fn uninit_builder_read_requires_exact_field_dst() {}
