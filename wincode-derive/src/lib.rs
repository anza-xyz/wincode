//! Derive macros for `SchemaWrite` and `SchemaRead`.
//!
//! Note using this on packed structs is UB.
//!
//! Refer to the [`wincode`](https://docs.rs/wincode) crate for examples.
use {
    proc_macro::TokenStream,
    syn::{parse_macro_input, DeriveInput},
};

mod assert_zero_copy;
mod common;
mod schema_read;
mod schema_write;
mod uninit_builder;

/// Implement `SchemaWrite` for a struct or enum.
#[proc_macro_derive(SchemaWrite, attributes(wincode))]
pub fn derive_schema_write(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match schema_write::generate(input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.write_errors().into(),
    }
}

/// Implement `SchemaRead` for a struct or enum.
#[proc_macro_derive(SchemaRead, attributes(wincode))]
pub fn derive_schema_read(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match schema_read::generate(input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.write_errors().into(),
    }
}

/// Include placement initialization helpers for structs.
///
/// This generates an `UninitBuilder` for the given struct, providing convenience
/// methods that can avoid a lot of boilerplate when implementing custom
/// `SchemaRead` implementations. In particular, it provides methods that
/// deal with projecting subfields of structs into `MaybeUninit`s. Without this,
/// one would have to write a litany of `&mut *(&raw mut (*dst_ptr).field).cast()` to
/// access MaybeUninit struct fields. It also provides initialization helpers and
/// drop tracking logic.
///
/// For example:
/// ```ignore
/// #[derive(UninitBuilder)]
/// struct Message {
///     payload: Vec<u8>,
///     bytes: [u8; 32],
/// }
///
/// unsafe impl<'de, C: Config> SchemaRead<'de, C> for Message {
///     type Dst = Self;
///
///     fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
///         let msg_builder = MessageUninitBuilder::<C>::from_maybe_uninit_mut(dst);
///         // Deserializes a `Vec<u8>` into the `payload` slot of `Message` and marks the field
///         // as initialized. If the subsequent `read_bytes` call fails, the `payload` field will
///         // be dropped.
///         msg_builder.read_payload(reader.by_ref())?;
///         msg_builder.read_bytes(reader)?;
///         msg_builder.finish();
///     }
/// }
/// ```
///
/// We cannot do this for enums, given the lack of facilities for placement initialization.
#[proc_macro_derive(UninitBuilder, attributes(wincode))]
pub fn derive_uninit_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match uninit_builder::generate(input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.write_errors().into(),
    }
}
