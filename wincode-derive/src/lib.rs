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
mod struct_extensions;

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
/// This adds some convenience methods to structs that can avoid a lot of boilerplate when
/// implementing custom `SchemaRead` implementations. In particular, provide methods that
/// deal with projecting subfields of structs into `MaybeUninit`s. Without this,
/// users have to write a litany of `&mut *(&raw mut (*dst_ptr).field).cast()` to
/// access MaybeUninit struct fields.
///
/// For example:
/// ```ignore
/// #[derive(SchemaRead)]
/// struct Header {
///     num_required_signatures: u8,
///     num_signed_accounts: u8,
///     num_unsigned_accounts: u8,
/// }
///
/// #[derive(SchemaRead)]
/// struct Body {
///     header: Header,
/// }
///
/// #[struct_extensions]
/// struct Message {
///     body: Body,
/// }
///
/// unsafe impl<'de, C: Config> SchemaRead<'de, C> for Message {
///     type Dst = Message;
///
///     fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
///         let msg = MessageUninitBuilder::<C>::from_maybe_uninit_mut(&mut dst);
///         // ...
///     }
/// }
/// ```
///
/// We cannot do this for enums, given the lack of facilities for placement initialization.
#[proc_macro_attribute]
pub fn struct_extensions(attr: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match struct_extensions::generate(attr.into(), input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.write_errors().into(),
    }
}
