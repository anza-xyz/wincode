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

/// Assert that a struct is zero-copy deserializable.
#[proc_macro_attribute]
pub fn assert_zero_copy(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item_struct = parse_macro_input!(item as DeriveInput);

    let result = match assert_zero_copy::generate(item_struct.clone()) {
        Ok(asserts) => asserts,
        Err(e) => e.write_errors(),
    };

    quote::quote! {
        #item_struct
        #result
    }
    .into()
}
