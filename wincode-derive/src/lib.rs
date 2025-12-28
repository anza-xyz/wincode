//! Derive macros for `SchemaWrite` and `SchemaRead`.
//!
//! Note using this on packed structs is UB.
//!
//! Refer to the [`wincode`](https://docs.rs/wincode) crate for examples.
use {
    proc_macro::TokenStream,
    syn::{parse_macro_input, DeriveInput},
};

mod common;
mod schema_read;
mod schema_write;
mod zero_copy;

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
#[proc_macro_derive(ZeroCopy, attributes(wincode))]
pub fn derive_zero_copy(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match zero_copy::generate(input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.write_errors().into(),
    }
}
