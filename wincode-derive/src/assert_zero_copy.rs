use {
    crate::common::{extract_repr, SchemaArgs, TraitImpl},
    darling::{ast::Data, Error, FromDeriveInput, Result},
    proc_macro2::TokenStream,
    quote::quote,
    syn::DeriveInput,
};

/// Generate compile-time asserts for `ZeroCopy` impl.
///
/// This function generates assertions to ensure that a struct meets the
/// requirements for implementing the `ZeroCopy` trait:
///   1. The item is indeed a struct (not an enum or union).
///   2. The struct representation is eligible for zero-copy.
///   3. The struct implements `SchemaRead`.
///   4. The struct implements `SchemaWrite`.
///   5. Each field of the struct implements `ZeroCopy`.
///   6. The struct itself has no padding bytes.
///
/// These assertions are enforced at compile-time, providing feedback
/// of any violations of the `ZeroCopy` requirements.
pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let args = SchemaArgs::from_derive_input(&input)?;
    let ident = &args.ident;

    // Assert the item is a struct.
    let zero_copy_asserts = match &args.data {
        Data::Struct(fields) => fields.iter().map(|field| {
            let target = field.target_resolved();
            quote! { assert_zerocopy_impl::<#target>() }
        }),
        _ => return Err(Error::custom("`ZeroCopy` can only be derived for structs")),
    };

    // Assert the struct representation is eligible for zero-copy.
    let repr = extract_repr(&input, TraitImpl::SchemaRead)?;

    if !repr.is_zero_copy_eligible() {
        return Err(Error::custom(
            "The struct representation is not eligible for zero-copy. Consider using \
             #[repr(transparent)] or #[repr(C)] on the struct.",
        ));
    }

    Ok(quote! {
        const _: () = {
            // Assert the struct implements `SchemaRead`.
            const _assert_schema_read_impl: fn() = || {
                fn assert_schema_read_impl<'de, T: ::wincode::SchemaRead<'de>>() {}
                assert_schema_read_impl::<#ident>()
            };

            // Assert the struct implements `SchemaWrite`.
            const _assert_schema_write_impl: fn() = || {
                fn assert_schema_write_impl<T: ::wincode::SchemaWrite>() {}
                assert_schema_write_impl::<#ident>()
            };

            // Assert all fields implement `ZeroCopy`.
            const _assert_zerocopy_impl: fn() = || {
                fn assert_zerocopy_impl<T: ::wincode::ZeroCopy>() {}
                #(#zero_copy_asserts);*
            };

            // Assert the struct has no padding bytes.
            const _assert_no_padding: () = {
                if let ::wincode::TypeMeta::Static { size, .. } = <#ident as ::wincode::SchemaRead<'_>>::TYPE_META {
                    if size != core::mem::size_of::<#ident>() {
                        panic!("derive(ZeroCopy) was applied to a type with padding");
                    }
                } else {
                    panic!("derive(ZeroCopy) was applied to a type with `TypeMeta::Dynamic`");
                }
            };
        };
    })
}
