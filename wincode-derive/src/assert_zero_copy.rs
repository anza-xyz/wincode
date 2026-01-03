use {
    crate::common::{get_crate_name, SchemaArgs, StructRepr},
    darling::{ast::Data, Error, Result},
    proc_macro2::TokenStream,
    quote::quote,
};

/// Generate compile-time asserts for `ZeroCopy` impl.
///
/// This function generates assertions to ensure that a struct meets the
/// requirements for implementing the `ZeroCopy` trait:
///   1. The item is indeed a struct (not an enum or union).
///   2. The struct representation is eligible for zero-copy.
///   3. The struct implements `SchemaRead`.
///   4. Each field of the struct implements `ZeroCopy`.
///   5. The struct itself has no padding bytes.
///   6. The struct implements `ZeroCopy`.
///
/// These assertions are enforced at compile-time, providing feedback
/// of any violations of the `ZeroCopy` requirements.
pub(crate) fn assert_zero_copy(args: &SchemaArgs, repr: &StructRepr) -> Result<TokenStream> {
    if !args.assert_zero_copy {
        return Ok(quote! {});
    }

    let crate_name = get_crate_name(args);
    let ident = &args.ident;

    // Assert the item is a struct.
    let zero_copy_field_asserts = match &args.data {
        Data::Struct(fields) => fields.iter().map(|field| {
            let target = field.target_resolved();
            quote! { assert_field_zerocopy_impl::<#target>() }
        }),
        _ => return Err(Error::custom("`ZeroCopy` can only be derived for structs")),
    };

    // Assert the struct representation is eligible for zero-copy.
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
                fn assert_schema_read_impl<'de, T: #crate_name::SchemaRead<'de>>() {}
                assert_schema_read_impl::<#ident>()
            };

            // Assert all fields implement `ZeroCopy`.
            const _assert_field_zerocopy_impl: fn() = || {
                fn assert_field_zerocopy_impl<T: #crate_name::ZeroCopy>() {}
                #(#zero_copy_field_asserts);*
            };

            // Assert the struct has no padding bytes.
            const _assert_no_padding: () = {
                if let #crate_name::TypeMeta::Static { size, .. } = <#ident as #crate_name::SchemaRead<'_>>::TYPE_META {
                    if size != core::mem::size_of::<#ident>() {
                        panic!("wincode(assert_zero_copy) was applied to a type with padding");
                    }
                } else {
                    panic!("wincode(assert_zero_copy) was applied to a type with `TypeMeta::Dynamic`");
                }
            };
        };
    })
}
