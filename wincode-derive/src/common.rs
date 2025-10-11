use {
    darling::{
        ast::{Data, Fields},
        Error, FromDeriveInput, FromField, FromVariant, Result,
    },
    proc_macro2::TokenStream,
    quote::quote,
    std::borrow::Cow,
    syn::{
        parse_quote, punctuated::Punctuated, spanned::Spanned, DeriveInput, Generics, Ident,
        Member, Meta, Path, Token, Type, Visibility,
    },
};

#[derive(FromField)]
#[darling(attributes(wincode), forward_attrs)]
pub(crate) struct Field {
    pub(crate) ident: Option<Ident>,
    pub(crate) ty: Type,

    /// Per-field `SchemaRead` and `SchemaWrite` override.
    ///
    /// This is how users can opt in to optimized `SchemaRead` and `SchemaWrite` implementations
    /// for a particular field.
    ///
    /// For example:
    /// ```ignore
    /// struct Foo {
    ///     #[wincode(with = "Pod<_>")]
    ///     x: [u8; u64],
    /// }
    /// ```
    #[darling(default)]
    pub(crate) with: Option<Type>,
}

impl Field {
    /// Get the target type for a field.
    ///
    /// If the field has a `with` attribute, return it.
    /// Otherwise, return the type.
    pub(crate) fn target(&self) -> &Type {
        if let Some(with) = &self.with {
            with
        } else {
            &self.ty
        }
    }

    /// Get the identifier for a struct member.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple struct), return an anonymous identifier with the given index.
    pub(crate) fn struct_member_ident(&self, index: usize) -> Member {
        if let Some(ident) = &self.ident {
            ident.clone().into()
        } else {
            index.into()
        }
    }

    /// Like [`Self::struct_member_ident`], but return a `String`.
    pub(crate) fn struct_member_ident_to_string(&self, index: usize) -> String {
        if let Some(ident) = &self.ident {
            ident.to_string()
        } else {
            index.to_string()
        }
    }

    /// Get an iterator over the identifiers for the struct members.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple struct), return an anonymous identifier.
    pub(crate) fn struct_member_ident_iter(
        fields: &Fields<Self>,
    ) -> impl Iterator<Item = Member> + use<'_> {
        fields
            .iter()
            .enumerate()
            .map(|(i, f)| f.struct_member_ident(i))
    }

    /// Get an iterator over the identifiers for the enum members.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple enum), return an anonymous identifier.
    ///
    /// Note this is unnecessary for unit enums, as they will not have fields.
    pub(crate) fn enum_member_ident_iter(
        fields: &Fields<Self>,
    ) -> impl Iterator<Item = Cow<'_, Ident>> + Clone + use<'_> {
        let mut alpha = ('a'..='z').cycle();
        fields.iter().map(move |field| {
            if let Some(ident) = &field.ident {
                Cow::Borrowed(ident)
            } else {
                let char_byte = [alpha.next().unwrap() as u8];
                let str = core::str::from_utf8(&char_byte).unwrap();
                let ident = Ident::new(str, field.ident.span());

                Cow::Owned(ident)
            }
        })
    }
}

#[derive(FromVariant)]
#[darling(attributes(wincode), forward_attrs)]
pub(crate) struct Variant {
    pub(crate) ident: Ident,
    pub(crate) fields: Fields<Field>,
}

pub(crate) type ImplBody = Data<Variant, Field>;

/// Generate code to suppress unused field lints.
///
/// If `from` is specified, the user is creating a mapping type, in which case those struct/enum
/// fields will almost certainly be unused, as they exist purely to describe the mapping. This will
/// trigger unused field lints.
///
/// Create a private, never-called item that references the fields to avoid unused field lints.
/// Users can disable this by setting `no_suppress_unused`.
pub(crate) fn suppress_unused_fields(args: &SchemaArgs) -> TokenStream {
    if args.from.is_none() || args.no_suppress_unused {
        return quote! {};
    }

    match &args.data {
        Data::Struct(fields) if !fields.is_empty() => {
            let idents = Field::struct_member_ident_iter(fields);
            let ident = &args.ident;
            let (impl_generics, ty_generics, where_clause) = args.generics.split_for_impl();
            quote! {
                const _: () = {
                    #[allow(dead_code, unused_variables)]
                    fn __wincode_use_fields #impl_generics (value: &#ident #ty_generics) #where_clause {
                        let _ = ( #( &value.#idents ),* );
                    }
                };
            }
        }
        // We can't suppress the lint on on enum variants, as that would require being able to
        // construct an arbitrary enum variant, which we can't do. Users will have to manually
        // add a `#[allow(unused)]` / `#[allow(dead_code)]` attribute to the enum variant if they want to
        // suppress the lint, or make it public.
        _ => {
            quote! {}
        }
    }
}

/// Get the path to `wincode` based on the `internal` flag.
pub(crate) fn get_crate_name(args: &SchemaArgs) -> Path {
    if args.internal {
        parse_quote!(crate)
    } else {
        parse_quote!(::wincode)
    }
}

/// Get the target `Src` or `Dst` type for a `SchemaRead` or `SchemaWrite` implementation.
///
/// If `from` is specified, the user is implementing `SchemaRead` or `SchemaWrite` on a foreign type,
/// so we return the `from` type.
/// Otherwise, we return the ident + ty_generics (target is `Self`).
pub(crate) fn get_src_dst(args: &SchemaArgs) -> Cow<'_, Type> {
    if let Some(from) = args.from.as_ref() {
        Cow::Borrowed(from)
    } else {
        Cow::Owned(parse_quote!(Self))
    }
}

/// Get the fully qualified target `Src` or `Dst` type for a `SchemaRead` or `SchemaWrite` implementation.
///
/// Like [`Self::get_src_dst`], but rather than producing `Self` when implementing a local type,
/// we return the fully qualified type.
pub(crate) fn get_src_dst_fully_qualified(args: &SchemaArgs) -> Cow<'_, Type> {
    if let Some(from) = args.from.as_ref() {
        Cow::Borrowed(from)
    } else {
        let ident = &args.ident;
        let (_, ty_generics, _) = args.generics.split_for_impl();
        Cow::Owned(parse_quote!(#ident #ty_generics))
    }
}

#[derive(FromDeriveInput)]
#[darling(attributes(wincode), forward_attrs)]
pub(crate) struct SchemaArgs {
    pub(crate) ident: Ident,
    pub(crate) generics: Generics,
    pub(crate) data: ImplBody,
    pub(crate) vis: Visibility,

    /// Used to determine the `wincode` path.
    ///
    /// If `internal` is `true`, the generated code will use the `crate::` path.
    /// Otherwise, it will use the `wincode` path.
    #[darling(default)]
    pub(crate) internal: bool,
    /// Specifies whether the type's implementations should map to another type.
    ///
    /// Useful for implementing `SchemaRead` and `SchemaWrite` on foreign types.
    #[darling(default)]
    pub(crate) from: Option<Type>,
    /// Specifies whether to suppress unused field lints on structs.
    ///
    /// Only applicable if `from` is specified.
    #[darling(default)]
    pub(crate) no_suppress_unused: bool,
    /// Specifies whether to generate placement initialization struct helpers on `SchemaRead` implementations.
    #[darling(default)]
    pub(crate) struct_extensions: bool,
}

/// Reject deriving on `#[repr(packed)]` types, as this is UB.
pub(crate) fn ensure_not_repr_packed(input: &DeriveInput, trait_name: &str) -> Result<()> {
    for attr in &input.attrs {
        if !attr.path().is_ident("repr") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("packed") {
                return Err(meta.error(format!(
                    "`{trait_name}` cannot be derived for types annotated with \
                     `#[repr(packed)]` or `#[repr(packed(n))]`"
                )));
            }

            // Don't leave unparsed input behind
            let _ = meta.input.parse::<TokenStream>();

            Ok(())
        })?;
    }
    Ok(())
}
