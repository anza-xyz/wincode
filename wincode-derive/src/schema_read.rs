use {
    crate::{
        assert_zero_copy::assert_zero_copy,
        common::{
            Field, FieldsExt, GenericField, SchemaArgs, StructRepr, TraitImpl, TypeExt, Variant,
            VariantsExt, default_tag_encoding, extract_repr, generic_field_types, get_crate_name,
            get_src_dst, get_src_dst_fully_qualified, suppress_unused_fields,
        },
        uninit_builder::impl_uninit_builder,
    },
    darling::{
        Error, FromDeriveInput, Result,
        ast::{Data, Fields, Style},
    },
    proc_macro2::{Literal, TokenStream},
    quote::{quote, quote_spanned},
    syn::{
        DeriveInput, GenericParam, Generics, Path, PredicateType, Token, Type, WhereClause,
        WherePredicate, parse_quote, punctuated::Punctuated,
    },
};

fn impl_struct(
    args: &SchemaArgs,
    fields: &Fields<Field>,
    repr: &StructRepr,
    crate_name: &Path,
) -> (TokenStream, TokenStream) {
    if fields.is_empty() {
        return (
            quote! {},
            quote! { #crate_name::TypeMeta::Static {
                size: 0,
                zero_copy: true,
            }},
        );
    }

    let num_fields = fields.len();
    let read_impl = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let ident = field.struct_member_ident(i);
            let target = field.target_resolved().with_lifetime("de");
            let hint = if field.with.is_some() {
                // Fields annotated with `with` may need help determining the pointer cast.
                //
                // This allows correct inference in `with` attributes, for example:
                // ```
                // struct Foo {
                //     #[wincode(with = "Pod<_>")]
                //     x: [u8; u64],
                // }
                // ```
                let ty = field.ty.with_lifetime("de");
                quote! { ::core::mem::MaybeUninit<#ty> }
            } else {
                quote! { ::core::mem::MaybeUninit<_> }
            };
            let init_count = if i == num_fields - 1 {
                quote! {}
            } else {
                quote! { *init_count += 1; }
            };
            if let Some(mode) = &field.skip {
                let val = mode.default_val_token_stream();
                quote! {
                    unsafe { (&raw mut (*dst_ptr).#ident).write(#val); }
                    #init_count
                }
            } else {
                quote! {
                    <#target as #crate_name::SchemaRead<'de, __WincodeConfig>>::read(
                        #crate_name::io::Reader::by_ref(&mut reader),
                        unsafe { &mut *(&raw mut (*dst_ptr).#ident).cast::<#hint>() }
                    )?;
                    #init_count
                }
            }
        })
        .collect::<Vec<_>>();

    let type_meta_impl = fields.type_meta_impl(TraitImpl::SchemaRead, repr, crate_name);

    let drop_guard = (0..fields.len()).map(|i| {
        // Generate code to drop already initialized fields in reverse order.
        let drop = fields.fields[..i]
            .iter()
            .rev()
            .enumerate()
            .map(|(j, field)| {
                let ident = field.struct_member_ident(i - 1 - j);
                quote! {
                    ::core::ptr::drop_in_place(&raw mut (*dst_ptr).#ident);
                }
            });
        let cnt = Literal::usize_unsuffixed(i);
        if i == 0 {
            quote! {
                0 => {}
            }
        } else {
            quote! {
                #cnt => {
                    unsafe { #(#drop)* }
                }
            }
        }
    });

    let counter_ty: Type = match fields.len().saturating_sub(1) {
        len if len <= u8::MAX as usize => parse_quote! { u8 },
        len if len <= u16::MAX as usize => parse_quote! { u16 },
        len if len <= u32::MAX as usize => parse_quote! { u32 },
        len if len <= u64::MAX as usize => parse_quote! { u64 },
        _ => panic!("Unsupported number of fields: {}", fields.len()),
    };

    let dst = get_src_dst_fully_qualified(args);
    let (impl_generics, ty_generics, where_clause) = args.generics.split_for_impl();
    let init_guard = quote! {
        let dst_ptr = dst.as_mut_ptr();
        let mut guard = __WincodeDropGuard {
            init_count: 0,
            dst_ptr,
        };
        let init_count = &mut guard.init_count;
    };
    (
        quote! {
            struct __WincodeDropGuard #impl_generics #where_clause {
                init_count: #counter_ty,
                dst_ptr: *mut #dst,
            }

            impl #impl_generics ::core::ops::Drop for __WincodeDropGuard #ty_generics #where_clause {
                #[cold]
                fn drop(&mut self) {
                    let dst_ptr = self.dst_ptr;
                    let init_count = self.init_count;
                    match init_count {
                        #(#drop_guard)*
                        // Impossible, given the `init_count` is bounded by the number of fields.
                        _ => { debug_assert!(false, "init_count out of bounds"); },
                    }
                }
            }

            match <Self as #crate_name::SchemaRead<'de, __WincodeConfig>>::TYPE_META {
                #crate_name::TypeMeta::Static { size, .. } => {
                    // SAFETY: `size` is the serialized size of the struct, which is the sum
                    // of the serialized sizes of the fields.
                    // Calling `read` on each field will consume exactly `size` bytes,
                    // fully consuming the trusted window.
                    let mut reader = unsafe { #crate_name::io::Reader::as_trusted_for(&mut reader, size) }?;
                    #init_guard
                    #(#read_impl)*
                    ::core::mem::forget(guard);
                }
                #crate_name::TypeMeta::Dynamic => {
                    #init_guard
                    #(#read_impl)*
                    ::core::mem::forget(guard);
                }
            }
        },
        quote! {
            #type_meta_impl
        },
    )
}

fn impl_enum(
    enum_ident: &Type,
    variants: &[Variant],
    tag_encoding_override: Option<&Type>,
    crate_name: &Path,
) -> (TokenStream, TokenStream) {
    if variants.is_empty() {
        return (
            quote! { return Err(#crate_name::error::invalid_value("cannot deserialize uninhabited enum")); },
            quote! { #crate_name::TypeMeta::Dynamic },
        );
    }

    let type_meta_impl = variants.type_meta_impl(
        TraitImpl::SchemaRead,
        tag_encoding_override.unwrap_or(&default_tag_encoding()),
        crate_name,
    );

    let read_impl = variants.iter().enumerate().map(|(i, variant)| {
        let variant_ident = &variant.ident;
        let fields = &variant.fields;
        let discriminant = variant.discriminant(i);

        match fields.style {
            style @ (Style::Struct | Style::Tuple) => {
                // No prefix disambiguation needed, as we are matching on a discriminant integer.
                let mut construct_idents = Vec::with_capacity(fields.len());
                let read = fields.enum_members_iter(None)
                    .map(|(field, ident)| {
                        let target = field.target_resolved().with_lifetime("de");

                        // Unfortunately we can't avoid temporaries for arbitrary enums, as Rust does not provide
                        // facilities for placement initialization on enums.
                        //
                        // In the future, we may be able to support an attribute that allows users to opt into
                        // a macro-generated shadowed enum that wraps all variant fields with `MaybeUninit`, which
                        // could be used to facilitate direct reads. The user would have to guarantee layout on
                        // their type (a la `#[repr(C)]`), or roll the dice on non-guaranteed layout -- so it would need to be opt-in.
                        let read = if let Some(mode) = &field.skip {
                            let val = mode.default_val_token_stream();
                            quote! { let #ident = #val; }
                        } else {
                            quote! {
                                let #ident = <#target as #crate_name::SchemaRead<'de, __WincodeConfig>>::get(#crate_name::io::Reader::by_ref(&mut reader))?;
                            }
                        };
                        construct_idents.push(ident);
                        read
                    })
                    .collect::<Vec<_>>();

                // No prefix disambiguation needed, as we are matching on a discriminant integer.
                let static_targets = fields.unskipped_iter().map(|field| {
                    let target = field.target_resolved().with_lifetime("de");
                    quote! {<#target as #crate_name::SchemaRead<'de, __WincodeConfig>>::TYPE_META}
                });

                let constructor = if style.is_struct() {
                    quote! {
                        #enum_ident::#variant_ident{#(#construct_idents),*}
                    }
                } else {
                    quote! {
                        #enum_ident::#variant_ident(#(#construct_idents),*)
                    }
                };

                quote! {
                    #discriminant => {
                        if let #crate_name::TypeMeta::Static { size: summed_sizes, .. } = #crate_name::TypeMeta::join_types([#(#static_targets),*]) {
                            // SAFETY: `summed_sizes` is the sum of the static sizes of the fields,
                            // which is the serialized size of the variant.
                            // Calling `read` on each field will consume exactly `summed_sizes` bytes,
                            // fully consuming the trusted window.
                            let mut reader = unsafe { #crate_name::io::Reader::as_trusted_for(&mut reader, summed_sizes) }?;
                            #(#read)*
                            dst.write(#constructor);
                        } else {
                            #(#read)*
                            dst.write(#constructor);
                        }
                    }
                }
            }

            Style::Unit => quote! {
                #discriminant => {
                    dst.write(#enum_ident::#variant_ident);
                }
            },
        }
    });

    let read_discriminant = if let Some(tag_encoding) = tag_encoding_override {
        quote! {
            <#tag_encoding as #crate_name::SchemaRead<'de, __WincodeConfig>>::get(#crate_name::io::Reader::by_ref(&mut reader))?;
        }
    } else {
        quote! {
            <__WincodeConfig::TagEncoding as #crate_name::tag_encoding::TagEncoding<__WincodeConfig>>::try_into_u32(
                <__WincodeConfig::TagEncoding as #crate_name::SchemaRead<'de, __WincodeConfig>>::get(#crate_name::io::Reader::by_ref(&mut reader))?,
            )?
        }
    };

    (
        quote! {
            let discriminant = #read_discriminant;
            match discriminant {
                #(#read_impl)*
                _ => return Err(#crate_name::error::invalid_tag_encoding(discriminant as usize)),
            }
        },
        quote! {
            #type_meta_impl
        },
    )
}

/// Extend the `'de` lifetime to all lifetime parameters in the generics.
///
/// This enforces that the `SchemaRead` lifetime (`'de`) and thus its
/// `Reader<'de>` (the source bytes) extends to all lifetime parameters
/// in the derived type.
///
/// For example, given the following type:
/// ```
/// struct Foo<'a> {
///     x: &'a str,
/// }
/// ```
///
/// We must ensure `'de` outlives all other lifetimes in the generics.
fn append_de_lifetime(generics: &mut Generics) {
    if generics.lifetimes().next().is_none() {
        generics
            .params
            .push(GenericParam::Lifetime(parse_quote!('de)));
        return;
    }

    let lifetimes = generics.lifetimes();
    // Ensure `'de` outlives other lifetimes in the generics.
    generics
        .params
        .push(GenericParam::Lifetime(parse_quote!('de: #(#lifetimes)+*)));
}

fn append_config(generics: &mut Generics, crate_name: &Path) {
    generics.params.push(GenericParam::Type(
        parse_quote!(__WincodeConfig: #crate_name::config::Config),
    ));
}

fn append_where_clause(generics: &mut Generics, data: &Data<Variant, Field>, crate_name: &Path) {
    let field_types = generic_field_types(data, generics);
    let mut predicates: Punctuated<WherePredicate, Token![,]> = Punctuated::new();
    for GenericField { target, ty } in &field_types {
        let mut bounds = Punctuated::new();
        bounds.push(parse_quote!(#crate_name::SchemaRead<'de, __WincodeConfig, Dst = #ty>));

        predicates.push(WherePredicate::Type(PredicateType {
            lifetimes: None,
            bounded_ty: parse_quote!(#target),
            colon_token: parse_quote![:],
            bounds,
        }));
    }

    /// Append an additional constraint to the where clause such that
    /// `SchemaRead<'de, __WincodeConfig>` is implemented for the given
    /// field's type.
    ///
    /// This constraint is only necessary for fields whose types contain lifetimes.
    /// In particular, for an arbitrary `T`, `SchemaRead<Config>` is _only_
    /// implemented for `&T` where `T` is `ZeroCopy<Config>`. In other words, because
    /// there is no blanket implementation for `SchemaRead<Config>` on `&T`, we must
    /// add constraints to the where clause such that `&T` satisfies `SchemaRead<Config>`
    /// or the derived implementation will not type-check.
    fn constrain_reference_type(
        field: &Field,
        predicates: &mut Punctuated<WherePredicate, Token![,]>,
        crate_name: &Path,
    ) {
        let ty = &field.ty.with_lifetime("de");
        let target = field.target_resolved().with_lifetime("de");
        let mut bounds = Punctuated::new();
        bounds.push(parse_quote!(#crate_name::SchemaRead<'de, __WincodeConfig, Dst = #ty>));
        predicates.push(WherePredicate::Type(PredicateType {
            lifetimes: None,
            bounded_ty: target,
            colon_token: parse_quote![:],
            bounds,
        }));
    }

    match data {
        Data::Struct(fields) => {
            for field in fields.fields_with_lifetime_iter() {
                constrain_reference_type(field, &mut predicates, crate_name);
            }
        }
        Data::Enum(variants) => {
            for variant in variants {
                for field in variant.fields.fields_with_lifetime_iter() {
                    constrain_reference_type(field, &mut predicates, crate_name);
                }
            }
        }
    }

    if predicates.is_empty() {
        return;
    }
    let where_clause = generics.make_where_clause();
    where_clause.predicates.extend(predicates);
}

fn append_generics(
    generics: &Generics,
    data: &Data<Variant, Field>,
    crate_name: &Path,
) -> Generics {
    let mut generics = generics.clone();
    append_de_lifetime(&mut generics);
    append_where_clause(&mut generics, data, crate_name);
    append_config(&mut generics, crate_name);
    generics
}

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let repr = extract_repr(&input, "SchemaRead")?;
    let args = SchemaArgs::from_derive_input(&input)?;
    let crate_name = get_crate_name(&args);
    let appended_generics = append_generics(&args.generics, &args.data, &crate_name);
    let (impl_generics, _, where_clause) = appended_generics.split_for_impl();
    let (_, ty_generics, _) = args.generics.split_for_impl();
    let ident = &args.ident;
    let src_dst = get_src_dst(&args);
    let field_suppress = suppress_unused_fields(&args);
    let struct_extensions = if args.struct_extensions {
        let tokens = impl_uninit_builder(&args, &crate_name)?;
        let deprecation = quote_spanned! {args.ident.span()=>
            const _: () = {
                #[deprecated(note = "#[wincode(struct_extensions)] is deprecated; use #[derive(UninitBuilder)] instead")]
                const __WINCODE_STRUCT_EXTENSIONS_DEPRECATED: () = ();
                const _: () = __WINCODE_STRUCT_EXTENSIONS_DEPRECATED;
            };
        };

        quote! {
            #deprecation
            #tokens
        }
    } else {
        quote!()
    };
    let zero_copy_asserts = assert_zero_copy(&args, &repr)?;

    let (read_impl, type_meta_impl) = match &args.data {
        Data::Struct(fields) => {
            if args.tag_encoding.is_some() {
                return Err(Error::custom("`tag_encoding` is only supported for enums"));
            }
            // Only structs are eligible being marked zero-copy, so only the struct
            // impl needs the repr.
            impl_struct(&args, fields, &repr, &crate_name)
        }
        Data::Enum(v) => {
            let enum_ident = match &args.from {
                Some(from) => from,
                None => &parse_quote!(Self),
            };
            impl_enum(enum_ident, v, args.tag_encoding.as_ref(), &crate_name)
        }
    };

    // Provide a `ZeroCopy` impl for the type if its `repr` is eligible and all its fields are zero-copy.
    let zero_copy_impl = match &args.data {
        Data::Struct(fields)
            if repr.is_zero_copy_eligible()
                // Generics will trigger "cannot use type generics in const context".
                // Unfortunate, but generics in a zero-copy context are presumably a more niche use-case,
                // so we'll deal with it for now.
                && args.generics.type_params().next().is_none()
                // Types containing references are not zero-copy eligible.
                && args.generics.lifetimes().next().is_none() =>
        {
            let field_tys = fields.iter().map(|field| &field.ty);
            let mut bounds = Punctuated::new();
            bounds.push(parse_quote!(__WincodeIsTrue));
            let no_pad_predicate = WherePredicate::Type(PredicateType {
                // Workaround for https://github.com/rust-lang/rust/issues/48214.
                lifetimes: Some(parse_quote!(for<'_wincode_internal>)),
                // Types are only zero-copy if they do not have any padding.
                bounded_ty: parse_quote!(
                    __WincodeAssert<
                        {
                            #(core::mem::size_of::<#field_tys>())+* == core::mem::size_of::<#ident>()
                        },
                    >
                ),
                colon_token: parse_quote![:],
                bounds,
            });

            let field_targets = fields.iter().map(|field| field.target_resolved());
            let mut bounds = Punctuated::new();
            bounds.push(parse_quote!(#crate_name::config::ZeroCopy<__WincodeConfig>));
            let zero_copy_predicate = field_targets.into_iter().map(|target| {
                WherePredicate::Type(PredicateType {
                    // Workaround for https://github.com/rust-lang/rust/issues/48214.
                    lifetimes: Some(parse_quote!(for<'_wincode_internal>)),
                    // Each field must be zero-copy.
                    bounded_ty: target,
                    colon_token: parse_quote![:],
                    bounds: bounds.clone(),
                })
            });

            let predicates = zero_copy_predicate.chain(core::iter::once(no_pad_predicate));
            let mut generics = args.generics.clone();
            append_config(&mut generics, &crate_name);
            let (impl_generics, _, _) = generics.split_for_impl();
            let (_, ty_generics, where_clause) = args.generics.split_for_impl();
            let mut where_clause = where_clause.cloned();
            match &mut where_clause {
                Some(where_clause) => {
                    where_clause.predicates.extend(predicates);
                }
                None => {
                    where_clause = Some(WhereClause {
                        where_token: parse_quote!(where),
                        predicates: Punctuated::from_iter(predicates),
                    });
                }
            }

            quote! {
                // Ugly, but functional.
                struct __WincodeAssert<const B: bool>;
                trait __WincodeIsTrue {}
                impl __WincodeIsTrue for __WincodeAssert<true> {}
                unsafe impl #impl_generics #crate_name::config::ZeroCopy<__WincodeConfig> for #ident #ty_generics #where_clause {}
            }
        }
        _ => quote!(),
    };

    Ok(quote! {
        const _: () = {
            #zero_copy_impl

            unsafe impl #impl_generics #crate_name::SchemaRead<'de, __WincodeConfig> for #ident #ty_generics #where_clause {
                type Dst = #src_dst;

                #[allow(clippy::arithmetic_side_effects)]
                const TYPE_META: #crate_name::TypeMeta = #type_meta_impl;

                #[inline]
                fn read(mut reader: impl #crate_name::io::Reader<'de>, dst: &mut ::core::mem::MaybeUninit<Self::Dst>) -> #crate_name::ReadResult<()> {
                    #read_impl
                    Ok(())
                }
            }
        };
        #zero_copy_asserts
        #struct_extensions
        #field_suppress
    })
}
