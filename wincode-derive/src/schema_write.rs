use {
    crate::{
        assert_zero_copy::assert_zero_copy,
        common::{
            Field, FieldsExt, SchemaArgs, StructRepr, TraitImpl, Variant, VariantsExt,
            default_tag_encoding, extract_repr, generic_field_types, get_crate_name,
        },
    },
    darling::{
        Error, FromDeriveInput, Result,
        ast::{Data, Fields, Style},
    },
    proc_macro2::TokenStream,
    quote::quote,
    syn::{
        DeriveInput, GenericParam, Generics, Path, PredicateType, Token, Type, WherePredicate,
        parse_quote, punctuated::Punctuated,
    },
};

fn impl_struct(
    fields: &Fields<Field>,
    repr: &StructRepr,
    crate_name: &Path,
) -> (TokenStream, TokenStream, TokenStream) {
    if fields.is_empty() {
        return (
            quote! {Ok(0)},
            quote! {Ok(())},
            quote! {
                #crate_name::TypeMeta::Static {
                    size: 0,
                    zero_copy: true,
                }
            },
        );
    }

    let target = fields
        .unskipped_iter()
        .map(|field| field.target_fully_qualified(TraitImpl::SchemaWrite));
    let mut size_count_idents = Vec::with_capacity(fields.len());

    let writes = fields.struct_members_iter()
        .filter_map(|(field, ident)| {
            if field.skip.is_none() {
                let target = field.target_fully_qualified(TraitImpl::SchemaWrite);
                let write = quote! { #target::write(#crate_name::io::Writer::by_ref(&mut writer), &src.#ident)?; };
                size_count_idents.push(ident);
                Some(write)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    let type_meta_impl = fields.type_meta_impl(TraitImpl::SchemaWrite, repr, crate_name);

    (
        quote! {
            if let #crate_name::TypeMeta::Static { size, .. } = <Self as #crate_name::SchemaWrite<__WincodeConfig>>::TYPE_META {
                return Ok(size);
            }
            let mut total = 0usize;
            #(
                total += #target::size_of(&src.#size_count_idents)?;
            )*
            Ok(total)
        },
        quote! {
            match <Self as #crate_name::SchemaWrite<__WincodeConfig>>::TYPE_META {
                #crate_name::TypeMeta::Static { size, .. } => {
                    // SAFETY: `size` is the serialized size of the struct, which is the sum
                    // of the serialized sizes of the fields.
                    // Calling `write` on each field will write exactly `size` bytes,
                    // fully initializing the trusted window.
                    let mut writer = unsafe { #crate_name::io::Writer::as_trusted_for(&mut writer, size) }?;
                    #(#writes)*
                    #crate_name::io::Writer::finish(&mut writer)?;
                }
                #crate_name::TypeMeta::Dynamic => {
                    #(#writes)*
                }
            }
            Ok(())
        },
        type_meta_impl,
    )
}

fn impl_enum(
    variants: &[Variant],
    tag_encoding_override: Option<&Type>,
    crate_name: &Path,
) -> (TokenStream, TokenStream, TokenStream) {
    if variants.is_empty() {
        return (
            quote! {Ok(0)},
            quote! {Ok(())},
            quote! {#crate_name::TypeMeta::Dynamic},
        );
    }
    let mut size_of_impl = Vec::with_capacity(variants.len());
    let mut write_impl = Vec::with_capacity(variants.len());
    let default_tag_encoding = default_tag_encoding();
    let tag_encoding = tag_encoding_override.unwrap_or(&default_tag_encoding);

    let type_meta_impl = variants.type_meta_impl(TraitImpl::SchemaWrite, tag_encoding, crate_name);

    for (i, variant) in variants.iter().enumerate() {
        let variant_ident = &variant.ident;
        let fields = &variant.fields;
        let discriminant = variant.discriminant(i);
        // Bincode always encodes the discriminant using the index of the field order.
        let (size_of_discriminant, write_discriminant) = if let Some(tag_encoding) =
            tag_encoding_override
        {
            (
                quote! {
                    <#tag_encoding as #crate_name::SchemaWrite<__WincodeConfig>>::size_of(&#discriminant)?
                },
                quote! {
                    <#tag_encoding as #crate_name::SchemaWrite<__WincodeConfig>>::write(#crate_name::io::Writer::by_ref(&mut writer), &#discriminant)?
                },
            )
        } else {
            (
                quote! {
                    <__WincodeConfig::TagEncoding as #crate_name::tag_encoding::TagEncoding<__WincodeConfig>>::size_of_from_u32(#discriminant)?
                },
                quote! {
                    <__WincodeConfig::TagEncoding as #crate_name::tag_encoding::TagEncoding<__WincodeConfig>>::write_from_u32(#crate_name::io::Writer::by_ref(&mut writer), #discriminant)?
                },
            )
        };

        let (size, write) = match fields.style {
            style @ (Style::Struct | Style::Tuple) => {
                let mut pattern_fragments = Vec::with_capacity(fields.len());
                let mut size_count_idents = vec![];

                let write = fields
                    .enum_members_iter(None)
                    .filter_map(|(field, ident)| {
                        if field.skip.is_none() {
                            let target = field.target_fully_qualified(TraitImpl::SchemaWrite);
                            let write = quote! {
                                #target::write(#crate_name::io::Writer::by_ref(&mut writer), #ident)?;
                            };
                            pattern_fragments.push(quote! { #ident });
                            size_count_idents.push(ident);
                            Some(write)
                        } else {
                            if style.is_struct() {
                                pattern_fragments.push(quote! { #ident: _ });
                            } else {
                                pattern_fragments.push(quote! { _ });
                            }
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                let match_case = if style.is_struct() {
                    quote! {
                        Self::#variant_ident{#(#pattern_fragments),*}
                    }
                } else {
                    quote! {
                        Self::#variant_ident(#(#pattern_fragments),*)
                    }
                };

                let unskipped_targets = fields
                    .unskipped_iter()
                    .map(|field| field.target_fully_qualified(TraitImpl::SchemaWrite));

                let static_targets = unskipped_targets
                    .clone()
                    .map(|target| quote! { #target::TYPE_META })
                    .collect::<Vec<_>>();
                (
                    quote! {
                        #match_case => {
                            // Validate the discriminant before the static-size fast path returns.
                            let mut total = #size_of_discriminant;
                            if let #crate_name::TypeMeta::Static { size, .. } = #crate_name::TypeMeta::join_types([<#tag_encoding as #crate_name::SchemaWrite<__WincodeConfig>>::TYPE_META #(,#static_targets)*]) {
                                return Ok(size);
                            }

                            #(
                                total += #unskipped_targets::size_of(#size_count_idents)?;
                            )*

                            Ok(total)
                        }
                    },
                    quote! {
                        #match_case => {
                            if let #crate_name::TypeMeta::Static { size: summed_sizes, .. } = #crate_name::TypeMeta::join_types([<#tag_encoding as #crate_name::SchemaWrite<__WincodeConfig>>::TYPE_META #(,#static_targets)*]) {
                                // SAFETY: `summed_sizes` is the sum of the static sizes of the fields + the discriminant size,
                                // which is the serialized size of the variant.
                                // Writing the discriminant and then calling `write` on each field will write
                                // exactly `summed_sizes` bytes, fully initializing the trusted window.
                                let mut writer = unsafe { #crate_name::io::Writer::as_trusted_for(&mut writer, summed_sizes) }?;
                                #write_discriminant;
                                #(#write)*
                                #crate_name::io::Writer::finish(&mut writer)?;
                                return Ok(());
                            }

                            #write_discriminant;
                            #(#write)*
                            Ok(())
                        }
                    },
                )
            }

            Style::Unit => (
                quote! {
                    Self::#variant_ident => {
                        Ok(#size_of_discriminant)
                    }
                },
                quote! {
                    Self::#variant_ident => {
                        #write_discriminant;
                        Ok(())
                    }
                },
            ),
        };

        size_of_impl.push(size);
        write_impl.push(write);
    }

    (
        quote! {
            match src {
                #(#size_of_impl)*
            }
        },
        quote! {
            match src {
                #(#write_impl)*
            }
        },
        quote! {
           #type_meta_impl
        },
    )
}

fn append_config(generics: &mut Generics, crate_name: &Path) {
    generics.params.push(GenericParam::Type(
        parse_quote!(__WincodeConfig: #crate_name::config::Config),
    ));
}

fn append_where_clause(generics: &mut Generics, data: &Data<Variant, Field>) {
    let field_types = generic_field_types(data, generics);
    let mut predicates: Punctuated<WherePredicate, Token![,]> = Punctuated::new();
    for field in field_types {
        let mut bounds = Punctuated::new();
        let constraint = field.as_constraint(TraitImpl::SchemaWrite);
        bounds.push(parse_quote!(#constraint));
        let target = field.target_resolved();

        predicates.push(WherePredicate::Type(PredicateType {
            lifetimes: None,
            bounded_ty: parse_quote!(#target),
            colon_token: parse_quote![:],
            bounds,
        }));
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
    append_where_clause(&mut generics, data);
    append_config(&mut generics, crate_name);
    generics
}

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let repr = extract_repr(&input, "SchemaWrite")?;
    let args = SchemaArgs::from_derive_input(&input)?;

    let crate_name = get_crate_name(&args);
    let appended_generics = append_generics(&args.generics, &args.data, &crate_name);
    let (impl_generics, _, where_clause) = appended_generics.split_for_impl();
    let (_, ty_generics, _) = args.generics.split_for_impl();
    let ident = &args.ident;
    let zero_copy_asserts = assert_zero_copy(&args, &repr, TraitImpl::SchemaWrite)?;

    let (size_of_impl, write_impl, type_meta_impl) = match &args.data {
        Data::Struct(fields) => {
            if args.tag_encoding.is_some() {
                return Err(Error::custom("`tag_encoding` is only supported for enums"));
            }
            // Only structs are eligible being marked zero-copy, so only the struct
            // impl needs the repr.
            impl_struct(fields, &repr, &crate_name)
        }
        Data::Enum(v) => impl_enum(v, args.tag_encoding.as_ref(), &crate_name),
    };

    Ok(quote! {
        const _: () = {
            unsafe impl #impl_generics #crate_name::SchemaWrite<__WincodeConfig> for #ident #ty_generics #where_clause {
                type Src = Self;

                #[allow(clippy::arithmetic_side_effects)]
                const TYPE_META: #crate_name::TypeMeta = #type_meta_impl;

                #[inline]
                fn size_of(src: &Self::Src) -> #crate_name::WriteResult<usize> {
                    #size_of_impl
                }

                #[inline]
                fn write(mut writer: impl #crate_name::io::Writer, src: &Self::Src) -> #crate_name::WriteResult<()> {
                    #write_impl
                }
            }
        };
        #zero_copy_asserts
    })
}
