use {
    crate::{
        assert_zero_copy::assert_zero_copy,
        common::{
            default_tag_encoding, extract_repr, get_crate_name, get_src_dst,
            suppress_unused_fields, Field, FieldsExt, SchemaArgs, StructRepr, TraitImpl, Variant,
            VariantsExt,
        },
    },
    darling::{
        ast::{Data, Fields, Style},
        Error, FromDeriveInput, Result,
    },
    proc_macro2::TokenStream,
    quote::quote,
    syn::{
        parse_quote, punctuated::Punctuated, DeriveInput, GenericParam, Generics, PredicateType,
        Token, Type, WherePredicate,
    },
};

fn impl_struct(
    fields: &Fields<Field>,
    repr: &StructRepr,
) -> (TokenStream, TokenStream, TokenStream) {
    if fields.is_empty() {
        return (
            quote! {Ok(0)},
            quote! {Ok(())},
            quote! {
                TypeMeta::Static {
                    size: 0,
                    zero_copy: true,
                }
            },
        );
    }

    let target = fields.unskipped_iter().map(|field| field.target_resolved());
    let mut size_count_idents = Vec::with_capacity(fields.len());

    let writes = fields.struct_members_iter()
        .filter_map(|(field, ident)| {
            if field.skip.is_none() {
                let target = field.target_resolved();
                let write = quote! { <#target as SchemaWrite<WincodeConfig>>::write(writer.by_ref(), &src.#ident)?; };
                size_count_idents.push(ident);
                Some(write)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    let type_meta_impl = fields.type_meta_impl(TraitImpl::SchemaWrite, repr);

    (
        quote! {
            if let TypeMeta::Static { size, .. } = <Self as SchemaWrite<WincodeConfig>>::TYPE_META {
                return Ok(size);
            }
            let mut total = 0usize;
            #(
                total += <#target as SchemaWrite<WincodeConfig>>::size_of(&src.#size_count_idents)?;
            )*
            Ok(total)
        },
        quote! {
            match <Self as SchemaWrite<WincodeConfig>>::TYPE_META {
                TypeMeta::Static { size, .. } => {
                    // SAFETY: `size` is the serialized size of the struct, which is the sum
                    // of the serialized sizes of the fields.
                    // Calling `write` on each field will write exactly `size` bytes,
                    // fully initializing the trusted window.
                    let mut writer = unsafe { writer.as_trusted_for(size) }?;
                    #(#writes)*
                    writer.finish()?;
                }
                TypeMeta::Dynamic => {
                    #(#writes)*
                }
            }
            Ok(())
        },
        type_meta_impl,
    )
}

fn impl_enum(
    enum_ident: &Type,
    variants: &[Variant],
    tag_encoding_override: Option<&Type>,
) -> (TokenStream, TokenStream, TokenStream) {
    if variants.is_empty() {
        return (quote! {Ok(0)}, quote! {Ok(())}, quote! {TypeMeta::Dynamic});
    }
    let mut size_of_impl = Vec::with_capacity(variants.len());
    let mut write_impl = Vec::with_capacity(variants.len());
    let default_tag_encoding = default_tag_encoding();
    let tag_encoding = tag_encoding_override.unwrap_or(&default_tag_encoding);

    let type_meta_impl = variants.type_meta_impl(TraitImpl::SchemaWrite, tag_encoding);

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
                    <#tag_encoding as SchemaWrite<WincodeConfig>>::size_of(&#discriminant)?
                },
                quote! {
                    <#tag_encoding as SchemaWrite<WincodeConfig>>::write(writer.by_ref(), &#discriminant)?
                },
            )
        } else {
            (
                quote! {
                    WincodeConfig::TagEncoding::size_of_from_u32(#discriminant)?
                },
                quote! {
                    WincodeConfig::TagEncoding::write_from_u32(writer.by_ref(), #discriminant)?
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
                            let target = field.target_resolved();
                            let write = quote! {
                                <#target as SchemaWrite<WincodeConfig>>::write(writer.by_ref(), #ident)?;
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
                        #enum_ident::#variant_ident{#(#pattern_fragments),*}
                    }
                } else {
                    quote! {
                        #enum_ident::#variant_ident(#(#pattern_fragments),*)
                    }
                };

                let unskipped_targets =
                    fields.unskipped_iter().map(|field| field.target_resolved());

                // Prefix disambiguation needed, as our match statement will destructure enum variant identifiers.
                let static_anon_idents = fields
                    .unskipped_anon_ident_iter(Some("__"))
                    .collect::<Vec<_>>();
                let static_targets = unskipped_targets
                    .clone()
                    .map(|target| quote! {<#target as SchemaWrite<WincodeConfig>>::TYPE_META})
                    .collect::<Vec<_>>();
                (
                    quote! {
                        #match_case => {
                            if let (TypeMeta::Static { size: disc_size, .. } #(,TypeMeta::Static { size: #static_anon_idents, .. })*) = (<#tag_encoding as SchemaWrite<WincodeConfig>>::TYPE_META #(,#static_targets)*) {
                                return Ok(disc_size + #(#static_anon_idents)+*);
                            }

                            let mut total = #size_of_discriminant;
                            #(
                                total += <#unskipped_targets as SchemaWrite<WincodeConfig>>::size_of(#size_count_idents)?;
                            )*

                            Ok(total)
                        }
                    },
                    quote! {
                        #match_case => {
                            if let (TypeMeta::Static { size: disc_size, .. } #(,TypeMeta::Static { size: #static_anon_idents, .. })*) = (<#tag_encoding as SchemaWrite<WincodeConfig>>::TYPE_META #(,#static_targets)*) {
                                let summed_sizes = disc_size + #(#static_anon_idents)+*;
                                // SAFETY: `summed_sizes` is the sum of the static sizes of the fields + the discriminant size,
                                // which is the serialized size of the variant.
                                // Writing the discriminant and then calling `write` on each field will write
                                // exactly `summed_sizes` bytes, fully initializing the trusted window.
                                let mut writer = unsafe { writer.as_trusted_for(summed_sizes) }?;
                                #write_discriminant;
                                #(#write)*
                                writer.finish()?;
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
                    #enum_ident::#variant_ident => {
                        Ok(#size_of_discriminant)
                    }
                },
                quote! {
                    #enum_ident::#variant_ident => {
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

fn append_config(generics: &mut Generics) {
    generics
        .params
        .push(GenericParam::Type(parse_quote!(WincodeConfig: Config)));
}

fn append_where_clause(generics: &mut Generics) {
    let mut predicates: Punctuated<WherePredicate, Token![,]> = Punctuated::new();
    for param in generics.type_params() {
        let ident = &param.ident;
        let mut bounds = Punctuated::new();
        bounds.push(parse_quote!(SchemaWrite<WincodeConfig, Src = #ident>));

        predicates.push(WherePredicate::Type(PredicateType {
            lifetimes: None,
            bounded_ty: parse_quote!(#ident),
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

fn append_generics(generics: &Generics) -> Generics {
    let mut generics = generics.clone();
    append_where_clause(&mut generics);
    append_config(&mut generics);
    generics
}

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let repr = extract_repr(&input, TraitImpl::SchemaWrite)?;
    let args = SchemaArgs::from_derive_input(&input)?;
    let appended_generics = append_generics(&args.generics);
    let (impl_generics, _, where_clause) = appended_generics.split_for_impl();
    let (_, ty_generics, _) = args.generics.split_for_impl();
    let ident = &args.ident;
    let crate_name = get_crate_name(&args);
    let src_dst = get_src_dst(&args);
    let field_suppress = suppress_unused_fields(&args);
    let zero_copy_asserts = assert_zero_copy(&args, &repr)?;

    let (size_of_impl, write_impl, type_meta_impl) = match &args.data {
        Data::Struct(fields) => {
            if args.tag_encoding.is_some() {
                return Err(Error::custom("`tag_encoding` is only supported for enums"));
            }
            // Only structs are eligible being marked zero-copy, so only the struct
            // impl needs the repr.
            impl_struct(fields, &repr)
        }
        Data::Enum(v) => {
            let enum_ident = match &args.from {
                Some(from) => from,
                None => &parse_quote!(Self),
            };
            impl_enum(enum_ident, v, args.tag_encoding.as_ref())
        }
    };

    Ok(quote! {
        const _: () = {
            use #crate_name::{SchemaWrite, WriteResult, io::Writer, TypeMeta, config::Config, tag_encoding::TagEncoding};
            unsafe impl #impl_generics #crate_name::SchemaWrite<WincodeConfig> for #ident #ty_generics #where_clause {
                type Src = #src_dst;

                #[allow(clippy::arithmetic_side_effects)]
                const TYPE_META: TypeMeta = #type_meta_impl;

                #[inline]
                fn size_of(src: &Self::Src) -> WriteResult<usize> {
                    #size_of_impl
                }

                #[inline]
                fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
                    #write_impl
                }
            }
        };
        #zero_copy_asserts
        #field_suppress
    })
}
