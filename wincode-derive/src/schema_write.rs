use {
    crate::{
        assert_zero_copy::assert_zero_copy,
        common::{
            Field, FieldsExt, SchemaArgs, StructRepr, TraitImpl, Variant, VariantsExt,
            default_tag_encoding, extract_repr, generic_field_types, get_crate_name,
            move_bounds_to_where, turbofish_without_lifetimes,
        },
    },
    darling::{
        Error, FromDeriveInput, Result,
        ast::{Data, Fields, Style},
    },
    proc_macro2::{Span, TokenStream},
    quote::quote,
    syn::{
        DeriveInput, GenericParam, Generics, Ident, Path, PredicateType, Token, Type,
        WherePredicate, parse_quote, punctuated::Punctuated,
    },
};

fn impl_struct(
    fields: &Fields<Field>,
    repr: &StructRepr,
    crate_name: &Path,
    impl_generics: &Generics,
    self_ty: &TokenStream,
) -> (
    TokenStream,
    TokenStream,
    TokenStream,
    Vec<TokenStream>,
    Vec<TokenStream>,
) {
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
            Vec::new(),
            Vec::new(),
        );
    }

    // Chain functions are free fns carrying the impl's own generics and where clause, so they
    // name the field schemas exactly as the impl does.
    let (chain_generics, _, chain_where) = impl_generics.split_for_impl();

    let metas = fields.plan_metas(TraitImpl::SchemaWrite, crate_name);
    // Each field's target type and member. One entry per declaration, so an index here is also
    // an index into the plan; a skipped field keeps its slot and holds none, rather than being
    // filtered out.
    let write_targets = fields
        .struct_members_iter()
        .map(|(field, ident)| match field.skip {
            Some(_) => None,
            None => Some((field.target_fully_qualified(TraitImpl::SchemaWrite), ident)),
        })
        .collect::<Vec<_>>();

    let chain_name =
        |index: usize| Ident::new(&format!("__wincode_write_chain_{index}"), Span::call_site());
    let write_through = |write: &Option<_>| {
        write.as_ref().map(|(target, ident)| {
            quote! {
                #target::write(#crate_name::io::Writer::by_ref(&mut writer), &src.#ident)?;
            }
        })
    };

    // Path to the write plan, shared by the guards below, which look up each field by index.
    let plan = quote!(<#self_ty as #crate_name::WriteFieldPlan<__WincodeConfig>>::PLAN);

    let chain_turbofish = turbofish_without_lifetimes(impl_generics);

    // One chain function per field, handing off to the next field's chain fn while its window
    // continues, so emission stays linear.
    let chain_fns = write_targets
        .iter()
        .enumerate()
        .map(|(index, write)| {
            let name = chain_name(index);
            let body = write_through(write);
            let next = (index + 1 < fields.len()).then(|| {
                let next_name = chain_name(index + 1);
                let next_index = index + 1;
                quote! {
                    if const { #plan[#next_index].is_in_window() } {
                        return #next_name #chain_turbofish(writer, src);
                    }
                }
            });
            quote! {
                #[inline(always)]
                fn #name #chain_generics(
                    mut writer: impl #crate_name::io::Writer,
                    src: &#self_ty,
                ) -> #crate_name::WriteResult<()>
                #chain_where
                {
                    #body
                    #next
                    Ok(())
                }
            }
        })
        .collect::<Vec<_>>();

    // An entry point per declaration, since any of them may open a window; the chain covers
    // the rest.
    let write_steps = write_targets
        .iter()
        .enumerate()
        .map(|(index, write)| {
            let name = chain_name(index);
            let direct = write_through(write);
            quote! {
                if const { #plan[#index].opens_window() } {
                    // Starts the chain that writes this field and every static one after it.
                    // SAFETY: the run's size is the sum of the serialized sizes of the fields it
                    // covers, which are each statically sized. The chain writes exactly those
                    // fields, so it fills the trusted window exactly once.
                    let size = const { #plan[#index].window_size() };
                    let mut window =
                        unsafe { #crate_name::io::Writer::as_trusted_for(&mut writer, size) }?;
                    #name #chain_turbofish(#crate_name::io::Writer::by_ref(&mut window), src)?;
                    #crate_name::io::Writer::finish(&mut window)?;
                } else if const { #plan[#index].is_direct() } {
                    #direct
                }
            }
        })
        .collect::<Vec<_>>();

    // Terms of the `size_of` sum, one per field that is actually written.
    let (targets, size_count_idents): (Vec<_>, Vec<_>) =
        write_targets.into_iter().flatten().unzip();

    let type_meta_impl = fields.type_meta_impl(TraitImpl::SchemaWrite, repr, crate_name);

    (
        quote! {
            if let #crate_name::TypeMeta::Static { size, .. } = <Self as #crate_name::SchemaWrite<__WincodeConfig>>::TYPE_META {
                return Ok(size);
            }
            let mut total = 0usize;
            #(
                total += #targets::size_of(&src.#size_count_idents)?;
            )*
            Ok(total)
        },
        quote! {
            #(#write_steps)*
            Ok(())
        },
        type_meta_impl,
        metas,
        chain_fns,
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
    move_bounds_to_where(&mut generics);
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
    let zero_copy_asserts = assert_zero_copy(&args, &repr)?;

    let self_ty = quote! { #ident #ty_generics };

    let (size_of_impl, write_impl, type_meta_impl, metas, chain_fns) = match &args.data {
        Data::Struct(fields) => {
            if args.tag_encoding.is_some() {
                return Err(Error::custom("`tag_encoding` is only supported for enums"));
            }
            // Only structs are eligible being marked zero-copy, so only the struct
            // impl needs the repr.
            impl_struct(fields, &repr, &crate_name, &appended_generics, &self_ty)
        }
        Data::Enum(v) => {
            let (size_of, write, meta) = impl_enum(v, args.tag_encoding.as_ref(), &crate_name);
            (size_of, write, meta, Vec::new(), Vec::new())
        }
    };

    let plan_impl = (!metas.is_empty()).then(|| {
        quote! {
            impl #impl_generics #crate_name::WriteFieldPlan<__WincodeConfig> for #ident #ty_generics
                #where_clause
            {
                const PLAN: &'static [#crate_name::FieldPlan] =
                    &#crate_name::TypeMeta::field_plan([#(#metas),*]);
            }
        }
    });
    Ok(quote! {
        const _: () = {
            #plan_impl
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
                    #(#chain_fns)*
                    #write_impl
                }
            }
        };
        #zero_copy_asserts
    })
}
