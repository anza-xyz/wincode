use {
    crate::common::{
        default_tag_encoding, extract_repr, get_crate_name, get_src_dst, suppress_unused_fields,
        Field, FieldsExt, SchemaArgs, StructRepr, TraitImpl, Variant,
    },
    darling::{
        ast::{Data, Fields, Style},
        Error, FromDeriveInput, Result,
    },
    proc_macro2::TokenStream,
    quote::quote,
    syn::{parse_quote, DeriveInput, Type},
};

fn impl_struct(
    fields: &Fields<Field>,
    repr: &StructRepr,
) -> (TokenStream, TokenStream, TokenStream) {
    if fields.is_empty() {
        return (quote! {Ok(0)}, quote! {Ok(())}, quote! {None});
    }

    let target = fields.iter().map(|field| field.target_resolved());
    let ident = fields.struct_member_ident_iter();

    let writes = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let ident = field.struct_member_ident(i);
            let target = field.target_resolved();
            quote! { <#target as SchemaWrite>::write(writer, &src.#ident)?; }
        })
        .collect::<Vec<_>>();

    let type_meta_impl = fields.type_meta_impl(TraitImpl::SchemaWrite, repr);

    (
        quote! {
            if let TypeMeta::Static { size, .. } = <Self as SchemaWrite>::TYPE_META {
                return Ok(size);
            }
            let mut total = 0usize;
            #(
                total += <#target as SchemaWrite>::size_of(&src.#ident)?;
            )*
            Ok(total)
        },
        quote! {
            match <Self as SchemaWrite>::TYPE_META {
                TypeMeta::Static { size, .. } => {
                    // SAFETY: `size` is the serialized size of the struct, which is the sum
                    // of the serialized sizes of the fields.
                    // Calling `write` on each field will write exactly `size` bytes,
                    // fully initializing the trusted window.
                    let writer = &mut unsafe { writer.as_trusted_for(size) }?;
                    #(#writes)*
                    writer.finish()?;
                }
                _ => {
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
    tag_encoding: Option<&Type>,
) -> (TokenStream, TokenStream, TokenStream) {
    if variants.is_empty() {
        return (quote! {Ok(0)}, quote! {Ok(())}, quote! {TypeMeta::Dynamic});
    }
    let default_tag_encoding = default_tag_encoding();
    let tag_encoding = tag_encoding.unwrap_or(&default_tag_encoding);
    let mut size_of_impl = Vec::with_capacity(variants.len());
    let mut write_impl = Vec::with_capacity(variants.len());
    // Note that all enums except unit enums are never static.
    let mut type_meta_impl = quote!(TypeMeta::Dynamic);
    if variants.iter().all(|variant| variant.fields.is_unit()) {
        // If all variants are unit, we know up front that the static size is the size of the discriminant.
        type_meta_impl = quote! {
            const {
                match <#tag_encoding as SchemaWrite>::TYPE_META {
                    // Unit enums are never zero-copy, as they have invalid bit patterns.
                    TypeMeta::Static { size, .. } => TypeMeta::Static { size, zero_copy: false },
                    TypeMeta::Dynamic => TypeMeta::Dynamic,
                }
            }
        };
    }

    for (i, variant) in variants.iter().enumerate() {
        let variant_ident = &variant.ident;
        let fields = &variant.fields;
        let discriminant = variant.discriminant(i);
        // Bincode always encodes the discriminant using the index of the field order.
        let size_of_discriminant = quote! {
            #tag_encoding::size_of(&#discriminant)?
        };
        let write_discriminant = quote! {
            #tag_encoding::write(writer, &#discriminant)?;
        };

        let (size, write) = match fields.style {
            style @ (Style::Struct | Style::Tuple) => {
                let target = fields.iter().map(|field| field.target_resolved());
                let ident = fields.enum_member_ident_iter(None);
                let write = fields
                    .iter()
                    .zip(ident.clone())
                    .map(|(field, ident)| {
                        let target = field.target_resolved();
                        quote! {
                            <#target as SchemaWrite>::write(writer, #ident)?;
                        }
                    })
                    .collect::<Vec<_>>();
                let ident_destructure = ident.clone();
                let match_case = if style.is_struct() {
                    quote! {
                        #enum_ident::#variant_ident{#(#ident_destructure),*}
                    }
                } else {
                    quote! {
                        #enum_ident::#variant_ident(#(#ident_destructure),*)
                    }
                };

                // Prefix disambiguation needed, as our match statement will destructure enum variant identifiers.
                let static_anon_idents = fields
                    .member_anon_ident_iter(Some("__"))
                    .collect::<Vec<_>>();
                let static_targets = fields
                    .iter()
                    .map(|field| {
                        let target = field.target_resolved();
                        quote! {<#target as SchemaWrite>::TYPE_META}
                    })
                    .collect::<Vec<_>>();

                (
                    quote! {
                        #match_case => {
                            if let (TypeMeta::Static { size: disc_size, .. } #(,TypeMeta::Static { size: #static_anon_idents, .. })*) = (<#tag_encoding as SchemaWrite>::TYPE_META #(,#static_targets)*) {
                                return Ok(disc_size + #(#static_anon_idents)+*);
                            }

                            let mut total = #size_of_discriminant;
                            #(
                                total += <#target as SchemaWrite>::size_of(#ident)?;
                            )*
                            Ok(total)
                        }
                    },
                    quote! {
                        #match_case => {
                            if let (TypeMeta::Static { size: disc_size, .. } #(,TypeMeta::Static { size: #static_anon_idents, .. })*) = (<#tag_encoding as SchemaWrite>::TYPE_META #(,#static_targets)*) {
                                let summed_sizes = disc_size + #(#static_anon_idents)+*;
                                // SAFETY: `summed_sizes` is the sum of the static sizes of the fields + the discriminant size,
                                // which is the serialized size of the variant.
                                // Writing the discriminant and then calling `write` on each field will write
                                // exactly `summed_sizes` bytes, fully initializing the trusted window.
                                let writer = &mut unsafe { writer.as_trusted_for(summed_sizes) }?;
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

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let repr = extract_repr(&input, TraitImpl::SchemaWrite)?;
    let args = SchemaArgs::from_derive_input(&input)?;
    let (impl_generics, ty_generics, where_clause) = args.generics.split_for_impl();
    let ident = &args.ident;
    let crate_name = get_crate_name(&args);
    let src_dst = get_src_dst(&args);
    let field_suppress = suppress_unused_fields(&args);

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
            use #crate_name::{SchemaWrite, WriteResult, io::Writer, TypeMeta};
            impl #impl_generics #crate_name::SchemaWrite for #ident #ty_generics #where_clause {
                type Src = #src_dst;

                #[allow(clippy::arithmetic_side_effects)]
                const TYPE_META: TypeMeta = #type_meta_impl;

                #[inline]
                fn size_of(src: &Self::Src) -> WriteResult<usize> {
                    #size_of_impl
                }

                #[inline]
                fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                    #write_impl
                }
            }
        };
        #field_suppress
    })
}
