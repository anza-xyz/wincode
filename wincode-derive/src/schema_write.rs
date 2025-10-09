use {
    crate::common::{
        get_crate_name, get_src_dst, suppress_unused_fields, Field, SchemaArgs, Variant,
    },
    darling::{
        ast::{Data, Fields, Style},
        FromDeriveInput, Result,
    },
    proc_macro2::TokenStream,
    quote::quote,
    syn::{parse_quote, DeriveInput, Type},
};

fn impl_struct(fields: &Fields<Field>) -> (TokenStream, TokenStream) {
    if fields.is_empty() {
        return (quote! {Ok(0)}, quote! {Ok(())});
    }

    let target = fields.iter().map(|field| field.target());
    let ident = Field::struct_member_ident_iter(fields);

    let writes = fields.iter().enumerate().map(|(i, field)| {
        let ident = field.struct_member_ident(i);
        let target = field.target();
        quote! { <#target as SchemaWrite>::write(writer, &src.#ident)?; }
    });

    (
        quote! {
            let mut total = 0usize;
            #(
                total = total.checked_add(<#target as SchemaWrite>::size_of(&src.#ident)?).ok_or_else(size_of_overflow)?;
            )*
            Ok(total)
        },
        quote! {
            #(#writes)*
            Ok(())
        },
    )
}

fn impl_enum(enum_ident: &Type, variants: &[Variant]) -> (TokenStream, TokenStream) {
    if variants.is_empty() {
        return (quote! {Ok(0)}, quote! {Ok(())});
    }
    let mut size_of_impl = Vec::with_capacity(variants.len());
    let mut write_impl = Vec::with_capacity(variants.len());

    for (i, variant) in variants.iter().enumerate() {
        let variant_ident = &variant.ident;
        let fields = &variant.fields;
        let discriminant = i as u32;
        // Bincode always encodes the discriminant as u32 using the index of the field order.
        let size_of_discriminant = quote! {
            u32::size_of(&#discriminant)?
        };
        let write_discriminant = quote! {
            u32::write(writer, &#discriminant)?;
        };

        let (size, write) = match fields.style {
            style @ (Style::Struct | Style::Tuple) => {
                let target = fields.iter().map(|field| field.target());
                let ident = Field::enum_member_ident_iter(fields);
                let write = fields.iter().zip(ident.clone()).map(|(field, ident)| {
                    let target = field.target();
                    quote! {
                        <#target as SchemaWrite>::write(writer, #ident)?;
                    }
                });
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

                (
                    quote! {
                        #match_case => {
                            let mut total = #size_of_discriminant;
                            #(
                                total = total.checked_add(<#target as SchemaWrite>::size_of(#ident)?).ok_or_else(size_of_overflow)?;
                            )*
                            Ok(total)
                        }
                    },
                    quote! {
                        #match_case => {
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
    )
}

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let args = SchemaArgs::from_derive_input(&input)?;
    let (impl_generics, ty_generics, where_clause) = args.generics.split_for_impl();
    let ident = &args.ident;
    let crate_name = get_crate_name(&args);
    let src_dst = get_src_dst(&args);
    let field_suppress = suppress_unused_fields(&args);

    let (size_of_impl, write_impl) = match &args.data {
        Data::Struct(fields) => impl_struct(fields),
        Data::Enum(v) => {
            let enum_ident = match &args.from {
                Some(from) => from,
                None => &parse_quote!(Self),
            };
            impl_enum(enum_ident, v)
        }
    };

    Ok(quote! {
        const _: () = {
            use #crate_name::{SchemaWrite, WriteResult, error::size_of_overflow, io::Writer};
            impl #impl_generics #crate_name::SchemaWrite for #ident #ty_generics #where_clause {
                type Src = #src_dst;

                #[inline]
                fn size_of(src: &Self::Src) -> WriteResult<usize> {
                    #size_of_impl
                }

                #[inline]
                fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
                    #write_impl
                }
            }
        };
        #field_suppress
    })
}
