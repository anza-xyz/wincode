use {
    crate::common::{
        get_crate_name, get_src_dst, suppress_unused_fields, Field, SchemaArgs, Variant,
    },
    darling::{
        ast::{Data, Fields, Style},
        Error, FromDeriveInput, Result,
    },
    proc_macro2::TokenStream,
    quote::{format_ident, quote},
    syn::{parse_quote, DeriveInput, GenericParam, Generics, Ident, Type},
};

/// Ensure target reference types are tied to the `'de` lifetime.
///
/// This ensures that rather than generating:
/// ```ignore
/// <&'a str as SchemaRead>::read(reader, dst)
/// ```
///
/// We generate:
/// ```ignore
/// <&'de str as SchemaRead>::read(reader, dst)
/// ```
///
/// We ensure that `'de` extends to all type parameters via [`append_de_lifetime`].
fn override_ref_lifetime(target: &Type) -> Type {
    let mut target = target.clone();
    if let Type::Reference(reference) = &mut target {
        if let Some(lifetime) = &mut reference.lifetime {
            lifetime.ident = Ident::new("de", lifetime.span());
        }
    }
    target
}

fn impl_struct(fields: &Fields<Field>) -> TokenStream {
    if fields.is_empty() {
        return quote! {};
    }

    let read_impl = fields.iter().enumerate().map(|(i, field)| {
        let ident = field.struct_member_ident(i);
        let target = override_ref_lifetime(field.target());
        // Generate code to drop already initialized fields in reverse order.
        let drop = fields.fields[..i]
            .iter()
            .rev()
            .enumerate()
            .map(|(j, field)| {
                let ident = field.struct_member_ident(i - 1 - j);
                quote! {
                    unsafe { ptr::drop_in_place(&mut (*dst_ptr).#ident); }
                }
            });
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
            let ty = &field.ty;
            quote! { MaybeUninit<#ty> }
        } else {
            quote! { MaybeUninit<_> }
        };
        quote! {
            // Clippy will warn about using `?` on the first `read` because it doesn't have any fields to drop,
            // and its block will just contain `return Err(e)`.
            #[allow(clippy::question_mark)]
            if let Err(e) = <#target as SchemaRead<'de>>::read(
                reader,
                unsafe { &mut *(&raw mut (*dst_ptr).#ident).cast::<#hint>() }
            ) {
                #(#drop)*
                return Err(e);
            }
        }
    });

    quote! {
        let dst_ptr = dst.as_mut_ptr();
        #(#read_impl)*
    }
}

/// Include placement initialization helpers for structs.
///
/// This adds some convenience methods to structs that can avoid a lot of boilerplate when
/// implementing custom `SchemaRead` implementations. In particular, provide methods that
/// deal with projecting subfields of structs into `MaybeUninit`s. Without this,
/// users have to write a litany of `&mut *(&raw mut (*dst_ptr).field).cast()` to
/// access MaybeUninit struct fields.
///
/// For example:
/// ```ignore
/// #[derive(SchemaRead)]
/// struct Header {
///     num_required_signatures: u8,
///     num_signed_accounts: u8,
///     num_unsigned_accounts: u8,
/// }
///
/// #[derive(SchemaRead)]
/// struct Body {
///     header: Header,
/// }
///
/// struct Message {
///     body: Body,
/// }
///
/// impl SchemaRead<'_> for Message {
///     type Dst = Message;
///
///     fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
///         // Some more complicated logic not capturable by the macro...
///         let mut body = MaybeUninit::<Body>::uninit();
///         // Project a mutable MaybeUninit<Header> from the MaybeUninit<Body>.
///         let header = Body::get_uninit_header_mut(&mut body);
///         // ...
///     }
/// }
/// ```
///
/// We cannot do this for enums, given the lack of facilities for placement initialization.
fn impl_struct_extensions(args: &SchemaArgs) -> Result<TokenStream> {
    if !args.struct_extensions {
        return Ok(quote! {});
    }

    let Data::Struct(fields) = &args.data else {
        return Err(Error::custom(
            "`struct_extensions` is only supported for structs",
        ));
    };

    if fields.is_empty() {
        return Ok(quote! {});
    }

    let struct_ident = &args.ident;
    let vis = &args.vis;
    let dst = get_src_dst(args);
    let impl_generics = append_de_lifetime(&args.generics);
    let (_, ty_generics, where_clause) = args.generics.split_for_impl();

    let helpers = fields.iter().enumerate().map(|(i, field)| {
        let ty = override_ref_lifetime(&field.ty);
        let target = override_ref_lifetime(field.target());
        let ident = field.struct_member_ident(i);
        let ident_string = field.struct_member_ident_to_string(i);
        let get_uninit_mut_ident = format_ident!("get_uninit_{}_mut", ident_string);
        let read_field_ident = format_ident!("read_{}", ident_string);
        let write_uninit_field_ident = format_ident!("write_uninit_{}", ident_string);
        let field_projection_type = if args.from.is_some() {
            // If the user is defining a mapping type, we need the type system to resolve the 
            // projection destination.
            quote! { <#ty as SchemaRead<'de>>::Dst }
        } else {
            // Otherwise we can use the type directly.
            // This makes the generated type more scrutable.
            quote! { #ty }
        };
        quote! {
            #[inline(always)]
            #vis fn #get_uninit_mut_ident(dst: &mut MaybeUninit<#dst>) -> &mut MaybeUninit<#field_projection_type> {
                unsafe { &mut *(&raw mut (*dst.as_mut_ptr()).#ident).cast() }
            }

            #[inline(always)]
            #vis fn #read_field_ident(reader: &mut Reader<'de>, dst: &mut MaybeUninit<#dst>) -> Result<()> {
                <#target as SchemaRead<'de>>::read(reader, Self::#get_uninit_mut_ident(dst))
            }

            #[inline(always)]
            #vis fn #write_uninit_field_ident(val: #field_projection_type, dst: &mut MaybeUninit<#dst>) {
                Self::#get_uninit_mut_ident(dst).write(val);
            }
        }
    });

    Ok(quote!(
        impl #impl_generics #struct_ident #ty_generics #where_clause {
            #(#helpers)*
        }
    ))
}

fn impl_enum(enum_ident: &Type, variants: &[Variant]) -> TokenStream {
    if variants.is_empty() {
        return quote! {Ok(())};
    }

    let read_impl = variants.iter().enumerate().map(|(i, variant)| {
        let variant_ident = &variant.ident;
        let fields = &variant.fields;
        let discriminant = i as u32;

        match fields.style {
            style @ (Style::Struct | Style::Tuple) => {
                let idents = Field::enum_member_ident_iter(fields);
                let read = fields.iter().zip(idents.clone()).map(|(field, ident)| {
                    let target = override_ref_lifetime(field.target());

                    // Unfortunately we can't avoid temporaries for arbitrary enums, as Rust does not provide
                    // facilities for placement initialization on enums.
                    //
                    // In the future, we may be able to support an attribute that allows users to opt into
                    // a macro-generated shadowed enum that wraps all variant fields with `MaybeUninit`, which
                    // could be used to facilitate direct reads. The user would have to guarantee layout on
                    // their type (a la `#[repr(C)]`), or roll the dice on non-guaranteed layout -- so it would need to be opt-in.
                    quote! {
                        let mut #ident = MaybeUninit::uninit();
                        <#target as SchemaRead<'de>>::read(reader, &mut #ident)?;
                        let #ident = unsafe { #ident.assume_init() };
                    }
                });

                let constructor = if style.is_struct() {
                    quote! {
                        #enum_ident::#variant_ident{#(#idents),*}
                    }
                } else {
                    quote! {
                        #enum_ident::#variant_ident(#(#idents),*)
                    }
                };

                quote! {
                    #discriminant => {
                        #(#read)*
                        dst.write(#constructor);
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

    quote! {
        let discriminant = u32::get(reader)?;
        match discriminant {
            #(#read_impl)*
            _ => return Err(error::invalid_tag_encoding(discriminant as usize)),
        }
    }
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
/// We must ensure `'a` lives at least as long as the underlying source buffer bytes (`'de`).
fn append_de_lifetime(generics: &Generics) -> Generics {
    let mut generics = generics.clone();
    if generics.lifetimes().next().is_none() {
        generics
            .params
            .push(GenericParam::Lifetime(parse_quote!('de)));
        return generics;
    }

    let lifetimes = generics.lifetimes();
    // Extend `'de` to all lifetimes in the generics.
    generics
        .params
        .push(GenericParam::Lifetime(parse_quote!('de: #(#lifetimes)+*)));
    generics
}

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let args = SchemaArgs::from_derive_input(&input)?;
    let appended_generics = append_de_lifetime(&args.generics);
    let (impl_generics, _, _) = appended_generics.split_for_impl();
    let (_, ty_generics, where_clause) = args.generics.split_for_impl();
    let ident = &args.ident;
    let crate_name = get_crate_name(&args);
    let src_dst = get_src_dst(&args);
    let field_suppress = suppress_unused_fields(&args);
    let struct_extensions = impl_struct_extensions(&args)?;

    let read_impl = match &args.data {
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
            use core::{ptr, mem::MaybeUninit};
            use #crate_name::{SchemaRead, Result, io::Reader, error};
            impl #impl_generics #crate_name::SchemaRead<'de> for #ident #ty_generics #where_clause {
                type Dst = #src_dst;

                #[inline]
                fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                    #read_impl
                    Ok(())
                }
            }
            #struct_extensions
        };
        #field_suppress
    })
}
