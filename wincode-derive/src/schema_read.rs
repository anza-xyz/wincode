use {
    crate::{
        assert_zero_copy::assert_zero_copy,
        common::{
            default_tag_encoding, extract_repr, get_crate_name, get_src_dst,
            get_src_dst_fully_qualified, suppress_unused_fields, Field, FieldsExt, SchemaArgs,
            StructRepr, TraitImpl, TypeExt, Variant, VariantsExt,
        },
    },
    darling::{
        ast::{Data, Fields, Style},
        Error, FromDeriveInput, Result,
    },
    proc_macro2::{Span, TokenStream},
    quote::{format_ident, quote},
    syn::{
        parse_quote, punctuated::Punctuated, DeriveInput, GenericParam, Generics, LitInt, Path,
        PredicateType, Token, Type, WhereClause, WherePredicate,
    },
};

fn impl_struct(
    args: &SchemaArgs,
    fields: &Fields<Field>,
    repr: &StructRepr,
) -> (TokenStream, TokenStream) {
    if fields.is_empty() {
        return (quote! {}, quote! {TypeMeta::Dynamic});
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
                quote! { MaybeUninit<#ty> }
            } else {
                quote! { MaybeUninit<_> }
            };
            let init_count = if i == num_fields - 1 {
                quote! {}
            } else {
                quote! { *init_count += 1; }
            };
            quote! {
                <#target as SchemaRead<'de, WincodeConfig>>::read(
                    reader,
                    unsafe { &mut *(&raw mut (*dst_ptr).#ident).cast::<#hint>() }
                )?;
                #init_count
            }
        })
        .collect::<Vec<_>>();

    let type_meta_impl = fields.type_meta_impl(TraitImpl::SchemaRead, repr);

    let drop_guard = (0..fields.len()).map(|i| {
        // Generate code to drop already initialized fields in reverse order.
        let drop = fields.fields[..i]
            .iter()
            .rev()
            .enumerate()
            .map(|(j, field)| {
                let ident = field.struct_member_ident(i - 1 - j);
                quote! {
                    ptr::drop_in_place(&raw mut (*dst_ptr).#ident);
                }
            });
        let cnt = i as u8;
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

    let dst = get_src_dst_fully_qualified(args);
    let (impl_generics, ty_generics, where_clause) = args.generics.split_for_impl();
    let init_guard = quote! {
        let dst_ptr = dst.as_mut_ptr();
        let mut guard = DropGuard {
            init_count: 0,
            dst_ptr,
        };
        let init_count = &mut guard.init_count;
    };
    (
        quote! {
            struct DropGuard #impl_generics #where_clause {
                init_count: u8,
                dst_ptr: *mut #dst,
            }

            impl #impl_generics ::core::ops::Drop for DropGuard #ty_generics #where_clause {
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

            match <Self as SchemaRead<'de, WincodeConfig>>::TYPE_META {
                TypeMeta::Static { size, .. } => {
                    // SAFETY: `size` is the serialized size of the struct, which is the sum
                    // of the serialized sizes of the fields.
                    // Calling `read` on each field will consume exactly `size` bytes,
                    // fully consuming the trusted window.
                    let reader = &mut unsafe { reader.as_trusted_for(size) }?;
                    #init_guard
                    #(#read_impl)*
                    mem::forget(guard);
                }
                TypeMeta::Dynamic => {
                    #init_guard
                    #(#read_impl)*
                    mem::forget(guard);
                }
            }
        },
        quote! {
            #type_meta_impl
        },
    )
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
/// unsafe impl<'de> SchemaRead<'de> for Message {
///     type Dst = Message;
///
///     fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
fn impl_struct_extensions(args: &SchemaArgs, crate_name: &Path) -> Result<TokenStream> {
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
    let builder_ident = format_ident!("{struct_ident}UninitBuilder");

    // We modify the generics to add a lifetime parameter for the inner `MaybeUninit` struct.
    let mut builder_generics = args.generics.clone();
    // Add the lifetime for the inner `&mut MaybeUninit` struct.
    builder_generics
        .params
        .push(GenericParam::Lifetime(parse_quote!('_wincode_inner)));
    builder_generics.params.push(GenericParam::Type(
        parse_quote!(WincodeConfig: #crate_name::config::Config),
    ));

    let builder_dst = get_src_dst_fully_qualified(args);

    let (builder_impl_generics, builder_ty_generics, builder_where_clause) =
        builder_generics.split_for_impl();
    // Determine how many bits are needed to track the initialization state of the fields.
    let (builder_bit_set_ty, builder_bit_set_bits): (Type, u32) = match fields.len() {
        len if len <= 8 => (parse_quote!(u8), u8::BITS),
        len if len <= 16 => (parse_quote!(u16), u16::BITS),
        len if len <= 32 => (parse_quote!(u32), u32::BITS),
        len if len <= 64 => (parse_quote!(u64), u64::BITS),
        len if len <= 128 => (parse_quote!(u128), u128::BITS),
        _ => {
            return Err(Error::custom(
                "`struct_extensions` is only supported for structs with up to 128 fields",
            ))
        }
    };
    let builder_struct_decl = {
        // `split_for_impl` will strip default type and const parameters, so we collect them manually
        // to preserve the declarations on the original struct.
        let generic_type_params = builder_generics.type_params();
        let generic_lifetimes = builder_generics.lifetimes();
        let generic_const = builder_generics.const_params();
        let where_clause = builder_generics.where_clause.as_ref();
        quote! {
            /// A helper struct that provides convenience methods for reading and writing to a `MaybeUninit` struct
            /// with a bit-set tracking the initialization state of the fields.
            ///
            /// The builder will drop all initialized fields in reverse order on drop. When the struct is fully initialized,
            /// you **must** call `finish` or `into_assume_init_mut` to forget the builder. Otherwise, all the
            /// initialized fields will be dropped when the builder is dropped.
            #[must_use]
            #vis struct #builder_ident < #(#generic_lifetimes,)* #(#generic_const,)* #(#generic_type_params,)* > #where_clause {
                inner: &'_wincode_inner mut core::mem::MaybeUninit<#builder_dst>,
                init_set: #builder_bit_set_ty,
                _config: core::marker::PhantomData<WincodeConfig>,
            }
        }
    };

    let builder_drop_impl = {
        // Drop all initialized fields in reverse order.
        let drops = fields.iter().rev().enumerate().map(|(index, field)| {
            // Compute the actual index relative to the reversed iterator.
            let real_index = fields.len() - 1 - index;
            let field_ident = field.struct_member_ident(real_index);
            // The corresponding bit for the field.
            let bit_set_index = LitInt::new(&(1u128 << real_index).to_string(), Span::call_site());
            quote! {
                if self.init_set & #bit_set_index != 0 {
                    // SAFETY: We are dropping an initialized field.
                    unsafe {
                        ptr::drop_in_place(&raw mut (*dst_ptr).#field_ident);
                    }
                }
            }
        });
        quote! {
            impl #builder_impl_generics ::core::ops::Drop for #builder_ident #builder_ty_generics #builder_where_clause {
                fn drop(&mut self) {
                    let dst_ptr = self.inner.as_mut_ptr();
                    #(#drops)*
                }
            }
        }
    };

    let builder_impl = {
        let is_fully_init_mask = if fields.len() as u32 == builder_bit_set_bits {
            quote!(#builder_bit_set_ty::MAX)
        } else {
            let field_bits = LitInt::new(&fields.len().to_string(), Span::call_site());
            quote!(((1 as #builder_bit_set_ty) << #field_bits) - 1)
        };

        quote! {
            impl #builder_impl_generics #builder_ident #builder_ty_generics #builder_where_clause {
                #vis const fn from_maybe_uninit_mut(inner: &'_wincode_inner mut MaybeUninit<#builder_dst>) -> Self {
                    Self {
                        inner,
                        init_set: 0,
                        _config: core::marker::PhantomData,
                    }
                }

                /// Check if the builder is fully initialized.
                ///
                /// This will check if all field initialization bits are set.
                #[inline]
                #vis const fn is_init(&self) -> bool {
                    self.init_set == #is_fully_init_mask
                }

                /// Assume the builder is fully initialized, and return a mutable reference to the inner `MaybeUninit` struct.
                ///
                /// The builder will be forgotten, so the drop logic will not longer run.
                ///
                /// # Safety
                ///
                /// Calling this when the content is not yet fully initialized causes undefined behavior: it is up to the caller
                /// to guarantee that the `MaybeUninit<T>` really is in an initialized state.
                #[inline]
                #vis unsafe fn into_assume_init_mut(mut self) -> &'_wincode_inner mut #builder_dst {
                    let mut this = ManuallyDrop::new(self);
                    // SAFETY: reference lives beyond the scope of the builder, and builder is forgotten.
                    let inner = unsafe { ptr::read(&mut this.inner) };
                    // SAFETY: Caller asserts the `MaybeUninit<T>` is in an initialized state.
                    unsafe {
                        inner.assume_init_mut()
                    }
                }

                /// Forget the builder, disabling the drop logic.
                #[inline]
                #vis const fn finish(self) {
                    mem::forget(self);
                }
            }
        }
    };

    // Generate the helper methods for the builder.
    let builder_helpers = fields.iter().enumerate().map(|(i, field)| {
        let ty = &field.ty;
        let target_reader_bound = field.target_resolved().with_lifetime("de");
        let ident = field.struct_member_ident(i);
        let ident_string = field.struct_member_ident_to_string(i);
        let uninit_mut_ident = format_ident!("uninit_{ident_string}_mut");
        let read_field_ident = format_ident!("read_{ident_string}");
        let write_uninit_field_ident = format_ident!("write_{ident_string}");
        let assume_init_field_ident = format_ident!("assume_init_{ident_string}");
        let init_with_field_ident = format_ident!("init_{ident_string}_with");
        let lifetimes = ty.lifetimes();
        // We must always extract the `Dst` from the type because `SchemaRead` implementations need
        // not necessarily write to `Self` -- they write to `Self::Dst`, which isn't necessarily `Self`
        // (e.g., in the case of container types).
        let field_projection_type = if lifetimes.is_empty() {
            quote!(<#ty as SchemaRead<'_, WincodeConfig>>::Dst)
        } else {
            let lt = lifetimes[0];
            // Even though a type may have multiple distinct lifetimes, we force them to be uniform
            // for a `SchemaRead` cast because an implementation of `SchemaRead` must bind all lifetimes
            // to the lifetime of the reader (and will not be implemented over multiple distinct lifetimes).
            let ty = ty.with_lifetime(&lt.ident.to_string());
            quote!(<#ty as SchemaRead<#lt, WincodeConfig>>::Dst)
        };

        // The bit index for the field.
        let index_bit = LitInt::new(&(1u128 << i).to_string(), Span::call_site());
        let set_index_bit = quote! {
            self.init_set |= #index_bit;
        };

        quote! {
            /// Get a mutable reference to the maybe uninitialized field.
            #[inline]
            #vis const fn #uninit_mut_ident(&mut self) -> &mut MaybeUninit<#field_projection_type> {
                // SAFETY:
                // - `self.inner` is a valid reference to a `MaybeUninit<#builder_dst>`.
                // - We return the field as `&mut MaybeUninit<#target>`, so
                //   the field is never exposed as initialized.
                unsafe { &mut *(&raw mut (*self.inner.as_mut_ptr()).#ident).cast() }
            }

            /// Write a value to the maybe uninitialized field.
            // This method can be marked `const` in the future when MSRV is >= 1.85.
            #[inline]
            #vis fn #write_uninit_field_ident(&mut self, val: #field_projection_type) -> &mut Self {
                self.#uninit_mut_ident().write(val);
                #set_index_bit
                self
            }

            /// Read a value from the reader into the maybe uninitialized field.
            #[inline]
            #vis fn #read_field_ident <'de>(&mut self, reader: &mut impl Reader<'de>) -> ReadResult<&mut Self> {
                // SAFETY:
                // - `self.inner` is a valid reference to a `MaybeUninit<#builder_dst>`.
                // - We return the field as `&mut MaybeUninit<#target>`, so
                //   the field is never exposed as initialized.
                let proj = unsafe { &mut *(&raw mut (*self.inner.as_mut_ptr()).#ident).cast() };
                <#target_reader_bound as SchemaRead<'de, WincodeConfig>>::read(reader, proj)?;
                #set_index_bit
                Ok(self)
            }

            /// Initialize the field with a given initializer function.
            ///
            /// # Safety
            ///
            /// The caller must guarantee that the initializer function fully initializes the field.
            #[inline]
            #vis unsafe fn #init_with_field_ident(&mut self, mut initializer: impl FnMut(&mut MaybeUninit<#field_projection_type>) -> ReadResult<()>) -> ReadResult<&mut Self> {
                initializer(self.#uninit_mut_ident())?;
                #set_index_bit
                Ok(self)
            }

            /// Mark the field as initialized.
            ///
            /// # Safety
            ///
            /// Caller must guarantee the field has been fully initialized prior to calling this.
            #[inline]
            #vis const unsafe fn #assume_init_field_ident(&mut self) -> &mut Self {
                #set_index_bit
                self
            }
        }
    });

    Ok(quote! {
        const _: () = {
            use {
                core::{mem::{MaybeUninit, ManuallyDrop, self}, ptr, marker::PhantomData},
                #crate_name::{SchemaRead, ReadResult, TypeMeta, io::Reader, error, config::Config},
            };

            #builder_drop_impl
            #builder_impl

            impl #builder_impl_generics #builder_ident #builder_ty_generics #builder_where_clause {
                #(#builder_helpers)*
            }
        };
        #builder_struct_decl
    })
}

fn impl_enum(
    enum_ident: &Type,
    variants: &[Variant],
    tag_encoding_override: Option<&Type>,
) -> (TokenStream, TokenStream) {
    if variants.is_empty() {
        return (quote! {Ok(())}, quote! {TypeMeta::Dynamic});
    }

    let type_meta_impl = variants.type_meta_impl(
        TraitImpl::SchemaRead,
        tag_encoding_override.unwrap_or(&default_tag_encoding()),
    );

    let read_impl = variants.iter().enumerate().map(|(i, variant)| {
        let variant_ident = &variant.ident;
        let fields = &variant.fields;
        let discriminant = variant.discriminant(i);

        match fields.style {
            style @ (Style::Struct | Style::Tuple) => {
                // No prefix disambiguation needed, as we are matching on a discriminant integer.
                let idents = fields.enum_member_ident_iter(None).collect::<Vec<_>>();
                let read = fields
                    .iter()
                    .zip(&idents)
                    .map(|(field, ident)| {
                        let target = field.target_resolved().with_lifetime("de");

                        // Unfortunately we can't avoid temporaries for arbitrary enums, as Rust does not provide
                        // facilities for placement initialization on enums.
                        //
                        // In the future, we may be able to support an attribute that allows users to opt into
                        // a macro-generated shadowed enum that wraps all variant fields with `MaybeUninit`, which
                        // could be used to facilitate direct reads. The user would have to guarantee layout on
                        // their type (a la `#[repr(C)]`), or roll the dice on non-guaranteed layout -- so it would need to be opt-in.
                        quote! {
                            let #ident = <#target as SchemaRead<'de, WincodeConfig>>::get(reader)?;
                        }
                    })
                    .collect::<Vec<_>>();

                // No prefix disambiguation needed, as we are matching on a discriminant integer.
                let static_anon_idents = fields.member_anon_ident_iter(None).collect::<Vec<_>>();
                let static_targets = fields.iter().map(|field| {
                    let target = field.target_resolved().with_lifetime("de");
                    quote! {<#target as SchemaRead<'de, WincodeConfig>>::TYPE_META}
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
                        if let (#(TypeMeta::Static { size: #static_anon_idents, .. }),*) = (#(#static_targets),*) {
                            let summed_sizes = #(#static_anon_idents)+*;
                            // SAFETY: `summed_sizes` is the sum of the static sizes of the fields,
                            // which is the serialized size of the variant.
                            // Calling `read` on each field will consume exactly `summed_sizes` bytes,
                            // fully consuming the trusted window.
                            let reader = &mut unsafe { reader.as_trusted_for(summed_sizes) }?;
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
            <#tag_encoding as SchemaRead<'de, WincodeConfig>>::get(reader)?;
        }
    } else {
        quote! {
            WincodeConfig::TagEncoding::try_into_u32(WincodeConfig::TagEncoding::get(reader)?)?
        }
    };

    (
        quote! {
            let discriminant = #read_discriminant;
            match discriminant {
                #(#read_impl)*
                _ => return Err(error::invalid_tag_encoding(discriminant as usize)),
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
        bounds.push(parse_quote!(SchemaRead<'de, WincodeConfig, Dst = #ident>));

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
    append_de_lifetime(&mut generics);
    append_where_clause(&mut generics);
    append_config(&mut generics);
    generics
}

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let repr = extract_repr(&input, TraitImpl::SchemaRead)?;
    let args = SchemaArgs::from_derive_input(&input)?;
    let appended_generics = append_generics(&args.generics);
    let (impl_generics, _, where_clause) = appended_generics.split_for_impl();
    let (_, ty_generics, _) = args.generics.split_for_impl();
    let ident = &args.ident;
    let crate_name = get_crate_name(&args);
    let src_dst = get_src_dst(&args);
    let field_suppress = suppress_unused_fields(&args);
    let struct_extensions = impl_struct_extensions(&args, &crate_name)?;
    let zero_copy_asserts = assert_zero_copy(&args, &repr)?;

    let (read_impl, type_meta_impl) = match &args.data {
        Data::Struct(fields) => {
            if args.tag_encoding.is_some() {
                return Err(Error::custom("`tag_encoding` is only supported for enums"));
            }
            // Only structs are eligible being marked zero-copy, so only the struct
            // impl needs the repr.
            impl_struct(&args, fields, &repr)
        }
        Data::Enum(v) => {
            let enum_ident = match &args.from {
                Some(from) => from,
                None => &parse_quote!(Self),
            };
            impl_enum(enum_ident, v, args.tag_encoding.as_ref())
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
            bounds.push(parse_quote!(IsTrue));
            let no_pad_predicate = WherePredicate::Type(PredicateType {
                // Workaround for https://github.com/rust-lang/rust/issues/48214.
                lifetimes: Some(parse_quote!(for<'_wincode_internal>)),
                // Types are only zero-copy if they do not have any padding.
                bounded_ty: parse_quote!(
                    Assert<
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
            bounds.push(parse_quote!(ZeroCopy<WincodeConfig>));
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
            append_config(&mut generics);
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
                struct Assert<const B: bool>;
                trait IsTrue {}
                impl IsTrue for Assert<true> {}
                unsafe impl #impl_generics ZeroCopy<WincodeConfig> for #ident #ty_generics #where_clause {}
            }
        }
        _ => quote!(),
    };

    Ok(quote! {
        const _: () = {
            use core::{ptr, mem::{self, MaybeUninit}};
            use #crate_name::{SchemaRead, ReadResult, tag_encoding::TagEncoding, TypeMeta, io::Reader, error, config::{Config, DefaultConfig, ZeroCopy}};

            #zero_copy_impl

            unsafe impl #impl_generics SchemaRead<'de, WincodeConfig> for #ident #ty_generics #where_clause {
                type Dst = #src_dst;

                #[allow(clippy::arithmetic_side_effects)]
                const TYPE_META: TypeMeta = #type_meta_impl;

                #[inline]
                fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
