use {
    crate::common::{get_crate_name, get_src_dst_fully_qualified, SchemaArgs, TypeExt},
    darling::{ast::Data, Error, FromDeriveInput, Result},
    proc_macro2::{Span, TokenStream},
    quote::{format_ident, quote},
    syn::{parse_quote, DeriveInput, GenericParam, LitInt, Path, Type},
};

pub(crate) fn impl_uninit_builder(args: &SchemaArgs, crate_name: &Path) -> Result<TokenStream> {
    let Data::Struct(fields) = &args.data else {
        return Err(Error::custom(
            "`UninitBuilder` is only supported for structs",
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
                "`UninitBuilder` is only supported for structs with up to 128 fields",
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
            #vis fn #read_field_ident <'de>(&mut self, reader: impl Reader<'de>) -> ReadResult<&mut Self> {
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

pub(crate) fn generate(input: DeriveInput) -> Result<TokenStream> {
    let args = SchemaArgs::from_derive_input(&input)?;
    let crate_name = get_crate_name(&args);
    let uninit_builder = impl_uninit_builder(&args, &crate_name)?;

    Ok(quote! {
        #uninit_builder
    })
}
