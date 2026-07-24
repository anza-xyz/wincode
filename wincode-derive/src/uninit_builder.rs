use {
    crate::common::{SchemaArgs, extract_repr, get_crate_name},
    darling::{Error, FromDeriveInput, Result, ast::Data},
    proc_macro2::{Span, TokenStream},
    quote::{format_ident, quote},
    syn::{DeriveInput, GenericParam, LitInt, Path, Type, parse_quote},
};

pub(crate) fn impl_uninit_builder(args: &SchemaArgs, crate_name: &Path) -> Result<TokenStream> {
    let Data::Struct(fields) = &args.data else {
        return Err(Error::custom(
            "`UninitBuilder` is only supported for structs",
        ));
    };

    if args.context.is_some() {
        return Err(Error::custom(
            "`UninitBuilder` is not supported with context",
        ));
    }

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
        parse_quote!(__WincodeConfig: #crate_name::config::Config),
    ));

    let builder_dst = {
        let (_, ty_generics, _) = args.generics.split_for_impl();
        quote!(#struct_ident #ty_generics)
    };
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
            ));
        }
    };
    let builder_struct_decl = {
        quote! {
            /// A helper for initializing fields of a value stored in `MaybeUninit`.
            ///
            /// The builder tracks which fields have been marked initialized and drops
            /// those fields in reverse declaration order when the builder is dropped.
            ///
            /// Initialization helpers overwrite fields using `MaybeUninit` semantics.
            /// Reinitializing a field does not drop its previous value and may therefore
            /// leak resources or skip other destructor side effects.
            ///
            /// After fully initializing the value, call `finish` or
            /// `into_assume_init_mut` to disable the builder's drop logic.
            #[must_use]
            #vis struct #builder_ident #builder_impl_generics #builder_where_clause {
                inner: &'_wincode_inner mut core::mem::MaybeUninit<#builder_dst>,
                init_set: #builder_bit_set_ty,
                _config: core::marker::PhantomData<__WincodeConfig>,
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
                        ::core::ptr::drop_in_place(&raw mut (*dst_ptr).#field_ident);
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
                /// Creates a builder for the supplied storage.
                ///
                /// Every field initially starts marked as uninitialized. This method does not
                /// inspect the storage or detect values that may already be present. Such
                /// values are not initially tracked and may be leaked if overwritten.
                #vis const fn from_maybe_uninit_mut(inner: &'_wincode_inner mut ::core::mem::MaybeUninit<#builder_dst>) -> Self {
                    Self {
                        inner,
                        init_set: 0,
                        _config: core::marker::PhantomData,
                    }
                }

                /// Returns whether every field is marked initialized.
                ///
                /// This only examines the builder's initialization markers; it does not
                /// inspect or validate the underlying storage. Its result is only reliable
                /// when the unsafe initialization methods have been used correctly.
                #[inline]
                #vis const fn is_init(&self) -> bool {
                    self.init_set == #is_fully_init_mask
                }

                /// Returns a mutable reference to the initialized value without running the
                /// builder's drop logic.
                ///
                /// # Safety
                ///
                /// The underlying storage must contain a valid, fully initialized value.
                /// The initialization markers alone do not guarantee this if unsafe builder
                /// methods have been used incorrectly.
                #[inline]
                #vis unsafe fn into_assume_init_mut(mut self) -> &'_wincode_inner mut #builder_dst {
                    let mut this = ::core::mem::ManuallyDrop::new(self);
                    // SAFETY: reference lives beyond the scope of the builder, and builder is forgotten.
                    let inner = unsafe { ::core::ptr::read(&mut this.inner) };
                    // SAFETY: Caller asserts the `MaybeUninit<T>` is in an initialized state.
                    unsafe {
                        inner.assume_init_mut()
                    }
                }

                /// Forgets the builder, disabling its drop logic.
                ///
                /// This method does not check whether every field is initialized. Calling it
                /// before initialization is complete prevents the builder from dropping any
                /// fields it currently tracks and may leak their resources.
                #[inline]
                #vis const fn finish(self) {
                    ::core::mem::forget(self);
                }
            }
        }
    };

    // Generate the helper methods for the builder.
    let builder_helpers = fields.iter().enumerate().map(|(i, field)| {
        let ty = &field.ty;
        let target_reader_bound = field.target_resolved();
        let ident = field.struct_member_ident(i);
        let ident_string = field.struct_member_ident_to_string(i);
        let uninit_mut_ident = format_ident!("uninit_{ident_string}_mut");
        let uninit_ref_ident = format_ident!("uninit_{ident_string}_ref");
        let read_field_ident = format_ident!("read_{ident_string}");
        let write_uninit_field_ident = format_ident!("write_{ident_string}");
        let assume_init_field_ident = format_ident!("assume_init_{ident_string}");
        let init_with_field_ident = format_ident!("init_{ident_string}_with");
        // The bit index for the field.
        let index_bit = LitInt::new(&(1u128 << i).to_string(), Span::call_site());
        let set_index_bit = quote! {
            self.init_set |= #index_bit;
        };

        quote! {
            /// Returns a mutable `MaybeUninit` projection of this field.
            #[inline]
            #vis const fn #uninit_mut_ident(&mut self) -> &mut ::core::mem::MaybeUninit<#ty> {
                // SAFETY:
                // - `self.inner` is a valid reference to a `MaybeUninit<#builder_dst>`.
                // - We return the field as `&mut MaybeUninit<#ty>`, so
                //   the field is never exposed as initialized.
                unsafe { &mut *(&raw mut (*self.inner.as_mut_ptr()).#ident).cast() }
            }


            /// Returns a shared `MaybeUninit` projection of this field.
            ///
            /// This does not indicate whether the field is initialized and does not alter
            /// its initialization marker.
            #[inline]
            #vis const fn #uninit_ref_ident(&self) -> &::core::mem::MaybeUninit<#ty> {
                // SAFETY:
                // - `self.inner` is a valid reference to a `MaybeUninit<#builder_dst>`.
                // - We return the field as `&MaybeUninit<#ty>`, so
                //   the field is never exposed as initialized.
                unsafe { &*(&raw const (*self.inner.as_ptr()).#ident).cast() }
            }

            /// Write a value into this field.
            ///
            /// If this field is already initialized, this method overwrites the
            /// previous value without dropping it. Only the newly written value remains
            /// tracked. Repeated calls may therefore leak resources or skip other
            /// destructor side effects.
            // This method can be marked `const` in the future when MSRV is >= 1.85.
            #[inline]
            #vis fn #write_uninit_field_ident(&mut self, val: #ty) -> &mut Self {
                self.#uninit_mut_ident().write(val);
                #set_index_bit
                self
            }

            /// Read a value from the reader into this field.
            ///
            /// If this field is already initialized and the read succeeds, this method
            /// overwrites the previous value without dropping it. Only the newly written
            /// value remains tracked. Repeated calls may therefore leak resources or skip
            /// other destructor side effects.
            ///
            /// If the read fails, the field's initialization marker is unchanged.
            #[inline]
            #vis fn #read_field_ident <'de>(&mut self, reader: impl #crate_name::io::Reader<'de>) -> #crate_name::ReadResult<&mut Self>
            where
                #target_reader_bound: #crate_name::SchemaRead<'de, __WincodeConfig, Dst = #ty>,
            {
                <#target_reader_bound as #crate_name::SchemaRead<'de, __WincodeConfig>>::read(
                    reader,
                    self.#uninit_mut_ident(),
                )?;
                #set_index_bit
                Ok(self)
            }

            /// Initialize the field with a given initializer function.
            ///
            /// If this field is already initialized and the initializer succeeds, this method
            /// overwrites the previous value without dropping it. Only the newly written
            /// value remains tracked. Repeated calls may therefore leak resources or skip
            /// other destructor side effects.
            ///
            /// # Safety
            ///
            /// The caller must guarantee that the initializer function fully initializes the field.
            #[inline]
            #vis unsafe fn #init_with_field_ident(&mut self, mut initializer: impl FnMut(&mut ::core::mem::MaybeUninit<#ty>) -> #crate_name::ReadResult<()>) -> #crate_name::ReadResult<&mut Self> {
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
    let _repr = extract_repr(&input, "UninitBuilder")?;
    let args = SchemaArgs::from_derive_input(&input)?;
    let crate_name = get_crate_name(&args);
    let uninit_builder = impl_uninit_builder(&args, &crate_name)?;

    Ok(quote! {
        #uninit_builder
    })
}
