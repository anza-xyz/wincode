use {
    core::str,
    proc_macro2::{Ident, Literal, Span},
    quote::quote,
    std::io::{Result, Write},
};

/// Generate `SchemaWrite` and `SchemaRead` implementations for tuples up to the given arity.
#[allow(clippy::arithmetic_side_effects)]
pub fn generate(arity: usize, mut out: impl Write) -> Result<()> {
    // Avoid single item tuples and avoid running out of alphabet.
    assert!(arity > 1 && arity <= 26, "arity must be > 1 and <= 26");

    for arity in 2..=arity {
        let mut alpha = 'A'..='Z';
        let params: Vec<_> = (0..arity)
            .map(|_| {
                let char_byte = [alpha.next().unwrap() as u8];
                let str = unsafe { str::from_utf8_unchecked(&char_byte) };
                Ident::new(str, Span::call_site())
            })
            .collect();
        let idxs: Vec<_> = (0..arity).map(Literal::usize_unsuffixed).collect();

        // The generic tuple (A, B, C, ...)
        let params_tuple = quote! { ( #(#params),* ) };

        let size_impl = {
            let parts = params.iter().zip(&idxs).map(
                |(ident, i)| quote!( <#ident as crate::SchemaWrite<Cfg>>::size_of(&value.#i)? ),
            );
            quote!(#(#parts)+*)
        };

        let write_impl = params
            .iter()
            .zip(&idxs)
            .map(|(ident, i)| quote!( <#ident as crate::SchemaWrite<Cfg>>::write(writer.by_ref(), &value.#i)?; ))
            .collect::<Vec<_>>();

        let read_impl = params
            .iter()
            .zip(&idxs)
            .enumerate()
            .map(|(i, (ident, index))| {
                let init_count = if i == arity - 1 {
                    quote! {}
                } else {
                    quote! { *init_count += 1; }
                };
                quote! {
                    <#ident as crate::SchemaRead<'de, Cfg>>::read(
                        reader.by_ref(),
                        unsafe { &mut *(&raw mut (*dst_ptr).#index).cast() }
                    )?;
                    #init_count
                }
            })
            .collect::<Vec<_>>();

        let write_static_size = params.iter().map(|ident| {
            quote! { <#ident as crate::SchemaWrite<Cfg>>::TYPE_META }
        });
        let read_static_size = params.iter().map(|ident| {
            quote! { <#ident as crate::SchemaRead<'de, Cfg>>::TYPE_META }
        });

        // Tuples don't have guaranteed layout, so we never mark them as zero-copy.
        let static_size_impl_write = quote! {
            TypeMeta::join_types([#(#write_static_size),*]).keep_zero_copy(false)
        };
        let static_size_impl_read = quote! {
            TypeMeta::join_types([#(#read_static_size),*]).keep_zero_copy(false)
        };

        let drop_arms = (0..arity).map(|init_count| {
            if init_count == 0 {
                // Nothing initialized.
                return quote!(0u8 => {});
            }
            // Generate code to drop already initialized fields in reverse order.
            let drops = idxs[..init_count].iter().rev().map(|i| {
                quote! { unsafe { core::ptr::drop_in_place(&raw mut (*dst_ptr).#i); } }
            });

            let cnt = init_count as u8;
            quote!(#cnt => { #(#drops)* })
        });

        let stream = quote! {
            unsafe impl<Cfg: crate::config::Config, #(#params),*> crate::SchemaWrite<Cfg> for #params_tuple
            where
                #(#params: crate::SchemaWrite<Cfg>,)*
                #(#params::Src: Sized,)*
            {
                type Src = (#(#params::Src),*);

                const TYPE_META: TypeMeta = #static_size_impl_write;

                #[inline]
                #[allow(clippy::arithmetic_side_effects)]
                fn size_of(value: &Self::Src) -> crate::WriteResult<usize> {
                    if let TypeMeta::Static { size, .. } = <Self as crate::SchemaWrite<Cfg>>::TYPE_META {
                        Ok(size)
                    } else {
                        Ok(#size_impl)
                    }
                }

                #[inline]
                fn write(mut writer: impl crate::io::Writer, value: &Self::Src) -> crate::WriteResult<()>
                {
                    use crate::io::Writer;
                    if let TypeMeta::Static { size, .. } = Self::TYPE_META {
                        // SAFETY: `size` is the serialized size of the tuple, which is the sum
                        // of the serialized sizes of the members.
                        // Calling `write` on each field will write exactly `size` bytes,
                        // fully initializing the trusted window.
                        let mut writer = unsafe { writer.write_hint(size) }?;
                        #(#write_impl)*
                        writer.finish()?;
                    } else {
                        #(#write_impl)*
                    }
                    Ok(())
                }
            }

            unsafe impl<'de, Cfg: crate::config::Config, #(#params),*> crate::SchemaRead<'de, Cfg> for #params_tuple
            where
                #(#params: crate::SchemaRead<'de, Cfg>,)*
            {
                type Dst = (#(#params::Dst),*);

                const TYPE_META: TypeMeta = #static_size_impl_read;

                #[inline]
                #[allow(clippy::arithmetic_side_effects, clippy::type_complexity)]
                fn read(
                    mut reader: impl crate::io::Reader<'de>,
                    dst: &mut core::mem::MaybeUninit<Self::Dst>
                ) -> crate::ReadResult<()>
                {
                    use crate::io::Reader;
                    let dst_ptr = dst.as_mut_ptr();
                    struct DropGuard<#(#params),*> {
                        init_count: u8,
                        dst_ptr: *mut (#(#params),*),
                    }

                    impl<#(#params),*> Drop for DropGuard<#(#params),*> {
                        #[cold]
                        fn drop(&mut self) {
                            let dst_ptr = self.dst_ptr;
                            match self.init_count {
                                #(#drop_arms,)*
                                // Impossible, given the `init_count` is bounded by the number of fields.
                                _ => { debug_assert!(false, "init_count out of bounds"); },
                            }
                        }
                    }

                    let mut guard = DropGuard { init_count: 0, dst_ptr };
                    let init_count = &mut guard.init_count;

                    if let TypeMeta::Static { size, .. } = Self::TYPE_META {
                        // SAFETY: `size` is the serialized size of the tuple, which is the sum
                        // of the serialized sizes of the members.
                        // Calling `read` on each field will consume exactly `size` bytes,
                        // fully consuming the trusted window.
                        let mut reader = unsafe { reader.read_hint(size) }?;
                        #(#read_impl)*
                    } else {
                        #(#read_impl)*
                    }

                    core::mem::forget(guard);
                    Ok(())
                }
            }
        };

        write!(out, "{stream}")?;
    }

    Ok(())
}
