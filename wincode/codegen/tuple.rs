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
        let mut alpha = ('A'..='Z').cycle();
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
            let parts = params
                .iter()
                .zip(&idxs)
                .map(|(ident, i)| quote!( <#ident as crate::SchemaWrite>::size_of(&value.#i)? ));
            quote!(#(#parts)+*)
        };

        let write_impl = params
            .iter()
            .zip(&idxs)
            .map(|(ident, i)| quote!( <#ident as crate::SchemaWrite>::write(writer, &value.#i)?; ));

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
                    <#ident as crate::SchemaRead<'de>>::read(
                        reader,
                        unsafe { &mut *(&raw mut (*dst_ptr).#index).cast() }
                    )?;
                    #init_count
                }
            });

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
            impl<#(#params),*> crate::SchemaWrite for #params_tuple
            where
                #(#params: crate::SchemaWrite,)*
                #(#params::Src: Sized,)*
            {
                type Src = (#(#params::Src),*);

                #[inline]
                #[allow(clippy::arithmetic_side_effects)]
                fn size_of(value: &Self::Src) -> crate::WriteResult<usize> {
                    Ok(#size_impl)
                }

                #[inline]
                fn write(writer: &mut crate::io::Writer, value: &Self::Src) -> crate::WriteResult<()>
                {
                    #(#write_impl)*
                    Ok(())
                }
            }

            impl<'de, #(#params),*> crate::SchemaRead<'de> for #params_tuple
            where
                #(#params: crate::SchemaRead<'de>,)*
            {
                type Dst = (#(#params::Dst),*);

                #[inline]
                #[allow(clippy::arithmetic_side_effects, clippy::type_complexity)]
                fn read(
                    reader: &mut crate::io::Reader<'de>,
                    dst: &mut core::mem::MaybeUninit<Self::Dst>
                ) -> crate::ReadResult<()>
                {
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

                    #(#read_impl)*

                    core::mem::forget(guard);
                    Ok(())
                }
            }
        };

        write!(out, "{stream}")?;
    }

    Ok(())
}
