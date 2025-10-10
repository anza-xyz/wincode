use {
    core::str,
    proc_macro::TokenStream,
    proc_macro2::Span,
    quote::quote,
    syn::{
        parse::{Parse, ParseStream},
        parse_macro_input, Error, Ident, Index, LitInt, Result,
    },
};

/// The maximum tuple arity to generate implementations for.
///
/// ```ignore
/// impl_tuple_schema!(16) -> (A,..=P)
/// ```
struct TupleArity(usize);

impl Parse for TupleArity {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.is_empty() {
            return Err(Error::new(
                input.span(),
                "must specify a maximum tuple arity",
            ));
        }
        let lit: LitInt = input.parse()?;
        Ok(TupleArity(lit.base10_parse()?))
    }
}

pub fn generate(input: TokenStream) -> TokenStream {
    let TupleArity(arity) = parse_macro_input!(input as TupleArity);
    // Avoid single item tuples and avoid running out of alphabet.
    assert!(arity > 2 && arity <= 26, "arity must be > 2 and <= 26");

    let impls = (2..=arity).map(|arity| {
        let mut alpha = ('A'..='Z').cycle();
        let params: Vec<_> = (0..arity)
            .map(|_| {
                let char_byte = [alpha.next().unwrap() as u8];
                let str = unsafe { str::from_utf8_unchecked(&char_byte) };
                Ident::new(str, Span::call_site())
            })
            .collect();
        let idxs: Vec<_> = (0..arity).map(Index::from).collect();

        // The generic tuple (A, B, C, ...)
        let params_tuple = quote! { ( #(#params),* ) };

        let size_impl = {
            let parts = params
                .iter()
                .zip(&idxs)
                .map(|(ident, i)| quote!( <#ident as SchemaWrite>::size_of(&value.#i)? ));
            quote!(0usize #(+#parts)*)
        };

        let write_impl = params
            .iter()
            .zip(&idxs)
            .map(|(ident, i)| quote!( <#ident as SchemaWrite>::write(writer, &value.#i)?; ));

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
                    <#ident as SchemaRead>::read(
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
                quote! { unsafe { ptr::drop_in_place(&mut (*dst_ptr).#i); } }
            });

            let cnt = init_count as u8;
            quote!(#cnt => { #(#drops)* })
        });

        quote! {
            impl<#(#params),*> SchemaWrite for #params_tuple
            where
                #(#params: crate::SchemaWrite,)*
                #(#params::Src: Sized,)*
            {
                type Src = (#(#params::Src),*);

                #[inline]
                fn size_of(value: &Self::Src) -> WriteResult<usize> {
                    Ok(#size_impl)
                }

                #[inline]
                fn write(writer: &mut Writer, value: &Self::Src) -> WriteResult<()>
                {
                    #(#write_impl)*
                    Ok(())
                }
            }

            impl<'de, #(#params),*> SchemaRead<'de> for #params_tuple
            where
                #(#params: SchemaRead<'de>,)*
            {
                type Dst = (#(#params::Dst),*);

                #[inline]
                fn read(
                    reader: &mut Reader<'de>,
                    dst: &mut MaybeUninit<Self::Dst>
                ) -> ReadResult<()>
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

                    mem::forget(guard);
                    Ok(())
                }
            }
        }
    });

    quote! {
        const _: () = {
            use crate::{SchemaRead, SchemaWrite, WriteResult, ReadResult, io::{Reader, Writer}};
            use core::{mem::{self, MaybeUninit}, ptr};
            #(#impls)*
        };
    }
    .into()
}
