use {
    darling::{
        ast::{Data, Fields},
        FromDeriveInput, FromField, FromVariant, Result,
    },
    proc_macro2::{Span, TokenStream},
    quote::quote,
    std::{
        borrow::Cow,
        collections::VecDeque,
        fmt::{self, Display},
    },
    syn::{
        parse_quote,
        spanned::Spanned,
        visit::{self, Visit},
        visit_mut::{self, VisitMut},
        DeriveInput, Expr, ExprLit, GenericArgument, Generics, Ident, Lifetime, Lit, LitInt,
        Member, Path, Type, TypeImplTrait, TypeParamBound, TypeReference, TypeTraitObject,
        Visibility,
    },
};

#[derive(FromField)]
#[darling(attributes(wincode), forward_attrs)]
pub(crate) struct Field {
    pub(crate) ident: Option<Ident>,
    pub(crate) ty: Type,

    /// Per-field `SchemaRead` and `SchemaWrite` override.
    ///
    /// This is how users can opt in to optimized `SchemaRead` and `SchemaWrite` implementations
    /// for a particular field.
    ///
    /// For example:
    /// ```ignore
    /// struct Foo {
    ///     #[wincode(with = "Pod<_>")]
    ///     x: [u8; u64],
    /// }
    /// ```
    #[darling(default)]
    pub(crate) with: Option<Type>,
}

pub(crate) trait TypeExt {
    /// Replace any lifetimes on this type with the given lifetime.
    ///
    /// For example, we can transform:
    /// ```ignore
    /// &'a str -> &'de str
    /// ```
    fn with_lifetime(&self, ident: &'static str) -> Type;

    /// Replace any inference tokens on this type with the fully qualified generic arguments
    /// of the given `infer` type.
    ///
    /// For example, we can transform:
    /// ```ignore
    /// let target = parse_quote!(Pod<_>);
    /// let actual = parse_quote!([u8; u64]);
    /// assert_eq!(target.with_infer(actual), parse_quote!(Pod<[u8; u64]>));
    /// ```
    fn with_infer(&self, infer: &Type) -> Type;
}

impl TypeExt for Type {
    fn with_lifetime(&self, ident: &'static str) -> Type {
        let mut this = self.clone();
        ReplaceLifetimes(ident).visit_type_mut(&mut this);
        this
    }

    fn with_infer(&self, infer: &Type) -> Type {
        let mut this = self.clone();

        // First, collect the generic arguments of the `infer` type.
        let mut stack = GenericStack::new();
        stack.visit_type(infer);
        // If there are no generic arguments on self, infer the given `infer` type itself.
        if stack.0.is_empty() {
            stack.0.push_back(infer);
        }
        // Perform the replacement.
        let mut infer = InferGeneric::from(stack);
        infer.visit_type_mut(&mut this);
        this
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum TraitImpl {
    SchemaRead,
    SchemaWrite,
}

impl Display for TraitImpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Field {
    /// Get the target type for a field.
    ///
    /// If the field has a `with` attribute, return it.
    /// Otherwise, return the type.
    pub(crate) const fn target(&self) -> &Type {
        if let Some(with) = &self.with {
            with
        } else {
            &self.ty
        }
    }

    /// Get the target type for a field with any inference tokens resolved.
    ///
    /// Users may annotate a field using `with` attributes that contain inference tokens,
    /// such as `Pod<_>`. This method will resolve those inference tokens to the actual type.
    ///
    /// The following will resolve to `Pod<[u8; u64]>` for `x`:
    ///
    /// ```ignore
    /// struct Foo {
    ///     #[wincode(with = "Pod<_>")]
    ///     x: [u8; u64],
    /// }
    /// ```
    pub(crate) fn target_resolved(&self) -> Type {
        self.target().with_infer(&self.ty)
    }

    /// Get the identifier for a struct member.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple struct), return an anonymous identifier with the given index.
    pub(crate) fn struct_member_ident(&self, index: usize) -> Member {
        if let Some(ident) = &self.ident {
            ident.clone().into()
        } else {
            index.into()
        }
    }

    /// Like [`Self::struct_member_ident`], but return a `String`.
    pub(crate) fn struct_member_ident_to_string(&self, index: usize) -> String {
        if let Some(ident) = &self.ident {
            ident.to_string()
        } else {
            index.to_string()
        }
    }
}

pub(crate) trait FieldsExt {
    fn type_meta_impl(&self, trait_impl: TraitImpl, repr: &StructRepr) -> TokenStream;
    /// Get an iterator over the identifiers for the struct members.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple struct), return an anonymous identifier.
    fn struct_member_ident_iter(&self) -> impl Iterator<Item = Member>;
    /// Get an iterator over type members as anonymous identifiers.
    ///
    /// If `prefix` is provided, the identifiers will be prefixed with the given str.
    ///
    /// Useful for tuple destructuring where using an index of a tuple struct as an identifier would
    /// incorrectly match a literal integer.
    ///
    /// E.g., given the struct:
    /// ```
    /// struct Foo(u8, u16);
    /// ```
    /// Iterating over the identifiers would yield [0, 1].
    ///
    /// Using these integer identifiers in a match statement when determining static size, for example, is incorrect:
    /// ```ignore
    /// if let (TypeMeta::Static { size: 0, .. }) = (<field as SchemaWrite>::TYPE_META) {
    /// ```
    ///
    /// You actually want an anonymous identifier, like `a`, `b`, etc.
    fn member_anon_ident_iter(&self, prefix: Option<&str>) -> impl Iterator<Item = Ident>;
    /// Get an iterator over the identifiers for the enum members.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple enum), return an anonymous identifier.
    ///
    /// Note this is unnecessary for unit enums, as they will not have fields.
    fn enum_member_ident_iter(
        &self,
        prefix: Option<&str>,
    ) -> impl Iterator<Item = Cow<'_, Ident>> + Clone;
}

impl FieldsExt for Fields<Field> {
    /// Generate the `TYPE_META` implementation for a struct.
    ///
    /// Enums cannot have a statically known serialized size (unless all variants are unit enums), so don't use this for enums.
    fn type_meta_impl(&self, trait_impl: TraitImpl, repr: &StructRepr) -> TokenStream {
        let tuple_expansion = match trait_impl {
            TraitImpl::SchemaRead => {
                let items = self.iter().map(|field| {
                    let target = field.target_resolved().with_lifetime("de");
                    quote! { <#target as SchemaRead<'de>>::TYPE_META }
                });
                quote! { #(#items),* }
            }
            TraitImpl::SchemaWrite => {
                let items = self.iter().map(|field| {
                    let target = field.target_resolved();
                    quote! { <#target as SchemaWrite>::TYPE_META }
                });
                quote! { #(#items),* }
            }
        };
        // No need to prefix, as this is only used in a struct context, where the static size is
        // known at compile time.
        let anon_idents = self.member_anon_ident_iter(None).collect::<Vec<_>>();
        let zero_copy_idents = self.member_anon_ident_iter(Some("zc_")).collect::<Vec<_>>();
        let is_zero_copy_eligible = repr.is_zero_copy_eligible();
        // Extract sizes and zero-copy flags from the TYPE_META implementations of the fields of the struct.
        // We can use this in aggregate to determine the static size and zero-copy eligibility of the struct.
        //
        // - The static size of a struct is the sum of the static sizes of its fields.
        // - The zero-copy eligibility of a struct is the logical AND of the zero-copy eligibility flags of its fields
        //   and the zero-copy eligibility the struct representation (e.g., `#[repr(transparent)]` or `#[repr(C)]`).
        quote! {
            // This will simultaneously only match if all fields are `TypeMeta::Static`, and extract the sizes and zero-copy flags
            // for each field.
            // If any field is not `TypeMeta::Static`, the entire match will fail, and we will fall through to the `Dynamic` case.
            if let (#(TypeMeta::Static { size: #anon_idents, zero_copy: #zero_copy_idents }),*) = (#tuple_expansion) {
                let serialized_size = #(#anon_idents)+*;
                // Bincode never serializes padding, so for types to qualify for zero-copy, the summed serialized size of
                // the fields must be equal to the in-memory size of the type. This is because zero-copy types
                // may be read/written directly using their in-memory representation; padding disqualifies a type
                // from this kind of optimization.
                let no_padding = serialized_size == core::mem::size_of::<Self>();
                TypeMeta::Static { size: serialized_size, zero_copy: no_padding && #is_zero_copy_eligible && #(#zero_copy_idents)&&* }
            } else {
                TypeMeta::Dynamic
            }
        }
    }

    fn struct_member_ident_iter(&self) -> impl Iterator<Item = Member> {
        self.iter()
            .enumerate()
            .map(|(i, f)| f.struct_member_ident(i))
    }

    fn member_anon_ident_iter(&self, prefix: Option<&str>) -> impl Iterator<Item = Ident> {
        anon_ident_iter(prefix).take(self.len())
    }

    fn enum_member_ident_iter(
        &self,
        prefix: Option<&str>,
    ) -> impl Iterator<Item = Cow<'_, Ident>> + Clone {
        let mut alpha = anon_ident_iter(prefix);
        self.iter().map(move |field| {
            if let Some(ident) = &field.ident {
                Cow::Borrowed(ident)
            } else {
                Cow::Owned(
                    alpha
                        .next()
                        .expect("alpha iterator should never be exhausted"),
                )
            }
        })
    }
}

fn anon_ident_iter(prefix: Option<&str>) -> impl Iterator<Item = Ident> + Clone + use<'_> {
    let prefix = prefix.unwrap_or("");
    ('a'..='z').cycle().enumerate().map(move |(i, ch)| {
        let wrap = i / 26;
        let name = if wrap == 0 {
            format!("{}{}", prefix, ch)
        } else {
            format!("{}{}{}", prefix, ch, wrap - 1)
        };
        Ident::new(&name, Span::call_site())
    })
}

#[derive(FromVariant)]
#[darling(attributes(wincode), forward_attrs)]
pub(crate) struct Variant {
    pub(crate) ident: Ident,
    pub(crate) fields: Fields<Field>,
    #[darling(default)]
    pub(crate) tag: Option<Expr>,
}

impl Variant {
    /// Get the discriminant expression for the variant.
    ///
    /// If the variant has a `tag` attribute, return it.
    /// Otherwise, return an integer literal with the given field index (the bincode default).
    pub(crate) fn discriminant(&self, field_index: usize) -> Cow<'_, Expr> {
        self.tag.as_ref().map(Cow::Borrowed).unwrap_or_else(|| {
            Cow::Owned(Expr::Lit(ExprLit {
                lit: Lit::Int(LitInt::new(&field_index.to_string(), Span::call_site())),
                attrs: vec![],
            }))
        })
    }
}

pub(crate) type ImplBody = Data<Variant, Field>;

/// Generate code to suppress unused field lints.
///
/// If `from` is specified, the user is creating a mapping type, in which case those struct/enum
/// fields will almost certainly be unused, as they exist purely to describe the mapping. This will
/// trigger unused field lints.
///
/// Create a private, never-called item that references the fields to avoid unused field lints.
/// Users can disable this by setting `no_suppress_unused`.
pub(crate) fn suppress_unused_fields(args: &SchemaArgs) -> TokenStream {
    if args.from.is_none() || args.no_suppress_unused {
        return quote! {};
    }

    match &args.data {
        Data::Struct(fields) if !fields.is_empty() => {
            let idents = fields.struct_member_ident_iter();
            let ident = &args.ident;
            let (impl_generics, ty_generics, where_clause) = args.generics.split_for_impl();
            quote! {
                const _: () = {
                    #[allow(dead_code, unused_variables)]
                    fn __wincode_use_fields #impl_generics (value: &#ident #ty_generics) #where_clause {
                        let _ = ( #( &value.#idents ),* );
                    }
                };
            }
        }
        // We can't suppress the lint on on enum variants, as that would require being able to
        // construct an arbitrary enum variant, which we can't do. Users will have to manually
        // add a `#[allow(unused)]` / `#[allow(dead_code)]` attribute to the enum variant if they want to
        // suppress the lint, or make it public.
        _ => {
            quote! {}
        }
    }
}

/// Get the path to `wincode` based on the `internal` flag.
pub(crate) fn get_crate_name(args: &SchemaArgs) -> Path {
    if args.internal {
        parse_quote!(crate)
    } else {
        parse_quote!(::wincode)
    }
}

/// Get the target `Src` or `Dst` type for a `SchemaRead` or `SchemaWrite` implementation.
///
/// If `from` is specified, the user is implementing `SchemaRead` or `SchemaWrite` on a foreign type,
/// so we return the `from` type.
/// Otherwise, we return the ident + ty_generics (target is `Self`).
pub(crate) fn get_src_dst(args: &SchemaArgs) -> Cow<'_, Type> {
    if let Some(from) = args.from.as_ref() {
        Cow::Borrowed(from)
    } else {
        Cow::Owned(parse_quote!(Self))
    }
}

/// Get the fully qualified target `Src` or `Dst` type for a `SchemaRead` or `SchemaWrite` implementation.
///
/// Like [`Self::get_src_dst`], but rather than producing `Self` when implementing a local type,
/// we return the fully qualified type.
pub(crate) fn get_src_dst_fully_qualified(args: &SchemaArgs) -> Cow<'_, Type> {
    if let Some(from) = args.from.as_ref() {
        Cow::Borrowed(from)
    } else {
        let ident = &args.ident;
        let (_, ty_generics, _) = args.generics.split_for_impl();
        Cow::Owned(parse_quote!(#ident #ty_generics))
    }
}

#[derive(FromDeriveInput)]
#[darling(attributes(wincode), forward_attrs)]
pub(crate) struct SchemaArgs {
    pub(crate) ident: Ident,
    pub(crate) generics: Generics,
    pub(crate) data: ImplBody,
    pub(crate) vis: Visibility,

    /// Used to determine the `wincode` path.
    ///
    /// If `internal` is `true`, the generated code will use the `crate::` path.
    /// Otherwise, it will use the `wincode` path.
    #[darling(default)]
    pub(crate) internal: bool,
    /// Specifies whether the type's implementations should map to another type.
    ///
    /// Useful for implementing `SchemaRead` and `SchemaWrite` on foreign types.
    #[darling(default)]
    pub(crate) from: Option<Type>,
    /// Specifies whether to suppress unused field lints on structs.
    ///
    /// Only applicable if `from` is specified.
    #[darling(default)]
    pub(crate) no_suppress_unused: bool,
    /// Specifies whether to generate placement initialization struct helpers on `SchemaRead` implementations.
    #[darling(default)]
    pub(crate) struct_extensions: bool,
    /// Specifies the encoding to use for enum discriminants.
    ///
    /// If specified, the enum discriminants will be encoded using the given type's `SchemaWrite`
    /// and `SchemaRead` implementations.
    /// Otherwise, the enum discriminants will be encoded using the default encoding (`u32`).
    #[darling(default)]
    pub(crate) tag_encoding: Option<Type>,
}

/// The default encoding to use for enum discriminants.
///
/// Bincode's default discriminant encoding is `u32`.
///
/// Note in the public APIs we refer to `tag` to mean the discriminant encoding
/// for friendlier naming.
#[inline]
pub(crate) fn default_tag_encoding() -> Type {
    parse_quote!(u32)
}

/// Metadata about the `#[repr]` attribute on a struct.
#[derive(Default)]
pub(crate) struct StructRepr {
    layout: Layout,
}

#[derive(Default)]
pub(crate) enum Layout {
    #[default]
    Rust,
    Transparent,
    C,
}

impl StructRepr {
    /// Check if this `#[repr]` attribute is eligible for zero-copy deserialization.
    ///
    /// Zero-copy deserialization is only supported for `#[repr(transparent)]` and `#[repr(C)]` structs.
    pub(crate) const fn is_zero_copy_eligible(&self) -> bool {
        matches!(self.layout, Layout::Transparent | Layout::C)
    }
}

/// Extract the `#[repr]` attribute from the derive input, returning an error if the type is packed (not supported).
pub(crate) fn extract_repr(input: &DeriveInput, trait_impl: TraitImpl) -> Result<StructRepr> {
    let mut struct_repr = StructRepr::default();
    for attr in &input.attrs {
        if !attr.path().is_ident("repr") {
            continue;
        }

        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("packed") {
                return Err(meta.error(format!(
                    "`{trait_impl}` cannot be derived for types annotated with `#[repr(packed)]` \
                     or `#[repr(packed(n))]`"
                )));
            }

            // Rust will reject a struct with both `#[repr(transparent)]` and `#[repr(C)]`, so we
            // don't need to check for conflicts here.
            if meta.path.is_ident("C") {
                struct_repr.layout = Layout::C;
                return Ok(());
            }
            if meta.path.is_ident("transparent") {
                struct_repr.layout = Layout::Transparent;
                return Ok(());
            }

            // Parse left over input.
            _ = meta.input.parse::<TokenStream>();

            Ok(())
        })?;
    }

    Ok(struct_repr)
}

/// Visitor to recursively collect the generic arguments of a type.
struct GenericStack<'ast>(VecDeque<&'ast Type>);
impl<'ast> GenericStack<'ast> {
    const fn new() -> Self {
        Self(VecDeque::new())
    }
}

impl<'ast> Visit<'ast> for GenericStack<'ast> {
    fn visit_generic_argument(&mut self, ga: &'ast GenericArgument) {
        if let GenericArgument::Type(t) = ga {
            match t {
                Type::Slice(slice) => {
                    self.0.push_back(&slice.elem);
                    return;
                }
                Type::Array(array) => {
                    self.0.push_back(&array.elem);
                    return;
                }
                Type::Path(tp)
                    if tp.path.segments.iter().any(|seg| {
                        matches!(seg.arguments, syn::PathArguments::AngleBracketed(_))
                    }) =>
                {
                    // Has generics, recurse.
                }
                _ => self.0.push_back(t),
            }
        }

        // Not a type argument, recurse as normal.
        visit::visit_generic_argument(self, ga);
    }
}

/// Visitor to recursively replace inference tokens with the collected generic arguments.
struct InferGeneric<'ast>(VecDeque<&'ast Type>);
impl<'ast> From<GenericStack<'ast>> for InferGeneric<'ast> {
    fn from(stack: GenericStack<'ast>) -> Self {
        Self(stack.0)
    }
}

impl<'ast> VisitMut for InferGeneric<'ast> {
    fn visit_generic_argument_mut(&mut self, ga: &mut GenericArgument) {
        if let GenericArgument::Type(Type::Infer(_)) = ga {
            let ty = self
                .0
                .pop_front()
                .expect("wincode-derive: inference mismatch: not enough collected types for `_`")
                .clone();
            *ga = GenericArgument::Type(ty);
        }
        visit_mut::visit_generic_argument_mut(self, ga);
    }

    fn visit_type_array_mut(&mut self, array: &mut syn::TypeArray) {
        if let Type::Infer(_) = &*array.elem {
            let ty = self
                .0
                .pop_front()
                .expect("wincode-derive: inference mismatch: not enough collected types for `_`")
                .clone();
            *array.elem = ty;
        }
        visit_mut::visit_type_array_mut(self, array);
    }
}

/// Visitor to recursively replace a given type's lifetimes with the given lifetime name.
struct ReplaceLifetimes(&'static str);

impl ReplaceLifetimes {
    /// Replace the lifetime with `'de`, preserving the span.
    fn replace(&self, t: &mut Lifetime) {
        t.ident = Ident::new(self.0, t.ident.span());
    }

    fn new_from_reference(&self, t: &mut TypeReference) {
        t.lifetime = Some(Lifetime {
            apostrophe: t.and_token.span(),
            ident: Ident::new(self.0, t.and_token.span()),
        })
    }
}

impl VisitMut for ReplaceLifetimes {
    fn visit_type_reference_mut(&mut self, t: &mut TypeReference) {
        match &mut t.lifetime {
            Some(l) => self.replace(l),
            // Lifetime may be elided. Prefer being explicit, as the implicit lifetime
            // may refer to a lifetime that is not `'de` (e.g., 'a on some type `Foo<'a>`).
            None => {
                self.new_from_reference(t);
            }
        }
        visit_mut::visit_type_reference_mut(self, t);
    }

    fn visit_generic_argument_mut(&mut self, ga: &mut GenericArgument) {
        if let GenericArgument::Lifetime(l) = ga {
            self.replace(l);
        }
        visit_mut::visit_generic_argument_mut(self, ga);
    }

    fn visit_type_trait_object_mut(&mut self, t: &mut TypeTraitObject) {
        for bd in &mut t.bounds {
            if let TypeParamBound::Lifetime(l) = bd {
                self.replace(l);
            }
        }
        visit_mut::visit_type_trait_object_mut(self, t);
    }

    fn visit_type_impl_trait_mut(&mut self, t: &mut TypeImplTrait) {
        for bd in &mut t.bounds {
            if let TypeParamBound::Lifetime(l) = bd {
                self.replace(l);
            }
        }
        visit_mut::visit_type_impl_trait_mut(self, t);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer_generic() {
        let src: Type = parse_quote!(Foo<_>);
        let infer = parse_quote!(Bar<u8>);
        assert_eq!(src.with_infer(&infer), parse_quote!(Foo<u8>));

        let src: Type = parse_quote!(Foo<_, _>);
        let infer = parse_quote!(Bar<u8, u16>);
        assert_eq!(src.with_infer(&infer), parse_quote!(Foo<u8, u16>));

        let src: Type = parse_quote!(Pod<_>);
        let infer = parse_quote!([u8; u64]);
        assert_eq!(src.with_infer(&infer), parse_quote!(Pod<[u8; u64]>));

        let src: Type = parse_quote!(containers::Vec<containers::Pod<_>>);
        let infer = parse_quote!(Vec<u8>);
        assert_eq!(
            src.with_infer(&infer),
            parse_quote!(containers::Vec<containers::Pod<u8>>)
        );

        let src: Type = parse_quote!(containers::Box<[Pod<_>]>);
        let infer = parse_quote!(Box<[u8]>);
        assert_eq!(
            src.with_infer(&infer),
            parse_quote!(containers::Box<[Pod<u8>]>)
        );

        let src: Type = parse_quote!(containers::Box<[Pod<[_; 32]>]>);
        let infer = parse_quote!(Box<[u8; 32]>);
        assert_eq!(
            src.with_infer(&infer),
            parse_quote!(containers::Box<[Pod<[u8; 32]>]>)
        );

        // Not an actual use-case, but added for robustness.
        let src: Type = parse_quote!(containers::Vec<containers::Box<[containers::Pod<_>]>>);
        let infer = parse_quote!(Vec<Box<[u8]>>);

        assert_eq!(
            src.with_infer(&infer),
            parse_quote!(containers::Vec<containers::Box<[containers::Pod<u8>]>>)
        );

        // Similarly, not a an actual use-case.
        let src: Type =
            parse_quote!(Pair<containers::Box<[containers::Pod<_>]>, containers::Pod<_>>);
        let infer: Type = parse_quote!(Pair<Box<[Foo<Bar<u8>>]>, u16>);
        assert_eq!(
            src.with_infer(&infer),
            parse_quote!(
                Pair<containers::Box<[containers::Pod<Foo<Bar<u8>>>]>, containers::Pod<u16>>
            )
        )
    }

    #[test]
    fn test_override_ref_lifetime() {
        let target: Type = parse_quote!(Foo<'a>);
        assert_eq!(target.with_lifetime("de"), parse_quote!(Foo<'de>));

        let target: Type = parse_quote!(&'a str);
        assert_eq!(target.with_lifetime("de"), parse_quote!(&'de str));
    }

    #[test]
    fn test_anon_ident_iter() {
        let mut iter = anon_ident_iter(None);
        assert_eq!(iter.next().unwrap().to_string(), "a");
        assert_eq!(iter.nth(25).unwrap().to_string(), "a0");
        assert_eq!(iter.next().unwrap().to_string(), "b0");
        assert_eq!(iter.nth(24).unwrap().to_string(), "a1");
    }
}
