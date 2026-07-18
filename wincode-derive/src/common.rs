use {
    darling::{
        FromDeriveInput, FromField, FromMeta, FromVariant, Result,
        ast::{Data, Fields, NestedMeta, Style},
        util::Flag,
    },
    proc_macro2::{Span, TokenStream},
    quote::{ToTokens as _, quote},
    std::{
        borrow::Cow,
        collections::{HashSet, VecDeque},
        fmt::{self, Display},
        rc::Rc,
    },
    syn::{
        DeriveInput, Expr, GenericArgument, Generics, Ident, Lifetime, Lit, LitInt, Member, Path,
        Type, TypeImplTrait, TypeParamBound, TypeReference, TypeTraitObject, Visibility,
        parse_quote,
        spanned::Spanned,
        visit::{self, Visit},
        visit_mut::{self, VisitMut},
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

    /// Opt out of writing or reading this field.
    ///
    /// The field will be initialized using one of the available modes:
    /// * `SkipMode::Default` - using `Default::default()`
    /// * `SkipMode::DefaultVal(expr)` - using value provided by (typically constant) `expr`
    pub(crate) skip: Option<SkipMode>,

    /// Flag to enable context for the field.
    ///
    /// Eventually plumbed through to the `context` field
    /// by stamping `context` from [`SchemaArgs`].
    ///
    /// This allows users to specify #[wincode(context)] on a field
    /// without having to fully qualify the type like is required
    /// on the root type attribute.
    #[darling(rename = "context")]
    context_flag: Flag,
    /// Stamped onto the field from [`SchemaArgs`] for easy access in methods.
    #[darling(skip)]
    pub(crate) context: Option<Type>,
    /// Stamped onto the field from [`SchemaArgs`] for easy access in methods.
    ///
    /// Always `Some`. Only marked as `Option` because `Path` does not have a `Default`
    /// implementation for `#[darling(skip)]`.
    #[darling(skip)]
    crate_name: Option<Path>,
    /// Stamped onto the field from [`SchemaArgs`] for easy access in methods,
    /// and to avoid allocating a `Vec<Lifetime>` for each invocation.
    #[darling(skip)]
    pub(crate) context_lifetimes: Rc<[Lifetime]>,
}

#[derive(FromMeta)]
#[darling(from_word = || Ok(Self::Default))]
pub enum SkipMode {
    /// Use `Default::default()` value to initialize the field.
    Default,
    /// Use the provided expression as value to initialize the field.
    DefaultVal(Expr),
}

impl SkipMode {
    pub(crate) fn default_val_token_stream(&self) -> TokenStream {
        match self {
            Self::Default => quote! { Default::default() },
            Self::DefaultVal(val) => val.to_token_stream(),
        }
    }
}

pub(crate) trait TypeExt {
    /// Replace any lifetimes on this type with the given lifetime,
    /// excluding any lifetimes in the `exclude` list.
    fn with_lifetime_excluding(&self, ident: &str, exclude: &[Lifetime]) -> Type;

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

    /// Return whether the type contains a lifetime parameter.
    fn has_lifetime(&self) -> bool;

    /// Return whether the type contains a lifetime with the same name as `lifetime`.
    fn contains_lifetime(&self, lifetime: &Lifetime) -> bool;

    /// Return the lifetimes of this type.
    fn lifetimes(&self) -> Vec<Lifetime>;
}

impl TypeExt for Type {
    fn with_lifetime_excluding(&self, ident: &str, exclude: &[Lifetime]) -> Type {
        let mut this = self.clone();
        ReplaceLifetimes {
            replacement: ident,
            exclude,
        }
        .visit_type_mut(&mut this);
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

    fn has_lifetime(&self) -> bool {
        let mut visitor = HasLifetime(false);
        visitor.visit_type(self);
        visitor.0
    }

    fn contains_lifetime(&self, lifetime: &Lifetime) -> bool {
        let mut visitor = ContainsLifetime {
            lifetime,
            found: false,
        };
        visitor.visit_type(self);
        visitor.found
    }

    fn lifetimes(&self) -> Vec<Lifetime> {
        let mut visitor = Lifetimes(Vec::new());
        visitor.visit_type(self);
        visitor.0
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum TraitImpl {
    SchemaRead,
    SchemaWrite,
}

impl Display for TraitImpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Field {
    /// Get the target type for a field.
    ///
    /// If the field has a `with` attribute, return it.
    /// Otherwise, return the type.
    pub(crate) fn target(&self) -> &Type {
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

    pub(crate) fn has_lifetime(&self) -> bool {
        self.ty.has_lifetime()
    }

    /// Generate the trait bound for this field, including the exact destination
    /// or source type expected by the containing type.
    ///
    /// Context lifetimes remain tied to the context; other read lifetimes are
    /// rewritten to `'de` because they may borrow from the input.
    pub(crate) fn as_constraint(&self, tr: TraitImpl) -> TokenStream {
        let crate_name = self.crate_name.as_ref().unwrap();
        match tr {
            TraitImpl::SchemaRead => {
                let ty = &self
                    .ty
                    .with_lifetime_excluding("de", &self.context_lifetimes);
                if let Some(ctx) = &self.context {
                    parse_quote!(#crate_name::SchemaReadContext<'de, __WincodeConfig, #ctx, Dst = #ty>)
                } else {
                    parse_quote!(#crate_name::SchemaRead<'de, __WincodeConfig, Dst = #ty>)
                }
            }
            TraitImpl::SchemaWrite => {
                let ty = &self.ty;
                parse_quote!(#crate_name::SchemaWrite<__WincodeConfig, Src = #ty>)
            }
        }
    }

    /// Generate the schema trait applied to this field's target type.
    ///
    /// A contextual read field uses `SchemaReadContext`; ordinary read fields
    /// and all write fields use their non-contextual traits.
    pub(crate) fn qualifier(&self, tr: TraitImpl) -> TokenStream {
        let crate_name = self.crate_name.as_ref().unwrap();
        match tr {
            TraitImpl::SchemaRead => {
                if let Some(ctx) = &self.context {
                    parse_quote!(#crate_name::SchemaReadContext<'de, __WincodeConfig, #ctx>)
                } else {
                    parse_quote!(#crate_name::SchemaRead<'de, __WincodeConfig>)
                }
            }
            TraitImpl::SchemaWrite => {
                parse_quote!(#crate_name::SchemaWrite<__WincodeConfig>)
            }
        }
    }

    /// Generate `<Target as Trait>`, resolving `#[wincode(with = ...)]`
    /// inference and applying the appropriate read-lifetime transformation.
    pub(crate) fn target_fully_qualified(&self, tr: TraitImpl) -> TokenStream {
        let target = match tr {
            TraitImpl::SchemaRead => self
                .target_resolved()
                .with_lifetime_excluding("de", &self.context_lifetimes),
            TraitImpl::SchemaWrite => self.target_resolved(),
        };
        let qualifier = self.qualifier(tr);
        parse_quote!(<#target as #qualifier>)
    }
}

pub(crate) trait FieldsExt {
    fn type_meta_impl(
        &self,
        trait_impl: TraitImpl,
        repr: &StructRepr,
        crate_name: &Path,
    ) -> TokenStream;
    /// Get an iterator over the fields and their identifiers for the struct members.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple struct), return an anonymous identifier.
    fn struct_members_iter(&self) -> impl Iterator<Item = (&Field, Member)>;
    /// Get an iterator over the fields and their identifiers for the enum members.
    ///
    /// If the field has a named identifier, return it.
    /// Otherwise (tuple enum), return an anonymous identifier.
    ///
    /// Note this is unnecessary for unit enums, as they will not have fields.
    fn enum_members_iter(
        &self,
        prefix: Option<&str>,
    ) -> impl Iterator<Item = (&Field, Cow<'_, Ident>)> + Clone;
    /// Get an iterator over the fields that do not have `skip` attribute.
    fn unskipped_iter(&self) -> impl Iterator<Item = &Field> + Clone;
    /// Get an iterator over fields that contain a lifetime parameter.
    fn fields_with_lifetime_iter(&self) -> impl Iterator<Item = &Field>;
}

impl FieldsExt for Fields<Field> {
    /// Generate the `TYPE_META` implementation for a struct.
    fn type_meta_impl(
        &self,
        trait_impl: TraitImpl,
        repr: &StructRepr,
        crate_name: &Path,
    ) -> TokenStream {
        let tuple_expansion = {
            let items = self.unskipped_iter().map(|field| {
                let target = field.target_fully_qualified(trait_impl);
                quote! { #target::TYPE_META }
            });
            quote! { #(#items),* }
        };
        let is_zero_copy_eligible = repr.is_zero_copy_eligible();
        // Extract sizes and zero-copy flags from the TYPE_META implementations of the fields of the struct.
        // We can use this in aggregate to determine the static size and zero-copy eligibility of the struct.
        //
        // - The static size of a struct is the sum of the static sizes of its fields.
        // - The zero-copy eligibility of a struct is the logical AND of the zero-copy eligibility flags of its fields
        //   and the zero-copy eligibility the struct representation (e.g., `#[repr(transparent)]` or `#[repr(C)]`).
        quote! {
            // If any field is not `TypeMeta::Static`, the sum type will not match and `Dynamic` case will be used
            if let #crate_name::TypeMeta::Static { size: serialized_size, zero_copy } = #crate_name::TypeMeta::join_types([#tuple_expansion]) {
                // Bincode never serializes padding, so for types to qualify for zero-copy, the summed serialized size of
                // the fields must be equal to the in-memory size of the type. This is because zero-copy types
                // may be read/written directly using their in-memory representation; padding disqualifies a type
                // from this kind of optimization.
                let no_padding = serialized_size == core::mem::size_of::<Self>();
                #crate_name::TypeMeta::Static { size: serialized_size, zero_copy: no_padding && #is_zero_copy_eligible && zero_copy }
            } else {
                #crate_name::TypeMeta::Dynamic
            }
        }
    }

    fn struct_members_iter(&self) -> impl Iterator<Item = (&Field, Member)> {
        self.iter()
            .enumerate()
            .map(|(i, field)| (field, field.struct_member_ident(i)))
    }

    fn enum_members_iter(
        &self,
        prefix: Option<&str>,
    ) -> impl Iterator<Item = (&Field, Cow<'_, Ident>)> + Clone {
        let mut alpha = anon_ident_iter(prefix);
        self.iter().map(move |field| {
            (
                field,
                if let Some(ident) = &field.ident {
                    Cow::Borrowed(ident)
                } else {
                    Cow::Owned(
                        alpha
                            .next()
                            .expect("alpha iterator should never be exhausted"),
                    )
                },
            )
        })
    }

    fn unskipped_iter(&self) -> impl Iterator<Item = &Field> + Clone {
        self.iter().filter(|field| field.skip.is_none())
    }

    fn fields_with_lifetime_iter(&self) -> impl Iterator<Item = &Field> {
        self.iter().filter(|field| field.has_lifetime())
    }
}

fn anon_ident_iter(prefix: Option<&str>) -> impl Iterator<Item = Ident> + Clone + use<'_> {
    let prefix = prefix.unwrap_or("");
    ('a'..='z').cycle().enumerate().map(move |(i, ch)| {
        let wrap = i / 26;
        let name = if wrap == 0 {
            format!("{prefix}{ch}")
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
    pub(crate) tag: Option<LitInt>,
}

impl Variant {
    /// Get the discriminant expression for the variant.
    ///
    /// If the variant has a `tag` attribute, return it.
    /// Otherwise, return an integer literal with the given field index (the bincode default).
    pub(crate) fn discriminant(&self, field_index: usize) -> Cow<'_, LitInt> {
        self.tag
            .as_ref()
            .map(Cow::Borrowed)
            .unwrap_or_else(|| Cow::Owned(LitInt::new(&field_index.to_string(), self.ident.span())))
    }
}

pub(crate) trait VariantsExt {
    /// Generate the `TYPE_META` implementation for an enum.
    fn type_meta_impl(
        &self,
        trait_impl: TraitImpl,
        tag_encoding: &Type,
        crate_name: &Path,
    ) -> TokenStream;
}

impl VariantsExt for &[Variant] {
    fn type_meta_impl(
        &self,
        trait_impl: TraitImpl,
        tag_encoding: &Type,
        crate_name: &Path,
    ) -> TokenStream {
        if self.is_empty() {
            return quote! { #crate_name::TypeMeta::Static { size: 0, zero_copy: false } };
        }

        // Enums have a statically known size in a very specific case: all variants have the same serialized size.
        // This holds trivially for enums where all variants are unit enums (the size is just the size of the discriminant).
        // In other cases, we need to compute the size of each variant and check if they are all equal.
        // Otherwise, the enum is dynamic.
        //
        // Enums are never zero-copy, as the discriminant may have invalid bit patterns.
        let idents = anon_ident_iter(Some("variant_"))
            .take(self.len())
            .collect::<Vec<_>>();
        let tag_expr = match trait_impl {
            TraitImpl::SchemaRead => {
                quote! { <#tag_encoding as #crate_name::SchemaRead<'de, __WincodeConfig>>::TYPE_META }
            }
            TraitImpl::SchemaWrite => {
                quote! { <#tag_encoding as #crate_name::SchemaWrite<__WincodeConfig>>::TYPE_META }
            }
        };
        let variant_type_metas = self
            .iter()
            .zip(&idents)
            .map(|(variant, ident)| match variant.fields.style {
                Style::Struct | Style::Tuple => {
                    // Gather the `TYPE_META` implementations for each field of the variant.
                    let fields_type_meta_expansion = {
                        let items = variant.fields.unskipped_iter().map(|field| {
                            let target = field.target_fully_qualified(trait_impl);
                            quote! { #target::TYPE_META }
                        });
                        quote! { #(#items),* }
                    };
                    // Assign the `TYPE_META` to a local variant identifier (`#ident`).
                    quote! {
                        // Sum the discriminant size and the sizes of the fields. Enums are never zero-copy
                        let #ident = #crate_name::TypeMeta::join_types([#tag_expr, #fields_type_meta_expansion]).keep_zero_copy(false);
                    }
                }
                Style::Unit => {
                    // For unit enums, the `TypeMeta` is just the `TypeMeta` of the discriminant.
                    //
                    // We always override the zero-copy flag to `false`, due to discriminants having potentially
                    // invalid bit patterns.
                    quote! {
                        let #ident = match #tag_expr {
                            #crate_name::TypeMeta::Static { size, .. } => {
                                #crate_name::TypeMeta::Static { size, zero_copy: false }
                            }
                            #crate_name::TypeMeta::Dynamic => #crate_name::TypeMeta::Dynamic,
                        };
                    }
                }
            });

        quote! {
            const {
                // Declare the `TypeMeta` implementations for each variant.
                #(#variant_type_metas)*
                // Place the local bindings for the variant identifiers in an array for iteration.
                let variant_sizes = [#(#idents),*];

                /// Iterate over all the variant `TypeMeta`s and check if they are all `TypeMeta::Static`
                /// and have the same size.
                ///
                /// This logic is broken into a function so that we can use `return`.
                const fn choose(variant_sizes: &[#crate_name::TypeMeta]) -> #crate_name::TypeMeta {
                    // If there is only one variant, it's safe to use that variant's `TypeMeta`.
                    //
                    // Note we check if there are 0 variants at the top of this function and exit early.
                    if variant_sizes.len() == 1 {
                        return variant_sizes[0];
                    }
                    let mut i = 1;
                    // Can't use a `for` loop in a const context.
                    while i < variant_sizes.len() {
                        match (variant_sizes[i], variant_sizes[0]) {
                            // Iff every variant is `TypeMeta::Static` and has the same size, we can assume the type is static.
                            (#crate_name::TypeMeta::Static { size: s1, .. }, #crate_name::TypeMeta::Static { size: s2, .. }) if s1 == s2 => {
                                // Check the next variant.
                                i += 1;
                            }
                            _ => {
                                // If any variant is not `TypeMeta::Static` or has a different size, the enum is dynamic.
                                return #crate_name::TypeMeta::Dynamic;
                            }
                        }
                    }

                    // If we made it here, all variants are `TypeMeta::Static` and have the same size,
                    // so we can return the first one.
                    variant_sizes[0]
                }
                choose(&variant_sizes)
            }
        }
    }
}

pub(crate) type ImplBody = Data<Variant, Field>;

/// Get the path to `wincode` based on the `internal` or `crate_path` option.
pub(crate) fn get_crate_name(args: &SchemaArgs) -> Path {
    if let Some(crate_path) = &args.crate_path {
        crate_path.clone()
    } else if args.internal {
        parse_quote!(crate)
    } else {
        parse_quote!(::wincode)
    }
}

#[derive(FromDeriveInput)]
#[darling(attributes(wincode), forward_attrs, and_then = Self::validate)]
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
    /// Specifies the encoding to use for enum discriminants.
    ///
    /// If specified, the enum discriminants will be encoded using the given type's `SchemaWrite`
    /// and `SchemaRead` implementations.
    /// Otherwise, the enum discriminants will be encoded using the default encoding (`u32`).
    #[darling(default)]
    pub(crate) tag_encoding: Option<Type>,
    /// Indicates whether to assert that the type is zero-copy or not.
    ///
    /// If specified, compile-time asserts will be generated to ensure the type meets zero-copy requirements.
    ///
    /// Supports both flag-style and explicit path specification:
    /// - `#[wincode(assert_zero_copy)]` - uses default config
    /// - `#[wincode(assert_zero_copy(MyConfig))]` - uses custom config path
    /// - `#[wincode(assert_zero_copy(schema = "read"))]` - checks only read metadata
    #[darling(default)]
    pub(crate) assert_zero_copy: Option<AssertZeroCopyConfig>,
    /// Specifies the path to the `wincode` crate.
    ///
    /// Useful when `wincode` is renamed in `Cargo.toml` or re-exported from another module.
    /// The path is emitted as written and resolved from the derive expansion site.
    #[darling(rename = "crate", default)]
    pub(crate) crate_path: Option<Path>,
    #[darling(default)]
    pub(crate) context: Option<Type>,
}

impl SchemaArgs {
    /// Ensure any specified enum variant tags are unique.
    pub(crate) fn validate_variant_tags(&self) -> Result<()> {
        match &self.data {
            Data::Enum(variants) => {
                let mut seen = HashSet::new();

                for (idx, variant) in variants.iter().enumerate() {
                    let (tag, span) = match &variant.tag {
                        Some(tag) => (
                            tag.base10_parse::<u128>().map_err(darling::Error::from)?,
                            tag.span(),
                        ),
                        None => (idx as u128, variant.ident.span()),
                    };
                    if !seen.insert(tag) {
                        return Err(darling::Error::custom(format!(
                            "duplicate enum discriminant {tag}"
                        ))
                        .with_span(&span));
                    }
                }

                Ok(())
            }
            Data::Struct(_) => Ok(()),
        }
    }

    /// Populate fields with derive-level metadata used during code generation.
    ///
    /// This stores the resolved crate path on every field and, for fields marked
    /// `#[wincode(context)]`, validates and caches the top-level context type and
    /// its lifetimes. Keeping this metadata on [`Field`] lets its helper methods
    /// generate bounds and fully qualified paths without threading the same
    /// arguments through every caller.
    fn populate_field_metadata(&mut self) -> Result<()> {
        fn resolve(
            field: &mut Field,
            context: Option<(&Type, &Rc<[Lifetime]>)>,
            crate_name: &Path,
        ) -> Result<()> {
            field.crate_name = Some(crate_name.clone());

            if !field.context_flag.is_present() {
                return Ok(());
            }

            let (context, context_lifetimes) = context.ok_or_else(|| {
                darling::Error::custom(
                    "`#[wincode(context)]` requires a top-level `context = \"...\"`",
                )
                .with_span(&field.context_flag.span())
            })?;

            field.context = Some(context.clone());
            field.context_lifetimes = context_lifetimes.clone();
            Ok(())
        }

        let crate_name = get_crate_name(self);
        let context_ty = self.context.as_ref();
        let context_lifetimes = context_ty.map(|c| Rc::from(c.lifetimes()));
        let context = context_ty.zip(context_lifetimes.as_ref());

        match &mut self.data {
            Data::Struct(fields) => {
                for field in &mut fields.fields {
                    resolve(field, context, &crate_name)?;
                }
            }
            Data::Enum(variants) => {
                for variant in variants {
                    for field in &mut variant.fields.fields {
                        resolve(field, context, &crate_name)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn validate(mut self) -> Result<Self> {
        self.validate_variant_tags()?;
        self.populate_field_metadata()?;
        Ok(self)
    }
}

/// Configuration for zero-copy assertions.
///
/// This type enables optional path specification for `assert_zero_copy`:
/// - `#[wincode(assert_zero_copy)]` - flag style, uses default config (`None` inner value)
/// - `#[wincode(assert_zero_copy(MyConfig))]` - explicit path
/// - `#[wincode(assert_zero_copy(schema = "read"))]` - read metadata only
#[derive(Debug, Clone)]
pub(crate) struct AssertZeroCopyConfig {
    pub(crate) config: Option<Path>,
    pub(crate) schema: ZeroCopySchema,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ZeroCopySchema {
    Read,
    Write,
    Both,
}

impl ZeroCopySchema {
    pub(crate) fn includes(self, trait_impl: TraitImpl) -> bool {
        matches!(
            (self, trait_impl),
            (Self::Both, _)
                | (Self::Read, TraitImpl::SchemaRead)
                | (Self::Write, TraitImpl::SchemaWrite)
        )
    }
}

impl FromMeta for AssertZeroCopyConfig {
    fn from_word() -> darling::Result<Self> {
        // #[wincode(assert_zero_copy)] - use default config
        Ok(AssertZeroCopyConfig {
            config: None,
            schema: ZeroCopySchema::Both,
        })
    }

    fn from_list(items: &[NestedMeta]) -> darling::Result<Self> {
        let mut config = None;
        let mut schema = ZeroCopySchema::Both;
        let mut schema_seen = false;

        for item in items {
            match item {
                NestedMeta::Meta(syn::Meta::Path(path)) if config.is_none() => {
                    config = Some(path.clone());
                }
                NestedMeta::Meta(syn::Meta::NameValue(value)) if value.path.is_ident("config") => {
                    let Expr::Path(path) = &value.value else {
                        return Err(darling::Error::unexpected_type("path"));
                    };
                    if config.replace(path.path.clone()).is_some() {
                        return Err(darling::Error::duplicate_field("config"));
                    }
                }
                NestedMeta::Meta(syn::Meta::NameValue(value)) if value.path.is_ident("schema") => {
                    if schema_seen {
                        return Err(darling::Error::duplicate_field("schema"));
                    }
                    schema_seen = true;
                    let Expr::Lit(expr) = &value.value else {
                        return Err(darling::Error::unexpected_type("string"));
                    };
                    let Lit::Str(value) = &expr.lit else {
                        return Err(darling::Error::unexpected_type("string"));
                    };
                    schema = match value.value().as_str() {
                        "read" => ZeroCopySchema::Read,
                        "write" => ZeroCopySchema::Write,
                        "both" => ZeroCopySchema::Both,
                        _ => {
                            return Err(darling::Error::custom(format!(
                                "unknown schema `{}`; expected `read`, `write`, or `both`",
                                value.value()
                            )));
                        }
                    };
                }
                _ => return Err(darling::Error::unexpected_type("path or named option")),
            }
        }

        Ok(AssertZeroCopyConfig { config, schema })
    }
}

/// The default encoding to use for enum discriminants.
///
/// Bincode's default discriminant encoding is `u32`.
///
/// Note in the public APIs we refer to `tag` to mean the discriminant encoding
/// for friendlier naming.
#[inline]
pub(crate) fn default_tag_encoding() -> Type {
    parse_quote!(__WincodeConfig::TagEncoding)
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
    pub(crate) fn is_zero_copy_eligible(&self) -> bool {
        matches!(self.layout, Layout::Transparent | Layout::C)
    }
}

/// Extract the `#[repr]` attribute from the derive input, returning an error if the type is packed (not supported).
pub(crate) fn extract_repr(input: &DeriveInput, trait_impl: &'static str) -> Result<StructRepr> {
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
impl GenericStack<'_> {
    fn new() -> Self {
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

impl VisitMut for InferGeneric<'_> {
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
struct ReplaceLifetimes<'a> {
    replacement: &'a str,
    exclude: &'a [Lifetime],
}

impl ReplaceLifetimes<'_> {
    /// Replace the lifetime with `'de`, preserving the span.
    fn replace(&self, t: &mut Lifetime) {
        // `'static` is a concrete outlives guarantee, not a borrow parameter.
        // Rewriting it to `'de` would allow data borrowed from the input buffer to be
        // written into fields whose type declares a static reference.
        if t.ident != "static" && !self.exclude.iter().any(|l| l.ident == t.ident) {
            t.ident = Ident::new(self.replacement, t.ident.span());
        }
    }

    fn new_from_reference(&self, t: &mut TypeReference) {
        t.lifetime = Some(Lifetime {
            apostrophe: t.and_token.span(),
            ident: Ident::new(self.replacement, t.and_token.span()),
        })
    }
}

impl VisitMut for ReplaceLifetimes<'_> {
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

struct HasLifetime(bool);

impl Visit<'_> for HasLifetime {
    fn visit_lifetime(&mut self, _: &Lifetime) {
        self.0 = true;
    }
}

struct ContainsLifetime<'a> {
    lifetime: &'a Lifetime,
    found: bool,
}

impl Visit<'_> for ContainsLifetime<'_> {
    fn visit_lifetime(&mut self, candidate: &Lifetime) {
        self.found |= candidate.ident == self.lifetime.ident;
    }
}

struct Lifetimes(Vec<Lifetime>);

impl Visit<'_> for Lifetimes {
    fn visit_lifetime(&mut self, lt: &Lifetime) {
        self.0.push(lt.clone());
    }
}

struct HasTypeParam<'a> {
    type_params: &'a HashSet<&'a Ident>,
    found: bool,
}

impl Visit<'_> for HasTypeParam<'_> {
    fn visit_ident(&mut self, i: &Ident) {
        if self.type_params.contains(i) {
            self.found = true;
        }
    }
}

/// Find fields whose types mention a generic type parameter of the derived type.
///
/// ```ignore
/// struct Wrapper<T> {
///     #[wincode(with = "containers::Vec<_, BincodeLen>")]
///     values: Vec<T>,
/// }
/// // target = containers::Vec<T, BincodeLen>
/// // ty     = Vec<T>
/// ```
///
/// When this happens, the generated code calls `SchemaRead`/`SchemaWrite` on the adapter type,
/// but the adapter's `Src`/`Dst` must match the real field type.
pub(crate) fn generic_field_types<'a>(
    data: &'a Data<Variant, Field>,
    generics: &Generics,
) -> Vec<&'a Field> {
    let type_params: HashSet<&Ident> = generics.type_params().map(|p| &p.ident).collect();
    if type_params.is_empty() {
        return Vec::new();
    }

    fn visit<'a>(
        fields: impl Iterator<Item = &'a Field>,
        type_params: &HashSet<&Ident>,
    ) -> Vec<&'a Field> {
        let mut seen = HashSet::new();
        let mut result = Vec::new();
        for field in fields {
            if field.skip.is_some() {
                continue;
            }
            let target = field.target_resolved();
            let mut visitor = HasTypeParam {
                type_params,
                found: false,
            };
            visitor.visit_type(&target);
            if visitor.found && seen.insert((target, &field.ty, &field.context)) {
                result.push(field);
            }
        }
        result
    }

    match data {
        Data::Struct(fields) => visit(fields.iter(), &type_params),
        Data::Enum(variants) => visit(variants.iter().flat_map(|v| v.fields.iter()), &type_params),
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
        assert_eq!(
            target.with_lifetime_excluding("de", &[]),
            parse_quote!(Foo<'de>)
        );

        let target: Type = parse_quote!(&'a str);
        assert_eq!(
            target.with_lifetime_excluding("de", &[]),
            parse_quote!(&'de str)
        );
    }

    #[test]
    fn lifetime_override_doesnt_clobber_static() {
        let target: Type = parse_quote!(Foo<'static>);
        assert_eq!(
            target.with_lifetime_excluding("de", &[]),
            parse_quote!(Foo<'static>)
        );

        let target: Type = parse_quote!(&'static str);
        assert_eq!(
            target.with_lifetime_excluding("de", &[]),
            parse_quote!(&'static str)
        );

        let target: Type = parse_quote!(Option<&'static str>);
        assert_eq!(
            target.with_lifetime_excluding("de", &[]),
            parse_quote!(Option<&'static str>)
        );
    }

    #[test]
    fn lifetime_override_preserves_excluded_lifetimes() {
        let target: Type = parse_quote!(Foo<'ctx, &'input str, &'ctx str, &'static str, &str>);
        let exclude = [parse_quote!('ctx)];

        assert_eq!(
            target.with_lifetime_excluding("de", &exclude),
            parse_quote!(Foo<'ctx, &'de str, &'ctx str, &'static str, &'de str>)
        );
    }

    #[test]
    fn test_anon_ident_iter() {
        let mut iter = anon_ident_iter(None);
        assert_eq!(iter.next().unwrap().to_string(), "a");
        assert_eq!(iter.nth(25).unwrap().to_string(), "a0");
        assert_eq!(iter.next().unwrap().to_string(), "b0");
        assert_eq!(iter.nth(24).unwrap().to_string(), "a1");
    }

    #[test]
    fn test_has_lifetime() {
        let ty: Type = parse_quote!(&'a Foo);
        assert!(ty.has_lifetime());

        let ty: Type = parse_quote!(Foo<'b, 'c>);
        assert!(ty.has_lifetime());
    }

    #[test]
    fn test_contains_lifetime() {
        let ty: Type = parse_quote!(Foo<'a, Option<&'b str>, &'static str>);

        assert!(ty.contains_lifetime(&parse_quote!('a)));
        assert!(ty.contains_lifetime(&parse_quote!('b)));
        assert!(ty.contains_lifetime(&parse_quote!('static)));
        assert!(!ty.contains_lifetime(&parse_quote!('c)));
    }

    #[test]
    fn assert_zero_copy_options_preserve_positional_config() {
        let meta = parse_quote!(assert_zero_copy(MyConfig, schema = "read"));
        let config = AssertZeroCopyConfig::from_meta(&meta).unwrap();

        assert_eq!(config.config, Some(parse_quote!(MyConfig)));
        assert_eq!(config.schema, ZeroCopySchema::Read);
        assert!(config.schema.includes(TraitImpl::SchemaRead));
        assert!(!config.schema.includes(TraitImpl::SchemaWrite));
    }

    #[test]
    fn assert_zero_copy_options_accept_named_config() {
        let meta = parse_quote!(assert_zero_copy(config = custom::Config, schema = "write"));
        let config = AssertZeroCopyConfig::from_meta(&meta).unwrap();

        assert_eq!(config.config, Some(parse_quote!(custom::Config)));
        assert_eq!(config.schema, ZeroCopySchema::Write);
    }

    #[test]
    fn assert_zero_copy_options_default_to_both() {
        let config = AssertZeroCopyConfig::from_meta(&parse_quote!(assert_zero_copy)).unwrap();

        assert_eq!(config.config, None);
        assert_eq!(config.schema, ZeroCopySchema::Both);
        assert!(config.schema.includes(TraitImpl::SchemaRead));
        assert!(config.schema.includes(TraitImpl::SchemaWrite));
    }
}
