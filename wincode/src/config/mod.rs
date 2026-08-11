//! Global configuration for wincode.
//!
//! This module provides configuration types and structs for configuring wincode's behavior.
//! See [`Configuration`] for more details on how to configure wincode.
//!
//! Additionally, this module provides traits and functions that mirror the serialization,
//! deserialization, and zero-copy traits and functions from the crate root, but with an
//! additional configuration parameter.
//!
//! # Deserialization size limits
//!
//! A limit set with [`Configuration::with_deserialization_size_limit`] is enforced by all
//! high-level deserialization entrypoints in this module.
//!
//! The limit is not enforced merely by using the configuration type in a direct call to
//! [`SchemaRead::get`](crate::SchemaRead::get) or [`SchemaRead::read`](crate::SchemaRead::read).
//! Code that calls [`SchemaRead`](crate::SchemaRead) directly must wrap its reader once at the
//! outermost deserialization boundary in [`LimitReader`](crate::io::LimitReader) and pass or
//! reborrow that same reader throughout the operation. Constructing a fresh wrapper in each
//! nested schema call resets the limit for each wrapper rather than enforcing one cumulative limit.
use {
    crate::{
        int_encoding::{BigEndian, ByteOrder, FixInt, IntEncoding, LittleEndian, VarInt},
        len::{BincodeLen, SeqLen},
        tag_encoding::TagEncoding,
    },
    core::marker::PhantomData,
};

pub const DEFAULT_PREALLOCATION_SIZE_LIMIT: usize = 4 << 20; // 4 MiB
pub const PREALLOCATION_SIZE_LIMIT_DISABLED: usize = usize::MAX;
pub const DEFAULT_DESERIALIZATION_SIZE_LIMIT: usize = DESERIALIZATION_SIZE_LIMIT_DISABLED;
pub const DESERIALIZATION_SIZE_LIMIT_DISABLED: usize = usize::MAX;

/// Compile-time configuration for runtime behavior.
///
/// Defaults:
/// - Zero-copy alignment check is enabled.
/// - Preallocation size limit is 4 MiB.
/// - Length encoding is [`BincodeLen`].
/// - Byte order is [`LittleEndian`].
/// - Integer encoding is [`FixInt`].
/// - Tag encoding is [`u32`].
/// - Deserialization size limiting is disabled.
pub struct Configuration<
    const ZERO_COPY_ALIGN_CHECK: bool = true,
    const PREALLOCATION_SIZE_LIMIT: usize = DEFAULT_PREALLOCATION_SIZE_LIMIT,
    LengthEncoding = BincodeLen,
    ByteOrder = LittleEndian,
    IntEncoding = FixInt,
    TagEncoding = u32,
    const DESERIALIZATION_SIZE_LIMIT: usize = DEFAULT_DESERIALIZATION_SIZE_LIMIT,
> {
    _l: PhantomData<LengthEncoding>,
    _b: PhantomData<ByteOrder>,
    _i: PhantomData<IntEncoding>,
    _t: PhantomData<TagEncoding>,
}

impl<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding,
    ByteOrder,
    IntEncoding,
    TagEncoding,
> Clone
    for Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding,
    ByteOrder,
    IntEncoding,
    TagEncoding,
> Copy
    for Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
{
}

const fn generate<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding,
    ByteOrder,
    IntEncoding,
    TagEncoding,
>() -> Configuration<
    ZERO_COPY_ALIGN_CHECK,
    PREALLOCATION_SIZE_LIMIT,
    LengthEncoding,
    ByteOrder,
    IntEncoding,
    TagEncoding,
    DESERIALIZATION_SIZE_LIMIT,
> {
    Configuration {
        _l: PhantomData,
        _b: PhantomData,
        _i: PhantomData,
        _t: PhantomData,
    }
}

impl Configuration {
    /// Create a new configuration with the default settings.
    ///
    /// Defaults:
    /// - Zero-copy alignment check is enabled.
    /// - Preallocation size limit is 4 MiB.
    /// - Length encoding is [`BincodeLen`].
    /// - Byte order is [`LittleEndian`].
    /// - Integer encoding is [`FixInt`].
    /// - Deserialization size limit is disabled.
    pub const fn default() -> DefaultConfig {
        generate()
    }
}

pub type DefaultConfig = Configuration;

impl<
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding,
    ByteOrder,
    IntEncoding,
    TagEncoding,
>
    Configuration<
        true,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
{
    // This impl is deliberately bounded to `ZERO_COPY_ALIGN_CHECK == true` rather than
    // being generic over it.
    //
    // If `new` were available for `false`, safe code could write
    // `Configuration::<false>::new()` to obtain an alignment-check-disabled config,
    // bypassing the `unsafe disable_zero_copy_align_check` gate.
    #[expect(clippy::new_without_default)]
    pub const fn new() -> Self {
        generate()
    }
}

impl<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding,
    ByteOrder,
    IntEncoding,
    TagEncoding,
>
    Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
{
    /// Use the given [`SeqLen`] implementation for sequence length encoding.
    ///
    /// Default is [`BincodeLen`].
    ///
    /// Note that this default can be overridden for individual cases by using
    /// [`containers`](crate::containers).
    pub const fn with_length_encoding<L>(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        L,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
    where
        Configuration<
            ZERO_COPY_ALIGN_CHECK,
            PREALLOCATION_SIZE_LIMIT,
            L,
            ByteOrder,
            IntEncoding,
            TagEncoding,
            DESERIALIZATION_SIZE_LIMIT,
        >: Config,
    {
        generate()
    }

    /// Use big-endian byte order.
    ///
    /// Note that changing the byte order will have a direct impact on zero-copy eligibility.
    /// Integers are only eligible for zero-copy when configured byte order matches the native byte order.
    ///
    /// Default is [`LittleEndian`].
    pub const fn with_big_endian(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        BigEndian,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use little-endian byte order.
    ///
    /// Default is [`LittleEndian`].
    pub const fn with_little_endian(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        LittleEndian,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use target platform byte order.
    ///
    /// Will use the native byte order of the target platform.
    #[cfg(target_endian = "little")]
    pub const fn with_platform_endian(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        LittleEndian,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use target platform byte order.
    ///
    /// Will use the native byte order of the target platform.
    #[cfg(target_endian = "big")]
    pub const fn with_platform_endian(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        BigEndian,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use [`FixInt`] for integer encoding.
    ///
    /// Default is [`FixInt`].
    pub const fn with_fixint_encoding(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        FixInt,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use [`VarInt`] for integer encoding.
    ///
    /// Default is [`FixInt`].
    ///
    /// Performance note: variable length integer encoding will hurt serialization and deserialization
    /// performance significantly relative to fixed width integer encoding. Additionally, all zero-copy
    /// capabilities on integers will be lost. Variable length integer encoding may be beneficial if
    /// reducing the resulting size of serialized data is important, but if serialization / deserialization
    /// performance is important, fixed width integer encoding is highly recommended.
    pub const fn with_varint_encoding(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        VarInt,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use the given [`IntEncoding`] implementation for integer encoding.
    ///
    /// Can be used for custom, unofficial integer encodings.
    ///
    /// Default is [`FixInt`].
    pub const fn with_int_encoding<I>(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        I,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
    where
        Configuration<
            ZERO_COPY_ALIGN_CHECK,
            PREALLOCATION_SIZE_LIMIT,
            LengthEncoding,
            ByteOrder,
            I,
            TagEncoding,
            DESERIALIZATION_SIZE_LIMIT,
        >: Config,
    {
        generate()
    }

    /// Enable the zero-copy alignment check.
    ///
    /// If enabled, zero-copy deserialization will ensure that pointers are correctly aligned for the target type
    /// before creating references.
    /// You should keep this enabled unless you have a very specific use case for disabling it.
    ///
    /// This is enabled by default.
    pub const fn enable_zero_copy_align_check(
        self,
    ) -> Configuration<
        true,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Disable the zero-copy alignment check.
    ///
    /// When disabled, zero-copy deserialization (`&'de T` and `&'de [T]` for `T: ZeroCopy`)
    /// will not verify that pointers into the buffer are correctly aligned before forming
    /// references. Creating a misaligned reference is **undefined behavior**.
    ///
    /// # Safety
    ///
    /// You must guarantee every zero-copy reference is correctly aligned for its type.
    ///
    /// This holds when:
    /// - The buffer is aligned to at least `align_of::<T>()` for each zero-copy type `T`,
    ///   and each zero-copy read occurs at an offset that preserves that alignment.
    /// - Or you only deserialize types with alignment 1 (e.g., `&[u8]`, `&[u8; N]`, `&str`, etc).
    ///
    /// Only disable this when you control the serialized layout and can enforce
    /// alignment; owned deserialization paths are unaffected.
    pub const unsafe fn disable_zero_copy_align_check(
        self,
    ) -> Configuration<
        false,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Set the preallocation size limit in bytes.
    ///
    /// wincode will preallocate all sequences up to this limit, or error
    /// if the size of the allocation would exceed this limit.
    /// This is used to prevent malicious data from causing
    /// excessive memory usage or OOM.
    ///
    /// The default limit is 4 MiB.
    pub const fn with_preallocation_size_limit<const LIMIT: usize>(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Disable the preallocation size limit.
    ///
    /// <div class="warning">Warning: only do this if you absolutely trust your input.</div>
    pub const fn disable_preallocation_size_limit(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT_DISABLED,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    > {
        generate()
    }

    /// Use the given [`TagEncoding`] implementation for enum discriminant encoding.
    ///
    /// Default is [`u32`].
    ///
    /// This can be overriden for individual cases with the `#[wincode(tag_encoding = ...)]`
    /// attribute.
    pub const fn with_tag_encoding<T>(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        T,
        DESERIALIZATION_SIZE_LIMIT,
    >
    where
        Configuration<
            ZERO_COPY_ALIGN_CHECK,
            PREALLOCATION_SIZE_LIMIT,
            LengthEncoding,
            ByteOrder,
            IntEncoding,
            T,
            DESERIALIZATION_SIZE_LIMIT,
        >: Config,
    {
        generate()
    }

    /// Set the maximum number of bytes that may be read by a deserialization operation.
    ///
    /// The limit is cumulative across all reads performed while deserializing a value. If an
    /// operation would exceed the remaining limit, it returns
    /// [`ReadError::ReadSizeLimit`](crate::io::ReadError::ReadSizeLimit). Trusted reader windows
    /// reserve their entire window against the limit.
    ///
    /// This is independent of the preallocation size limit. The deserialization size limit is
    /// disabled by default.
    ///
    /// The limit is enforced by the high-level deserialization entrypoints in [`config`](self),
    /// not by direct calls to [`SchemaRead::get`](crate::SchemaRead::get) or
    /// [`SchemaRead::read`](crate::SchemaRead::read). When using [`SchemaRead`](crate::SchemaRead)
    /// directly, wrap the reader in [`LimitReader`](crate::io::LimitReader) if you need this
    /// behavior.
    pub const fn with_deserialization_size_limit<const LIMIT: usize>(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        LIMIT,
    > {
        generate()
    }

    /// Disable the deserialization size limit.
    ///
    /// This is the default.
    ///
    /// This does not change the preallocation size limit.
    pub const fn disable_deserialization_size_limit(
        self,
    ) -> Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        ByteOrder,
        IntEncoding,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT_DISABLED,
    > {
        generate()
    }
}

/// Trait for accessing configuration values when only the constant knobs are needed
/// (e.g., `PREALLOCATION_SIZE_LIMIT`, `ZERO_COPY_ALIGN_CHECK`, `DESERIALIZATION_SIZE_LIMIT`).
///
/// Split from [`Config`] to avoid dependency cycles that can overflow the compiler stack,
/// such as [`SeqLen`] -> [`Config`] -> [`SeqLen`].
///
/// Prefer this trait over [`Config`] when you don't need configuration type parameters
/// that themselves depend on [`Config`] (e.g., [`SeqLen`], which depends on [`ConfigCore`]).
pub trait ConfigCore: 'static + Sized {
    const PREALLOCATION_SIZE_LIMIT: Option<usize>;
    const ZERO_COPY_ALIGN_CHECK: bool;
    /// Maximum number of bytes reserved for reads during one deserialization operation.
    ///
    /// A value of `None` disables the limit. This policy is consumed by the high-level
    /// deserialization entrypoints in [`config`](self); it does not automatically affect direct
    /// calls to [`SchemaRead`](crate::SchemaRead).
    const DESERIALIZATION_SIZE_LIMIT: Option<usize> = None;

    type ByteOrder: ByteOrder;
    type IntEncoding: IntEncoding<Self::ByteOrder>;
}

impl<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding: 'static,
    B,
    I,
    TagEncoding: 'static,
> ConfigCore
    for Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        B,
        I,
        TagEncoding,
        DESERIALIZATION_SIZE_LIMIT,
    >
where
    B: ByteOrder,
    I: IntEncoding<B>,
{
    const PREALLOCATION_SIZE_LIMIT: Option<usize> =
        if PREALLOCATION_SIZE_LIMIT == PREALLOCATION_SIZE_LIMIT_DISABLED {
            None
        } else {
            Some(PREALLOCATION_SIZE_LIMIT)
        };
    const ZERO_COPY_ALIGN_CHECK: bool = ZERO_COPY_ALIGN_CHECK;
    const DESERIALIZATION_SIZE_LIMIT: Option<usize> =
        if DESERIALIZATION_SIZE_LIMIT == DESERIALIZATION_SIZE_LIMIT_DISABLED {
            None
        } else {
            Some(DESERIALIZATION_SIZE_LIMIT)
        };

    type ByteOrder = B;
    type IntEncoding = I;
}

/// Trait for configuration access when you need access to type parameters that depend on [`Config`]
/// (e.g., [`Config::LengthEncoding`]).
///
/// Prefer [`ConfigCore`] when you don't need those configuration type parameters that depend
/// on [`Config`] (e.g., primitive types).
pub trait Config: ConfigCore {
    type LengthEncoding: SeqLen<Self> + 'static;
    type TagEncoding: TagEncoding<Self> + 'static;
}

impl<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    const DESERIALIZATION_SIZE_LIMIT: usize,
    LengthEncoding: 'static,
    B,
    I,
    T,
> Config
    for Configuration<
        ZERO_COPY_ALIGN_CHECK,
        PREALLOCATION_SIZE_LIMIT,
        LengthEncoding,
        B,
        I,
        T,
        DESERIALIZATION_SIZE_LIMIT,
    >
where
    LengthEncoding: SeqLen<Self>,
    T: TagEncoding<Self>,
    B: ByteOrder,
    I: IntEncoding<B>,
{
    type LengthEncoding = LengthEncoding;
    type TagEncoding = T;
}

mod serde;
pub use serde::*;
