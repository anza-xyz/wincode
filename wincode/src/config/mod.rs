//! Global configuration for wincode.
//!
//! This module provides configuration types and structs for configuring wincode's behavior.
//! See [`Configuration`] for more details on how to configure wincode.
//!
//! Additionally, this module provides traits and functions that mirror the serialization,
//! deserialization, and zero-copy traits and functions from the crate root, but with an
//! additional configuration parameter.
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

/// Compile-time configuration for runtime behavior.
///
/// Defaults:
/// - Zero-copy alignment check is enabled.
/// - Preallocation size limit is 4 MiB.
/// - Length encoding is [`BincodeLen`].
/// - Byte order is [`LittleEndian`].
/// - Integer encoding is [`FixInt`].
/// - Tag encoding is [`u32`].
pub struct Configuration<
    const ZERO_COPY_ALIGN_CHECK: bool = true,
    const PREALLOCATION_SIZE_LIMIT: usize = DEFAULT_PREALLOCATION_SIZE_LIMIT,
    LengthEncoding = BincodeLen,
    ByteOrder = LittleEndian,
    IntEncoding = FixInt,
    TagEncoding = u32,
> {
    _l: PhantomData<LengthEncoding>,
    _b: PhantomData<ByteOrder>,
    _i: PhantomData<IntEncoding>,
    _t: PhantomData<TagEncoding>,
}

impl<
        const ZERO_COPY_ALIGN_CHECK: bool,
        const PREALLOCATION_SIZE_LIMIT: usize,
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
    >
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<
        const ZERO_COPY_ALIGN_CHECK: bool,
        const PREALLOCATION_SIZE_LIMIT: usize,
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
    >
{
}

const fn generate<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
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
    pub const fn default() -> DefaultConfig {
        generate()
    }
}

pub type DefaultConfig = Configuration;

impl<
        const ZERO_COPY_ALIGN_CHECK: bool,
        const PREALLOCATION_SIZE_LIMIT: usize,
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
    >
{
    #[expect(clippy::new_without_default)]
    pub const fn new() -> Self {
        generate()
    }

    /// Use the given [`SeqLen`] implementation for sequence length encoding.
    ///
    /// Default is [`BincodeLen`].
    ///
    /// Note that this default can be overridden for individual cases by using
    /// [`containers`](crate::containers).
    pub const fn with_length_encoding<L>(
        self,
    ) -> Configuration<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, L, ByteOrder, IntEncoding>
    where
        Configuration<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, L>: Config,
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
    ) -> Configuration<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding, ByteOrder, I>
    where
        Configuration<
            ZERO_COPY_ALIGN_CHECK,
            PREALLOCATION_SIZE_LIMIT,
            LengthEncoding,
            ByteOrder,
            I,
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
    ) -> Configuration<true, PREALLOCATION_SIZE_LIMIT, LengthEncoding, ByteOrder, IntEncoding> {
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
    ) -> Configuration<false, PREALLOCATION_SIZE_LIMIT, LengthEncoding, ByteOrder, IntEncoding>
    {
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
    ) -> Configuration<ZERO_COPY_ALIGN_CHECK, LIMIT, LengthEncoding, ByteOrder, IntEncoding> {
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
    >
    where
        Configuration<
            ZERO_COPY_ALIGN_CHECK,
            PREALLOCATION_SIZE_LIMIT,
            LengthEncoding,
            ByteOrder,
            IntEncoding,
            T,
        >: Config,
    {
        generate()
    }
}

/// Trait for accessing configuration values when only the constant knobs are needed
/// (e.g., `PREALLOCATION_SIZE_LIMIT`, `ZERO_COPY_ALIGN_CHECK`).
///
/// Split from [`Config`] to avoid dependency cycles that can overflow the compiler stack,
/// such as [`SeqLen`] -> [`Config`] -> [`SeqLen`].
///
/// Prefer this trait over [`Config`] when you don't need configuration type parameters
/// that themselves depend on [`Config`] (e.g., [`SeqLen`], which depends on [`ConfigCore`]).
pub trait ConfigCore: 'static + Sized {
    const PREALLOCATION_SIZE_LIMIT: Option<usize>;
    const ZERO_COPY_ALIGN_CHECK: bool;
    type ByteOrder: ByteOrder;
    type IntEncoding: IntEncoding<Self::ByteOrder>;
}

impl<
        const ZERO_COPY_ALIGN_CHECK: bool,
        const PREALLOCATION_SIZE_LIMIT: usize,
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
        LengthEncoding: 'static,
        B,
        I,
        T,
    > Config
    for Configuration<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding, B, I, T>
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
