//! Global configuration for wincode.
//!
//! This module provides configuration types and structs for configuring wincode's behavior.
//! See [`ConfigBuilder`] for more details on how to configure wincode.
//!
//! Additionally, this module provides traits and functions that mirror the serialization,
//! deserialization, and zero-copy traits and functions from the crate root, but with an
//! additional configuration parameter.
use {
    crate::len::{BincodeLen, SeqLen},
    core::marker::PhantomData,
};

pub const DEFAULT_PREALLOCATION_SIZE_LIMIT: usize = 4 << 20; // 4 MiB
pub const PREALLOCATION_SIZE_LIMIT_DISABLED: usize = usize::MAX;

/// Builder to configure global settings.
///
/// Defaults:
/// - Zero-copy alignment check is enabled.
/// - Preallocation size limit is 4 MiB.
/// - Length encoding is [`BincodeLen`].
pub struct ConfigBuilder<
    const ZERO_COPY_ALIGN_CHECK: bool = true,
    const PREALLOCATION_SIZE_LIMIT: usize = DEFAULT_PREALLOCATION_SIZE_LIMIT,
    LengthEncoding = BincodeLen,
> {
    _l: PhantomData<LengthEncoding>,
}

impl<const ZERO_COPY_ALIGN_CHECK: bool, const PREALLOCATION_SIZE_LIMIT: usize, LengthEncoding> Clone
    for ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<const ZERO_COPY_ALIGN_CHECK: bool, const PREALLOCATION_SIZE_LIMIT: usize, LengthEncoding> Copy
    for ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding>
{
}

const fn generate<
    const ZERO_COPY_ALIGN_CHECK: bool,
    const PREALLOCATION_SIZE_LIMIT: usize,
    LengthEncoding,
>() -> ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding> {
    ConfigBuilder { _l: PhantomData }
}

impl ConfigBuilder {
    /// Create a new config builder with the default settings.
    ///
    /// Defaults:
    /// - Zero-copy alignment check is enabled.
    /// - Preallocation size limit is 4 MiB.
    /// - Length encoding is [`BincodeLen`].
    pub const fn default() -> DefaultConfig {
        generate()
    }
}

pub type DefaultConfig = ConfigBuilder;

impl<const ZERO_COPY_ALIGN_CHECK: bool, const PREALLOCATION_SIZE_LIMIT: usize, LengthEncoding>
    ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding>
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
    ) -> ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, L>
    where
        ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, L>: Config,
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
    ) -> ConfigBuilder<true, PREALLOCATION_SIZE_LIMIT, LengthEncoding> {
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
    ) -> ConfigBuilder<false, PREALLOCATION_SIZE_LIMIT, LengthEncoding> {
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
    ) -> ConfigBuilder<ZERO_COPY_ALIGN_CHECK, LIMIT, LengthEncoding> {
        generate()
    }

    /// Disable the preallocation size limit.
    ///
    /// <div class="warning">Warning: only do this if you absolutely trust your input.</div>
    pub const fn disable_preallocation_size_limit(
        self,
    ) -> ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT_DISABLED, LengthEncoding>
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
}

impl<
        const ZERO_COPY_ALIGN_CHECK: bool,
        const PREALLOCATION_SIZE_LIMIT: usize,
        LengthEncoding: 'static,
    > ConfigCore
    for ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding>
{
    const PREALLOCATION_SIZE_LIMIT: Option<usize> =
        if PREALLOCATION_SIZE_LIMIT == PREALLOCATION_SIZE_LIMIT_DISABLED {
            None
        } else {
            Some(PREALLOCATION_SIZE_LIMIT)
        };
    const ZERO_COPY_ALIGN_CHECK: bool = ZERO_COPY_ALIGN_CHECK;
}

/// Trait for configuration access when you need access to type parameters that depend on [`Config`]
/// (e.g., [`Config::LengthEncoding`]).
///
/// Prefer [`ConfigCore`] when you don't need those configuration type parameters that depend
/// on [`Config`] (e.g., primitive types).
pub trait Config: ConfigCore {
    type LengthEncoding: SeqLen<Self> + 'static;
}

impl<
        const ZERO_COPY_ALIGN_CHECK: bool,
        const PREALLOCATION_SIZE_LIMIT: usize,
        LengthEncoding: 'static,
    > Config for ConfigBuilder<ZERO_COPY_ALIGN_CHECK, PREALLOCATION_SIZE_LIMIT, LengthEncoding>
where
    LengthEncoding: SeqLen<Self>,
{
    type LengthEncoding = LengthEncoding;
}

mod serde;
pub use serde::*;
