//! Schema traits.
//!
//! # Example
//!
//! ```
//! # #[cfg(all(feature = "solana-short-vec", feature = "alloc"))] {
//! # use rand::prelude::*;
//! # use wincode::{Serialize, Deserialize, len::{BincodeFixInt, ShortU16Len}, containers::{self, Pod}};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # use std::array;
//!
//! # #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
//! #[repr(transparent)]
//! #[derive(Clone, Copy)]
//! struct Signature([u8; 32]);
//! # #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
//! #[repr(transparent)]
//! #[derive(Clone, Copy)]
//! struct Address([u8; 32]);
//!
//! # #[derive(SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
//! struct MyStruct {
//!     #[wincode(with = "containers::Vec<Pod<_>, BincodeFixInt>")]
//!     signature: Vec<Signature>,
//!     #[serde(with = "solana_short_vec")]
//!     #[wincode(with = "containers::Vec<Pod<_>, ShortU16Len>")]
//!     address: Vec<Address>,
//! }
//!
//! let my_struct = MyStruct {
//!     signature: (0..10).map(|_| Signature(array::from_fn(|_| random()))).collect(),
//!     address: (0..10).map(|_| Address(array::from_fn(|_| random()))).collect(),
//! };
//! let bincode_serialized = bincode::serialize(&my_struct).unwrap();
//! let wincode_serialized = wincode::serialize(&my_struct).unwrap();
//! assert_eq!(bincode_serialized, wincode_serialized);
//!
//! let bincode_deserialized: MyStruct = bincode::deserialize(&bincode_serialized).unwrap();
//! let wincode_deserialized: MyStruct = wincode::deserialize(&wincode_serialized).unwrap();
//! assert_eq!(bincode_deserialized, wincode_deserialized);
//! # }
//! ```
use {
    crate::{
        config::{Config, ConfigCore, DefaultConfig},
        error::{ReadResult, WriteResult},
        io::*,
        len::SeqLen,
    },
    core::mem::MaybeUninit,
};

pub mod containers;
mod impls;

/// Indicates what kind of assumptions can be made when encoding or decoding a type.
///
/// Readers and writers may use this to optimize their behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeMeta {
    /// The type has a statically known serialized size.
    ///
    /// Specifying this variant can have significant performance benefits, as it can allow
    /// writers to prefetch larger chunks of memory such that subsequent read/write operations
    /// in those chunks can be performed at once without intermediate bounds checks.
    ///
    /// Specifying this variant incorrectly will almost certainly result in a panic at runtime.
    ///
    /// Take care not to specify this on variable length types, like `Vec` or `String`, as their
    /// serialized size will vary based on their length.
    Static {
        /// The static serialized size of the type.
        size: usize,
        /// Whether the type is eligible for zero-copy encoding/decoding.
        ///
        /// This indicates that the type has no invalid bit patterns, no layout requirements, no endianness
        /// checks, etc. This is a very strong claim that should be used judiciously.
        ///
        /// Specifying this incorrectly may trigger UB.
        zero_copy: bool,
    },
    /// The type has a dynamic size, and no optimizations can be made.
    Dynamic,
}

impl TypeMeta {
    #[inline(always)]
    pub(crate) const fn size_assert_zero_copy(self) -> usize {
        match self {
            TypeMeta::Static {
                size,
                zero_copy: true,
            } => size,
            _ => panic!("Type is not zero-copy"),
        }
    }
}

/// Types that can be written (serialized) to a [`Writer`].
pub trait SchemaWrite<C: ConfigCore> {
    type Src: ?Sized;

    const TYPE_META: TypeMeta = TypeMeta::Dynamic;

    /// Get the serialized size of `Self::Src`.
    fn size_of(src: &Self::Src) -> WriteResult<usize>;
    /// Write `Self::Src` to `writer`.
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()>;
}

/// Types that can be read (deserialized) from a [`Reader`].
pub trait SchemaRead<'de, C: ConfigCore> {
    type Dst;

    const TYPE_META: TypeMeta = TypeMeta::Dynamic;

    /// Read into `dst` from `reader`.
    ///
    /// # Safety
    ///
    /// - Implementation must properly initialize the `Self::Dst`.
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()>;

    /// Read `Self::Dst` from `reader` into a new `Self::Dst`.
    #[inline(always)]
    fn get(reader: &mut impl Reader<'de>) -> ReadResult<Self::Dst> {
        let mut value = MaybeUninit::uninit();
        Self::read(reader, &mut value)?;
        // SAFETY: `read` must properly initialize the `Self::Dst`.
        Ok(unsafe { value.assume_init() })
    }
}

/// Marker trait for types that can be deserialized via direct borrows from a [`Reader`].
///
/// <div class="warning">
/// You should not manually implement this trait for your own type unless you absolutely
/// know what you're doing. The derive macros will automatically implement this trait for your type
/// if it is eligible for zero-copy deserialization.
/// </div>
///
/// # Safety
///
/// - The type must not have any invalid bit patterns, no layout requirements, no endianness checks, etc.
pub unsafe trait ZeroCopy: 'static {
    /// Get a reference to a type from the given bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(all(feature = "alloc", feature = "derive"))] {
    /// # use wincode::{SchemaWrite, SchemaRead, ZeroCopy};
    /// # #[derive(Debug, PartialEq, Eq)]
    /// #[derive(SchemaWrite, SchemaRead)]
    /// #[repr(C)]
    /// struct Data {
    ///     bytes: [u8; 7],
    ///     the_answer: u8,
    /// }
    ///
    /// let data = Data { bytes: *b"wincode", the_answer: 42 };
    ///
    /// let serialized = wincode::serialize(&data).unwrap();
    /// let data_ref = Data::from_bytes(&serialized).unwrap();
    ///
    /// assert_eq!(data_ref, &data);
    /// # }
    /// ```
    #[inline(always)]
    fn from_bytes<'de>(mut bytes: &'de [u8]) -> ReadResult<&'de Self>
    where
        Self: SchemaRead<'de, DefaultConfig, Dst = Self> + Sized,
    {
        <&Self as SchemaRead<'de, DefaultConfig>>::get(&mut bytes)
    }

    /// Like [`ZeroCopy::from_bytes`], but allows the caller to provide a custom configuration.
    #[inline(always)]
    #[expect(unused_variables)]
    fn from_bytes_with_config<'de, C: Config>(
        mut bytes: &'de [u8],
        config: C,
    ) -> ReadResult<&'de Self>
    where
        Self: SchemaRead<'de, C, Dst = Self> + Sized,
    {
        <&Self as SchemaRead<'de, C>>::get(&mut bytes)
    }

    /// Get a mutable reference to a type from the given bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(all(feature = "alloc", feature = "derive"))] {
    /// # use wincode::{SchemaWrite, SchemaRead, ZeroCopy};
    /// # #[derive(Debug, PartialEq, Eq)]
    /// #[derive(SchemaWrite, SchemaRead)]
    /// #[repr(C)]
    /// struct Data {
    ///     bytes: [u8; 7],
    ///     the_answer: u8,
    /// }
    ///
    /// let data = Data { bytes: [0; 7], the_answer: 0 };
    ///
    /// let mut serialized = wincode::serialize(&data).unwrap();
    /// let data_mut = Data::from_bytes_mut(&mut serialized).unwrap();
    /// data_mut.bytes = *b"wincode";
    /// data_mut.the_answer = 42;
    ///
    /// let deserialized: Data = wincode::deserialize(&serialized).unwrap();
    /// assert_eq!(deserialized, Data { bytes: *b"wincode", the_answer: 42 });
    /// # }
    /// ```
    #[inline(always)]
    fn from_bytes_mut<'de>(mut bytes: &'de mut [u8]) -> ReadResult<&'de mut Self>
    where
        Self: SchemaRead<'de, DefaultConfig, Dst = Self> + Sized,
    {
        <&mut Self as SchemaRead<'de, DefaultConfig>>::get(&mut bytes)
    }

    /// Like [`ZeroCopy::from_bytes_mut`], but allows the caller to provide a custom configuration.
    #[inline(always)]
    #[expect(unused_variables)]
    fn from_bytes_mut_with_config<'de, C: Config>(
        mut bytes: &'de mut [u8],
        config: C,
    ) -> ReadResult<&'de mut Self>
    where
        Self: SchemaRead<'de, C, Dst = Self> + Sized,
    {
        <&mut Self as SchemaRead<'de, C>>::get(&mut bytes)
    }
}

/// A type that can be read (deserialized) from a [`Reader`] without borrowing from it.
pub trait SchemaReadOwned<C: ConfigCore>: for<'de> SchemaRead<'de, C> {}
impl<T, C: ConfigCore> SchemaReadOwned<C> for T where T: for<'de> SchemaRead<'de, C> {}

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
fn size_of_elem_iter<'a, T, Len, C>(
    value: impl ExactSizeIterator<Item = &'a T::Src>,
) -> WriteResult<usize>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C> + 'a,
{
    if let TypeMeta::Static { size, .. } = T::TYPE_META {
        return Ok(Len::write_bytes_needed(value.len())? + size * value.len());
    }
    // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
    Ok(Len::write_bytes_needed(value.len())?
        + (value
            .map(T::size_of)
            .try_fold(0usize, |acc, x| x.map(|x| acc + x))?))
}

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
/// Variant of [`size_of_elem_iter`] specialized for slices, which can opt into
/// an optimized implementation for bytes (`u8`s).
fn size_of_elem_slice<T, Len, C>(value: &[T::Src]) -> WriteResult<usize>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    size_of_elem_iter::<T, Len, C>(value.iter())
}

#[inline(always)]
fn write_elem_iter<'a, T, Len, C>(
    writer: &mut impl Writer,
    src: impl ExactSizeIterator<Item = &'a T::Src>,
) -> WriteResult<()>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C> + 'a,
{
    if let TypeMeta::Static { size, .. } = T::TYPE_META {
        #[allow(clippy::arithmetic_side_effects)]
        let needed = Len::write_bytes_needed(src.len())? + size * src.len();
        // SAFETY: `needed` is the size of the encoded length plus the size of the items.
        // `Len::write` and len writes of `T::Src` will write `needed` bytes,
        // fully initializing the trusted window.
        let mut writer = unsafe { writer.as_trusted_for(needed) }?;
        Len::write(&mut writer, src.len())?;
        for item in src {
            T::write(&mut writer, item)?;
        }
        writer.finish()?;
        return Ok(());
    }

    Len::write(writer, src.len())?;
    for item in src {
        T::write(writer, item)?;
    }
    Ok(())
}

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
/// Variant of [`write_elem_iter`] specialized for slices, which can opt into
/// an optimized implementation for bytes (`u8`s).
fn write_elem_slice<T, Len, C>(writer: &mut impl Writer, src: &[T::Src]) -> WriteResult<()>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    if let TypeMeta::Static {
        size,
        zero_copy: true,
    } = T::TYPE_META
    {
        let needed = Len::write_bytes_needed(src.len())? + src.len() * size;
        // SAFETY: `needed` is the size of the encoded length plus the size of the slice (bytes).
        // `Len::write` and `writer.write(src)` will write `needed` bytes,
        // fully initializing the trusted window.
        let writer = &mut unsafe { writer.as_trusted_for(needed) }?;
        Len::write(writer, src.len())?;
        // SAFETY: `T::Src` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        unsafe { writer.write_slice_t(src)? };
        writer.finish()?;
        return Ok(());
    }
    write_elem_iter::<T, Len, C>(writer, src.iter())
}

#[cfg(all(test, feature = "std", feature = "derive"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects, deprecated)]

    use {
        crate::{
            config::{self, Config, ConfigBuilder, DefaultConfig},
            containers::{self, Elem, Pod},
            deserialize, deserialize_mut,
            error::{self, invalid_tag_encoding},
            io::{Reader, Writer},
            len::FixInt,
            proptest_config::proptest_cfg,
            serialize, Deserialize, ReadResult, SchemaRead, SchemaWrite, Serialize, TypeMeta,
            WriteResult, ZeroCopy,
        },
        core::{marker::PhantomData, ptr},
        proptest::prelude::*,
        std::{
            cell::Cell,
            collections::{BinaryHeap, VecDeque},
            mem::MaybeUninit,
            ops::{Deref, DerefMut},
            rc::Rc,
            result::Result,
            sync::Arc,
        },
    };

    #[cfg(target_endian = "little")]
    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
        Clone,
        Copy,
    )]
    #[wincode(internal)]
    #[repr(C)]
    struct StructZeroCopy {
        a: u128,
        b: i128,
        c: u64,
        d: i64,
        e: u32,
        f: i32,
        ar1: [u8; 8],
        g: u16,
        h: i16,
        ar2: [u8; 12],
        i: u8,
        j: i8,
        ar3: [u8; 14],
    }

    #[cfg(not(target_endian = "little"))]
    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
        Clone,
        Copy,
    )]
    #[wincode(internal)]
    #[repr(C)]
    struct StructZeroCopy {
        byte: u8,
        ar: [u8; 32],
    }

    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
    )]
    #[wincode(internal)]
    struct StructStatic {
        a: u64,
        b: bool,
        e: [u8; 32],
    }

    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
    )]
    #[wincode(internal)]
    struct StructNonStatic {
        a: u64,
        b: bool,
        e: String,
    }

    #[test]
    fn struct_zero_copy_derive_size() {
        #[cfg(target_endian = "little")]
        let size = size_of::<u128>()
            + size_of::<i128>()
            + size_of::<u64>()
            + size_of::<i64>()
            + size_of::<u32>()
            + size_of::<i32>()
            + size_of::<[u8; 8]>()
            + size_of::<u16>()
            + size_of::<i16>()
            + size_of::<[u8; 12]>()
            + size_of::<u8>()
            + size_of::<i8>()
            + size_of::<[u8; 14]>();
        #[cfg(not(target_endian = "little"))]
        let size = size_of::<u8>() + size_of::<[u8; 32]>();
        let expected = TypeMeta::Static {
            size,
            zero_copy: true,
        };
        assert_eq!(
            <StructZeroCopy as SchemaWrite<DefaultConfig>>::TYPE_META,
            expected
        );
        assert_eq!(
            <StructZeroCopy as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            expected
        );
    }

    #[test]
    fn struct_zero_copy_transparent_derive_size() {
        #[derive(SchemaWrite, SchemaRead)]
        #[wincode(internal)]
        #[repr(transparent)]
        struct Address([u8; 32]);

        let expected = TypeMeta::Static {
            size: size_of::<[u8; 32]>(),
            zero_copy: true,
        };
        assert_eq!(<Address as SchemaWrite<DefaultConfig>>::TYPE_META, expected);
        assert_eq!(
            <Address as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            expected
        );
    }

    #[test]
    fn struct_static_derive_size() {
        let expected = TypeMeta::Static {
            size: size_of::<u64>() + size_of::<bool>() + size_of::<[u8; 32]>(),
            zero_copy: false,
        };
        assert_eq!(
            <StructStatic as SchemaWrite<DefaultConfig>>::TYPE_META,
            expected
        );
        assert_eq!(
            <StructStatic as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            expected
        );
    }

    #[test]
    fn struct_non_static_derive_size() {
        let expected = TypeMeta::Dynamic;
        assert_eq!(
            <StructNonStatic as SchemaWrite<DefaultConfig>>::TYPE_META,
            expected
        );
        assert_eq!(
            <StructNonStatic as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            expected
        );
    }

    thread_local! {
        /// TL counter for tracking drops (or lack thereof -- a leak).
        static TL_DROP_COUNT: Cell<isize> = const { Cell::new(0) };
    }

    fn get_tl_drop_count() -> isize {
        TL_DROP_COUNT.with(|cell| cell.get())
    }

    fn tl_drop_count_inc() {
        TL_DROP_COUNT.with(|cell| cell.set(cell.get() + 1));
    }

    fn tl_drop_count_dec() {
        TL_DROP_COUNT.with(|cell| cell.set(cell.get() - 1));
    }

    fn tl_drop_count_reset() {
        TL_DROP_COUNT.with(|cell| cell.set(0));
    }

    #[must_use]
    #[derive(Debug)]
    /// Guard for test set up that will ensure that the TL counter is 0 at the start and end of the test.
    struct TLDropGuard;

    impl TLDropGuard {
        fn new() -> Self {
            assert_eq!(
                get_tl_drop_count(),
                0,
                "TL counter drifted from zero -- another test may have leaked"
            );
            Self
        }
    }

    impl Drop for TLDropGuard {
        #[track_caller]
        fn drop(&mut self) {
            let v = get_tl_drop_count();
            if !std::thread::panicking() {
                assert_eq!(
                    v, 0,
                    "TL counter drifted from zero -- this test might have leaked"
                );
            }
            tl_drop_count_reset();
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    /// A `SchemaWrite` and `SchemaRead` that will increment the TL counter when constructed.
    struct DropCounted;

    impl Arbitrary for DropCounted {
        type Parameters = ();
        type Strategy = Just<Self>;
        fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
            Just(Self::new())
        }
    }

    impl DropCounted {
        const TAG_BYTE: u8 = 0;

        fn new() -> Self {
            tl_drop_count_inc();
            Self
        }
    }

    impl Clone for DropCounted {
        fn clone(&self) -> Self {
            tl_drop_count_inc();
            Self
        }
    }

    impl Drop for DropCounted {
        fn drop(&mut self) {
            tl_drop_count_dec();
        }
    }

    impl<C: Config> SchemaWrite<C> for DropCounted {
        type Src = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn size_of(_src: &Self::Src) -> WriteResult<usize> {
            Ok(1)
        }
        fn write(writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
            <u8 as SchemaWrite<C>>::write(writer, &Self::TAG_BYTE)?;
            Ok(())
        }
    }

    impl<'de, C: Config> SchemaRead<'de, C> for DropCounted {
        type Dst = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
            reader.consume(1)?;
            // This will increment the counter.
            dst.write(DropCounted::new());
            Ok(())
        }
    }

    /// A `SchemaRead` that will always error on read.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, proptest_derive::Arbitrary)]
    struct ErrorsOnRead;

    impl ErrorsOnRead {
        const TAG_BYTE: u8 = 1;
    }

    impl<C: Config> SchemaWrite<C> for ErrorsOnRead {
        type Src = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn size_of(_src: &Self::Src) -> WriteResult<usize> {
            Ok(1)
        }

        fn write(writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
            <u8 as SchemaWrite<C>>::write(writer, &Self::TAG_BYTE)
        }
    }

    impl<'de, C: Config> SchemaRead<'de, C> for ErrorsOnRead {
        type Dst = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn read(
            reader: &mut impl Reader<'de>,
            _dst: &mut MaybeUninit<Self::Dst>,
        ) -> ReadResult<()> {
            reader.consume(1)?;
            Err(error::ReadError::PointerSizedReadError)
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, proptest_derive::Arbitrary)]
    enum DropCountedMaybeError {
        DropCounted(DropCounted),
        ErrorsOnRead(ErrorsOnRead),
    }

    impl<C: Config> SchemaWrite<C> for DropCountedMaybeError {
        type Src = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn size_of(src: &Self::Src) -> WriteResult<usize> {
            match src {
                DropCountedMaybeError::DropCounted(v) => {
                    <DropCounted as SchemaWrite<C>>::size_of(v)
                }
                DropCountedMaybeError::ErrorsOnRead(v) => {
                    <ErrorsOnRead as SchemaWrite<C>>::size_of(v)
                }
            }
        }

        fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
            match src {
                DropCountedMaybeError::DropCounted(v) => {
                    <DropCounted as SchemaWrite<C>>::write(writer, v)
                }
                DropCountedMaybeError::ErrorsOnRead(v) => {
                    <ErrorsOnRead as SchemaWrite<C>>::write(writer, v)
                }
            }
        }
    }

    impl<'de, C: Config> SchemaRead<'de, C> for DropCountedMaybeError {
        type Dst = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
            let byte = <u8 as SchemaRead<'de, C>>::get(reader)?;
            match byte {
                DropCounted::TAG_BYTE => {
                    dst.write(DropCountedMaybeError::DropCounted(DropCounted::new()));
                    Ok(())
                }
                ErrorsOnRead::TAG_BYTE => Err(error::ReadError::PointerSizedReadError),
                _ => Err(invalid_tag_encoding(byte as usize)),
            }
        }
    }

    #[test]
    fn drop_count_sanity() {
        let _guard = TLDropGuard::new();
        // Ensure our incrementing counter works
        let serialized = { serialize(&[DropCounted::new(), DropCounted::new()]).unwrap() };
        let _deserialized: [DropCounted; 2] = deserialize(&serialized).unwrap();
        assert_eq!(get_tl_drop_count(), 2);
    }

    #[test]
    fn drop_count_maybe_error_sanity() {
        let _guard = TLDropGuard::new();
        let serialized =
            { serialize(&[DropCountedMaybeError::DropCounted(DropCounted::new())]).unwrap() };
        let _deserialized: [DropCountedMaybeError; 1] = deserialize(&serialized).unwrap();
        assert_eq!(get_tl_drop_count(), 1);

        let serialized = {
            serialize(&[
                DropCountedMaybeError::DropCounted(DropCounted::new()),
                DropCountedMaybeError::ErrorsOnRead(ErrorsOnRead),
            ])
            .unwrap()
        };
        let _deserialized: ReadResult<[DropCountedMaybeError; 2]> = deserialize(&serialized);
    }

    /// Test that the derive macro handles drops of initialized fields on partially initialized structs.
    #[test]
    fn test_struct_derive_handles_partial_drop() {
        /// Represents a struct that would leak if the derive macro didn't handle drops of initialized fields
        /// on error.
        #[derive(SchemaWrite, SchemaRead, proptest_derive::Arbitrary, Debug, PartialEq, Eq)]
        #[wincode(internal)]
        struct CouldLeak {
            data: DropCountedMaybeError,
            data2: DropCountedMaybeError,
            data3: DropCountedMaybeError,
        }

        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(could_leak: CouldLeak)| {
            let serialized = serialize(&could_leak).unwrap();
            let deserialized = CouldLeak::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(could_leak, deserialized);
            }
        });
    }

    // Odd use case, but it's technically valid so we test it.
    #[test]
    fn test_vec_of_references_borrows_from_input() {
        #[derive(
            SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary, Clone, Copy,
        )]
        #[wincode(internal)]
        #[repr(transparent)]
        struct BigBytes([u8; 512]);
        proptest!(proptest_cfg(), |(vec in proptest::collection::vec(any::<BigBytes>(), 0..=8))| {
            // Serialize as owned bytes.
            let bytes = serialize(&vec).unwrap();
            let borrowed: Vec<&BigBytes> = deserialize(&bytes).unwrap();

            prop_assert_eq!(borrowed.len(), vec.len());
            let start = bytes.as_ptr().addr();
            let end = start + bytes.len();
            for (i, r) in borrowed.iter().enumerate() {
                // Values match
                prop_assert_eq!(**r, vec[i]);
                // References point into the input buffer
                let p = ptr::from_ref(*r).addr();
                prop_assert!(p >= start && p < end);
            }
        });
    }

    // Odd use case, but it's technically valid so we test it.
    #[test]
    fn test_boxed_slice_of_references_borrows_from_input() {
        #[derive(
            SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary, Clone, Copy,
        )]
        #[wincode(internal)]
        #[repr(transparent)]
        struct BigBytes([u8; 512]);
        proptest!(proptest_cfg(), |(vec in proptest::collection::vec(any::<BigBytes>(), 0..=8))| {
            let boxed: Box<[BigBytes]> = vec.into_boxed_slice();
            let bytes = serialize(&boxed).unwrap();
            let borrowed: Box<[&BigBytes]> = deserialize(&bytes).unwrap();

            prop_assert_eq!(borrowed.len(), boxed.len());
            let start = bytes.as_ptr().addr();
            let end = start + bytes.len();
            for (i, &r) in borrowed.iter().enumerate() {
                prop_assert_eq!(*r, boxed[i]);
                let p = ptr::from_ref(r).addr();
                prop_assert!(p >= start && p < end);
            }
        });
    }

    /// Test that the derive macro handles drops of initialized fields on partially initialized enums.
    #[test]
    fn test_enum_derive_handles_partial_drop() {
        /// Represents an enum that would leak if the derive macro didn't handle drops of initialized fields
        /// on error.
        #[derive(SchemaWrite, SchemaRead, proptest_derive::Arbitrary, Debug, PartialEq, Eq)]
        #[wincode(internal)]
        enum CouldLeak {
            A {
                a: DropCountedMaybeError,
                b: DropCountedMaybeError,
            },
            B(
                DropCountedMaybeError,
                DropCountedMaybeError,
                DropCountedMaybeError,
            ),
            C(DropCountedMaybeError),
            D,
        }

        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(could_leak: CouldLeak)| {
            let serialized = serialize(&could_leak).unwrap();
            let deserialized = CouldLeak::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(could_leak, deserialized);
            }
        });
    }

    #[test]
    fn test_tuple_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        let serialized =
            { serialize(&(DropCounted::new(), DropCounted::new(), ErrorsOnRead)).unwrap() };
        let deserialized: ReadResult<(DropCounted, DropCounted, ErrorsOnRead)> =
            deserialize(&serialized);
        assert!(deserialized.is_err());
    }

    #[test]
    fn test_vec_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(vec in proptest::collection::vec(any::<DropCountedMaybeError>(), 0..100))| {
            let serialized = serialize(&vec).unwrap();
            let deserialized = <Vec<DropCountedMaybeError>>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(vec, deserialized);
            }
        });
    }

    #[test]
    fn test_vec_deque_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(vec in proptest::collection::vec_deque(any::<DropCountedMaybeError>(), 0..100))| {
            let serialized = serialize(&vec).unwrap();
            let deserialized = <VecDeque<DropCountedMaybeError>>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(vec, deserialized);
            }
        });
    }

    #[test]
    fn test_boxed_slice_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(slice in proptest::collection::vec(any::<DropCountedMaybeError>(), 0..100).prop_map(|vec| vec.into_boxed_slice()))| {
            let serialized = serialize(&slice).unwrap();
            let deserialized = <Box<[DropCountedMaybeError]>>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(slice, deserialized);
            }
        });
    }

    #[test]
    fn test_rc_slice_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(slice in proptest::collection::vec(any::<DropCountedMaybeError>(), 0..100).prop_map(Rc::from))| {
            let serialized = serialize(&slice).unwrap();
            let deserialized = <Rc<[DropCountedMaybeError]>>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(slice, deserialized);
            }
        });
    }

    #[test]
    fn test_arc_slice_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(slice in proptest::collection::vec(any::<DropCountedMaybeError>(), 0..100).prop_map(Arc::from))| {
            let serialized = serialize(&slice).unwrap();
            let deserialized = <Arc<[DropCountedMaybeError]>>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(slice, deserialized);
            }
        });
    }

    #[test]
    fn test_arc_handles_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(data in any::<DropCountedMaybeError>().prop_map(Rc::from))| {
            let serialized = serialize(&data).unwrap();
            let deserialized = deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(data, deserialized);
            }
        });
    }

    #[test]
    fn test_rc_handles_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(data in any::<DropCountedMaybeError>().prop_map(Rc::from))| {
            let serialized = serialize(&data).unwrap();
            let deserialized = deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(data, deserialized);
            }
        });
    }

    #[test]
    fn test_box_handles_drop() {
        let _guard = TLDropGuard::new();
        proptest!(proptest_cfg(), |(data in any::<DropCountedMaybeError>().prop_map(Box::new))| {
            let serialized = serialize(&data).unwrap();
            let deserialized = deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(data, deserialized);
            }
        });
    }

    #[test]
    fn test_array_handles_partial_drop() {
        let _guard = TLDropGuard::new();

        proptest!(proptest_cfg(), |(array in proptest::array::uniform32(any::<DropCountedMaybeError>()))| {
            let serialized = serialize(&array).unwrap();
            let deserialized = <[DropCountedMaybeError; 32]>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(array, deserialized);
            }
        });
    }

    #[test]
    fn test_struct_extensions_builder_handles_partial_drop() {
        #[derive(SchemaWrite, SchemaRead, Debug, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Test {
            a: DropCounted,
            b: DropCounted,
            c: DropCounted,
        }

        {
            let _guard = TLDropGuard::new();
            proptest!(proptest_cfg(), |(test: Test)| {
                let serialized = serialize(&test).unwrap();
                let mut test = MaybeUninit::<Test>::uninit();
                let reader = &mut serialized.as_slice();
                let mut builder = TestUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut test);
                builder.read_a(reader)?.read_b(reader)?;
                prop_assert!(!builder.is_init());
                // Struct is not fully initialized, so the two initialized fields should be dropped.
            });
        }

        #[derive(SchemaWrite, SchemaRead, Debug, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        // Same test, but with a tuple struct.
        struct TestTuple(DropCounted, DropCounted);

        {
            let _guard = TLDropGuard::new();
            proptest!(proptest_cfg(), |(test: TestTuple)| {
                let serialized = serialize(&test).unwrap();
                let mut test = MaybeUninit::<TestTuple>::uninit();
                let reader = &mut serialized.as_slice();
                let mut builder = TestTupleUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut test);
                builder.read_0(reader)?;
                prop_assert!(!builder.is_init());
                // Struct is not fully initialized, so the first initialized field should be dropped.
            });
        }
    }

    #[test]
    fn test_struct_extensions_nested_builder_handles_partial_drop() {
        #[derive(SchemaWrite, SchemaRead, Debug, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Inner {
            a: DropCounted,
            b: DropCounted,
            c: DropCounted,
        }

        #[derive(SchemaWrite, SchemaRead, Debug, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Test {
            inner: Inner,
            b: DropCounted,
        }

        {
            let _guard = TLDropGuard::new();
            proptest!(proptest_cfg(), |(test: Test)| {
                let serialized = serialize(&test).unwrap();
                let mut test = MaybeUninit::<Test>::uninit();
                let reader = &mut serialized.as_slice();
                let mut outer_builder = TestUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut test);
                unsafe {
                    outer_builder.init_inner_with(|inner| {
                        let mut inner_builder = InnerUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(inner);
                        inner_builder.read_a(reader)?;
                        inner_builder.read_b(reader)?;
                        inner_builder.read_c(reader)?;
                        assert!(inner_builder.is_init());
                        inner_builder.finish();
                        Ok(())
                    })?;
                }
                // Outer struct is not fully initialized, so the inner struct should be dropped.
            });
        }
    }

    #[test]
    fn test_struct_extensions_nested_fully_initialized() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Inner {
            a: DropCounted,
            b: DropCounted,
            c: DropCounted,
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Test {
            inner: Inner,
            b: DropCounted,
        }

        {
            let _guard = TLDropGuard::new();
            proptest!(proptest_cfg(), |(test: Test)| {
                let serialized = serialize(&test).unwrap();
                let mut uninit = MaybeUninit::<Test>::uninit();
                let reader = &mut serialized.as_slice();
                let mut outer_builder = TestUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
                unsafe {
                    outer_builder.init_inner_with(|inner| {
                        let mut inner_builder = InnerUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(inner);
                        inner_builder.read_a(reader)?;
                        inner_builder.read_b(reader)?;
                        inner_builder.read_c(reader)?;
                        assert!(inner_builder.is_init());
                        inner_builder.finish();
                        Ok(())
                    })?;
                }
                outer_builder.read_b(reader)?;
                prop_assert!(outer_builder.is_init());
                outer_builder.finish();
                let init = unsafe { uninit.assume_init() };
                prop_assert_eq!(test, init);
            });
        }
    }

    #[test]
    fn test_struct_extensions() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Test {
            a: Vec<u8>,
            b: [u8; 32],
            c: u64,
        }

        proptest!(proptest_cfg(), |(test: Test)| {
            let serialized = serialize(&test).unwrap();
            let mut uninit = MaybeUninit::<Test>::uninit();
            let reader = &mut serialized.as_slice();
            let mut builder = TestUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
            builder
                .read_a(reader)?
                .read_b(reader)?
                .write_c(test.c);
            prop_assert!(builder.is_init());
            builder.finish();
            let init = unsafe { uninit.assume_init() };
            prop_assert_eq!(test, init);
        });
    }

    #[test]
    fn test_struct_extensions_with_container() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Test {
            #[wincode(with = "containers::Vec<Pod<_>>")]
            a: Vec<u8>,
            #[wincode(with = "containers::Pod<_>")]
            b: [u8; 32],
            c: u64,
        }

        proptest!(proptest_cfg(), |(test: Test)| {
            let mut uninit = MaybeUninit::<Test>::uninit();
            let mut builder = TestUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
            builder
                .write_a(test.a.clone())
                .write_b(test.b)
                .write_c(test.c);
            prop_assert!(builder.is_init());
            let init_mut = unsafe { builder.into_assume_init_mut() };
            prop_assert_eq!(&test, init_mut);
            // Ensure `uninit` is marked initialized so fields are dropped.
            let init = unsafe { uninit.assume_init() };
            prop_assert_eq!(test, init);
        });
    }

    #[test]
    fn test_struct_extensions_with_reference() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        struct Test {
            a: Vec<u8>,
            b: Option<String>,
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq)]
        #[wincode(internal, struct_extensions)]
        struct TestRef<'a> {
            a: &'a [u8],
            b: Option<&'a str>,
        }

        proptest!(proptest_cfg(), |(test: Test)| {
            let mut uninit = MaybeUninit::<TestRef>::uninit();
            let mut builder = TestRefUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
            builder
                .write_a(test.a.as_slice())
                .write_b(test.b.as_deref());
            prop_assert!(builder.is_init());
            builder.finish();
            let init = unsafe { uninit.assume_init() };
            prop_assert_eq!(test.a.as_slice(), init.a);
            prop_assert_eq!(test.b.as_deref(), init.b);
        });
    }

    #[test]
    fn test_struct_extensions_with_mapped_type() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        struct Test {
            a: Vec<u8>,
            b: [u8; 32],
            c: u64,
        }

        #[derive(SchemaWrite, SchemaRead)]
        #[wincode(internal, from = "Test", struct_extensions)]
        struct TestMapped {
            a: containers::Vec<containers::Pod<u8>>,
            b: containers::Pod<[u8; 32]>,
            c: u64,
        }

        proptest!(proptest_cfg(), |(test: Test)| {
            let mut uninit = MaybeUninit::<Test>::uninit();
            let mut builder = TestMappedUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
            builder
                .write_a(test.a.clone())
                .write_b(test.b)
                .write_c(test.c);
            prop_assert!(builder.is_init());
            builder.finish();
            let init = unsafe { uninit.assume_init() };
            prop_assert_eq!(test, init);
        });
    }

    #[test]
    fn test_struct_extensions_builder_fully_initialized() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        struct Test {
            a: DropCounted,
            b: DropCounted,
            c: DropCounted,
        }

        {
            let _guard = TLDropGuard::new();
            proptest!(proptest_cfg(), |(test: Test)| {
                let serialized = serialize(&test).unwrap();
                let mut uninit = MaybeUninit::<Test>::uninit();
                let reader = &mut serialized.as_slice();
                let mut builder = TestUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
                builder
                    .read_a(reader)?
                    .read_b(reader)?
                    .read_c(reader)?;
                prop_assert!(builder.is_init());
                let init = unsafe { builder.into_assume_init_mut() };
                prop_assert_eq!(&test, init);

                let init = unsafe { uninit.assume_init() };
                prop_assert_eq!(test, init);
            });
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal, struct_extensions)]
        // Same test, but with a tuple struct.
        struct TestTuple(DropCounted, DropCounted);

        {
            let _guard = TLDropGuard::new();
            proptest!(proptest_cfg(), |(test: TestTuple)| {
                let serialized = serialize(&test).unwrap();
                let mut uninit = MaybeUninit::<TestTuple>::uninit();
                let reader = &mut serialized.as_slice();
                let mut builder = TestTupleUninitBuilder::<DefaultConfig>::from_maybe_uninit_mut(&mut uninit);
                builder
                    .read_0(reader)?
                    .read_1(reader)?;
                assert!(builder.is_init());
                builder.finish();

                let init = unsafe { uninit.assume_init() };
                prop_assert_eq!(test, init);
            });
        }
    }

    #[test]
    fn test_struct_with_reference_equivalence() {
        #[derive(
            SchemaWrite, SchemaRead, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize,
        )]
        #[wincode(internal)]
        struct WithReference<'a> {
            data: &'a str,
            id: u64,
        }

        proptest!(proptest_cfg(), |(s in any::<String>(), id in any::<u64>())| {
            let serialized = serialize(&WithReference { data: &s, id }).unwrap();
            let bincode_serialized = bincode::serialize(&WithReference { data: &s, id }).unwrap();
            prop_assert_eq!(&serialized, &bincode_serialized);
            let deserialized: WithReference = deserialize(&serialized).unwrap();
            let bincode_deserialized: WithReference = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_enum_equivalence() {
        #[derive(
            SchemaWrite,
            SchemaRead,
            Debug,
            PartialEq,
            Eq,
            serde::Serialize,
            serde::Deserialize,
            Clone,
            proptest_derive::Arbitrary,
        )]
        #[wincode(internal)]
        enum Enum {
            A { name: String, id: u64 },
            B(String, #[wincode(with = "containers::Vec<Pod<_>>")] Vec<u8>),
            C,
        }

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let bincode_serialized = bincode::serialize(&e).unwrap();
            prop_assert_eq!(&serialized, &bincode_serialized);
            let deserialized: Enum = deserialize(&serialized).unwrap();
            let bincode_deserialized: Enum = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn enum_with_tag_encoding_roundtrip() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal, tag_encoding = "u8")]
        enum Enum {
            A { name: String, id: u64 },
            B(String, Vec<u8>),
            C,
        }

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let deserialized: Enum = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, e);
        });
    }

    #[test]
    fn enum_with_custom_tag_roundtrip() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        enum Enum {
            #[wincode(tag = 5)]
            A { name: String, id: u64 },
            #[wincode(tag = 8)]
            B(String, Vec<u8>),
            #[wincode(tag = 13)]
            C,
        }

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let deserialized: Enum = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, e);
        });

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let int: u32 = match e {
                Enum::A { .. } => 5,
                Enum::B(..) => 8,
                Enum::C => 13,
            };
            prop_assert_eq!(&int.to_le_bytes(), &serialized[..4]);
        });
    }

    #[test]
    fn unit_enum_with_tag_encoding_static_size() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal, tag_encoding = "u8")]
        enum Enum {
            A,
            B,
            C,
        }

        assert!(matches!(
            <Enum as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 1,
                zero_copy: false
            }
        ));

        assert!(matches!(
            <Enum as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 1,
                zero_copy: false
            }
        ));
    }

    #[test]
    fn unit_enum_with_static_size() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        enum Enum {
            A,
            B,
            C,
        }

        assert!(matches!(
            <Enum as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 4,
                zero_copy: false
            }
        ));

        assert!(matches!(
            <Enum as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 4,
                zero_copy: false
            }
        ));
    }

    #[test]
    fn enum_tag_encoding() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal, tag_encoding = "u8")]
        enum EnumU8 {
            A,
            B,
            C,
        }

        proptest!(proptest_cfg(), |(e: EnumU8)| {
            let serialized = serialize(&e).unwrap();
            let int = e as u8;
            prop_assert_eq!(&int.to_le_bytes(), &serialized[..]);
        });

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal, tag_encoding = "u8")]
        enum EnumTupleU8 {
            A(u64),
            B(StructStatic),
            C(StructNonStatic),
        }

        proptest!(proptest_cfg(), |(e: EnumTupleU8)| {
            let serialized = serialize(&e).unwrap();
            let int: u8 = match e {
                EnumTupleU8::A(_) => 0,
                EnumTupleU8::B(_) => 1,
                EnumTupleU8::C(_) => 2,
            };
            prop_assert_eq!(&int.to_le_bytes(), &serialized[..1]);
        });

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal, tag_encoding = "u8")]
        enum EnumRecordU8 {
            A { id: u64 },
            B { data: StructStatic },
            C { data: StructNonStatic },
        }

        proptest!(proptest_cfg(), |(e: EnumRecordU8)| {
            let serialized = serialize(&e).unwrap();
            let int: u8 = match e {
                EnumRecordU8::A { .. } => 0,
                EnumRecordU8::B { .. } => 1,
                EnumRecordU8::C { .. } => 2,
            };
            prop_assert_eq!(&int.to_le_bytes(), &serialized[..1]);
        });
    }

    #[test]
    fn enum_static_uniform_variants() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        enum Enum {
            A {
                a: u64,
            },
            B {
                x: u32,
                y: u32,
            },
            C {
                a: u8,
                b: u8,
                c: u8,
                d: u8,
                e: u8,
                f: u8,
                g: u8,
                h: u8,
            },
        }

        assert_eq!(
            <Enum as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                // (account for discriminant u32)
                size: 8 + 4,
                zero_copy: false
            }
        );
        assert_eq!(
            <Enum as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                // (account for discriminant u32)
                size: 8 + 4,
                zero_copy: false
            }
        );

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let deserialized: Enum = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, e);
        });
    }

    #[test]
    fn enum_dynamic_non_uniform_variants() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        enum Enum {
            A { a: u64 },
            B { x: u32, y: u32 },
            C { a: u8, b: u8 },
        }

        assert_eq!(
            <Enum as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Dynamic
        );
        assert_eq!(
            <Enum as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Dynamic
        );

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let deserialized: Enum = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, e);
        });
    }

    #[test]
    fn enum_single_variant_type_meta_pass_thru() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        enum Enum {
            A { a: u8, b: [u8; 32] },
        }

        // Single variant enums should use the `TypeMeta` of the variant, but the zero-copy
        // flag should be `false`, due to the discriminant having potentially invalid bit patterns.
        assert_eq!(
            <Enum as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 1 + 32 + 4,
                zero_copy: false
            }
        );
        assert_eq!(
            <Enum as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 1 + 32 + 4,
                zero_copy: false
            }
        );
    }

    #[test]
    fn enum_unit_and_non_unit_dynamic() {
        #[derive(
            SchemaWrite,
            SchemaRead,
            Debug,
            PartialEq,
            proptest_derive::Arbitrary,
            serde::Serialize,
            serde::Deserialize,
        )]
        #[wincode(internal)]
        enum Enum {
            Unit,
            NonUnit(u8),
        }

        assert_eq!(
            <Enum as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Dynamic
        );
        assert_eq!(
            <Enum as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Dynamic
        );

        proptest!(proptest_cfg(), |(e: Enum)| {
            let serialized = serialize(&e).unwrap();
            let bincode_serialized = bincode::serialize(&e).unwrap();
            prop_assert_eq!(&serialized, &bincode_serialized);

            let deserialized: Enum = deserialize(&serialized).unwrap();
            let bincode_deserialized: Enum = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&deserialized, &bincode_deserialized);
            prop_assert_eq!(deserialized, e);
        });
    }

    #[test]
    fn test_phantom_data() {
        let val = PhantomData::<StructStatic>;
        let serialized = serialize(&val).unwrap();
        let bincode_serialized = bincode::serialize(&val).unwrap();
        assert_eq!(&serialized, &bincode_serialized);
        assert_eq!(
            <PhantomData<StructStatic> as SchemaWrite<DefaultConfig>>::size_of(&val).unwrap(),
            bincode::serialized_size(&val).unwrap() as usize
        );
        let deserialized: PhantomData<StructStatic> = deserialize(&serialized).unwrap();
        let bincode_deserialized: PhantomData<StructStatic> =
            bincode::deserialize(&bincode_serialized).unwrap();
        assert_eq!(deserialized, bincode_deserialized);
    }

    #[test]
    fn test_unit() {
        let serialized = serialize(&()).unwrap();
        let bincode_serialized = bincode::serialize(&()).unwrap();
        assert_eq!(&serialized, &bincode_serialized);
        assert_eq!(
            <() as SchemaWrite<DefaultConfig>>::size_of(&()).unwrap(),
            bincode::serialized_size(&()).unwrap() as usize
        );
        assert!(deserialize::<()>(&serialized).is_ok());
        assert!(bincode::deserialize::<()>(&bincode_serialized).is_ok());
    }

    #[test]
    fn test_borrowed_bytes() {
        #[derive(
            SchemaWrite, SchemaRead, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize,
        )]
        #[wincode(internal)]
        struct BorrowedBytes<'a> {
            bytes: &'a [u8],
        }

        proptest!(proptest_cfg(), |(bytes in proptest::collection::vec(any::<u8>(), 0..=100))| {
            let val = BorrowedBytes { bytes: &bytes };
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: BorrowedBytes = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BorrowedBytes = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&val, &bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        });
    }

    #[test]
    fn test_boxed_slice_pod_drop() {
        #[derive(proptest_derive::Arbitrary, Debug, Clone, Copy)]
        #[allow(dead_code)]
        struct Signature([u8; 64]);

        type Target = containers::Box<[Pod<Signature>]>;
        proptest!(proptest_cfg(), |(slice in proptest::collection::vec(any::<Signature>(), 1..=32).prop_map(|vec| vec.into_boxed_slice()))| {
            let serialized = Target::serialize(&slice).unwrap();
            // Deliberately trigger the drop with a failed deserialization
            // This test is specifically to get miri to exercise the drop logic
            let deserialized = Target::deserialize(&serialized[..serialized.len() - 32]);
            prop_assert!(deserialized.is_err());
        });
    }

    #[test]
    fn test_zero_copy_padding_disqualification() {
        #[derive(SchemaWrite, SchemaRead)]
        #[wincode(internal)]
        #[repr(C, align(4))]
        struct Padded {
            a: u8,
        }

        assert!(matches!(
            <Padded as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                // Serialized size is still the size of the byte, not the in-memory size.
                size: 1,
                // Padding disqualifies the type from zero-copy optimization.
                zero_copy: false
            }
        ));

        assert!(matches!(
            <Padded as SchemaRead<'_, DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                // Serialized size is still the size of the byte, not the in-memory size.
                size: 1,
                // Padding disqualifies the type from zero-copy optimization.
                zero_copy: false
            }
        ));
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_char(val in any::<char>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            prop_assert_eq!(<char as SchemaWrite<DefaultConfig>>::size_of(&val).unwrap(), bincode::serialized_size(&val).unwrap() as usize);

            let bincode_deserialized: char = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: char = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(val, bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }

        #[test]
        fn test_elem_compat(val in any::<StructStatic>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = <Elem<StructStatic>>::serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: StructStatic = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: StructStatic = <Elem<StructStatic>>::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&val, &bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }

        #[test]
        fn test_elem_vec_compat(val in proptest::collection::vec(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = <containers::Vec<Elem<StructStatic>>>::serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = <containers::Vec<Elem<StructStatic>>>::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&val, &bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }

        #[test]
        fn test_vec_elem_static(vec in proptest::collection::vec(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Vec<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_elem_zero_copy(vec in proptest::collection::vec(any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<StructZeroCopy> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Vec<StructZeroCopy> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_elem_non_static(vec in proptest::collection::vec(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Vec<StructNonStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_elem_bytes(vec in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<u8> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Vec<u8> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_serialize_slice(slice in proptest::collection::vec(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(slice.as_slice()).unwrap();
            let schema_serialized = serialize(slice.as_slice()).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
        }

        #[test]
        fn test_vec_pod(vec in proptest::collection::vec(any::<[u8; 32]>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<[u8; 32]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Vec<[u8; 32]> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_deque_elem_static(vec in proptest::collection::vec_deque(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: VecDeque<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: VecDeque<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_deque_elem_non_static(vec in proptest::collection::vec_deque(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: VecDeque<StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: VecDeque<StructNonStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_deque_elem_bytes(vec in proptest::collection::vec_deque(any::<u8>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            let schema_serialized = serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: VecDeque<u8> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: VecDeque<u8> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_hash_map_zero_copy(map in proptest::collection::hash_map(any::<u8>(), any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_hash_map_static(map in proptest::collection::hash_map(any::<u64>(), any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_hash_map_non_static(map in proptest::collection::hash_map(any::<u64>(), any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_hash_set_zero_copy(set in proptest::collection::hash_set(any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }

        #[test]
        fn test_hash_set_static(set in proptest::collection::hash_set(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }

        #[test]
        fn test_hash_set_non_static(set in proptest::collection::hash_set(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }

        #[test]
        fn test_btree_map_zero_copy(map in proptest::collection::btree_map(any::<u8>(), any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_btree_map_static(map in proptest::collection::btree_map(any::<u64>(), any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_btree_map_non_static(map in proptest::collection::btree_map(any::<u64>(), any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_btree_set_zero_copy(set in proptest::collection::btree_set(any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }

        #[test]
        fn test_btree_set_static(set in proptest::collection::btree_set(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }

        #[test]
        fn test_btree_set_non_static(map in proptest::collection::btree_set(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_binary_heap_zero_copy(heap in proptest::collection::binary_heap(any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&heap).unwrap();
            let schema_serialized = serialize(&heap).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BinaryHeap<StructZeroCopy> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BinaryHeap<StructZeroCopy> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(heap.as_slice(), bincode_deserialized.as_slice());
            prop_assert_eq!(heap.as_slice(), schema_deserialized.as_slice());
        }

        #[test]
        fn test_binary_heap_static(heap in proptest::collection::binary_heap(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&heap).unwrap();
            let schema_serialized = serialize(&heap).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BinaryHeap<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BinaryHeap<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(heap.as_slice(), bincode_deserialized.as_slice());
            prop_assert_eq!(heap.as_slice(), schema_deserialized.as_slice());
        }

        #[test]
        fn test_binary_heap_non_static(heap in proptest::collection::binary_heap(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&heap).unwrap();
            let schema_serialized = serialize(&heap).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BinaryHeap<StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BinaryHeap<StructNonStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(heap.as_slice(), bincode_deserialized.as_slice());
            prop_assert_eq!(heap.as_slice(), schema_deserialized.as_slice());
        }

        #[test]
        fn test_linked_list_zero_copy(list in proptest::collection::linked_list(any::<StructZeroCopy>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&list).unwrap();
            let schema_serialized = serialize(&list).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&list, &bincode_deserialized);
            prop_assert_eq!(list, schema_deserialized);
        }

        #[test]
        fn test_linked_list_static(list in proptest::collection::linked_list(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&list).unwrap();
            let schema_serialized = serialize(&list).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&list, &bincode_deserialized);
            prop_assert_eq!(list, schema_deserialized);
        }

        #[test]
        fn test_linked_list_non_static(list in proptest::collection::linked_list(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&list).unwrap();
            let schema_serialized = serialize(&list).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&list, &bincode_deserialized);
            prop_assert_eq!(list, schema_deserialized);
        }

        #[test]
        fn test_array_bytes(array in any::<[u8; 32]>()) {
            let bincode_serialized = bincode::serialize(&array).unwrap();
            let schema_serialized = serialize(&array).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: [u8; 32] = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: [u8; 32] = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&array, &bincode_deserialized);
            prop_assert_eq!(array, schema_deserialized);
        }

        #[test]
        fn test_array_static(array in any::<[u64; 32]>()) {
            let bincode_serialized = bincode::serialize(&array).unwrap();
            type Target = [u64; 32];
            let schema_serialized = Target::serialize(&array).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Target = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Target = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&array, &bincode_deserialized);
            prop_assert_eq!(array, schema_deserialized);
        }

        #[test]
        fn test_array_non_static(array in any::<[StructNonStatic; 16]>()) {
            let bincode_serialized = bincode::serialize(&array).unwrap();
            type Target = [StructNonStatic; 16];
            let schema_serialized = Target::serialize(&array).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Target = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Target = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&array, &bincode_deserialized);
            prop_assert_eq!(array, schema_deserialized);
        }

        #[test]
        fn test_option(option in proptest::option::of(any::<StructStatic>())) {
            let bincode_serialized = bincode::serialize(&option).unwrap();
            let schema_serialized = serialize(&option).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Option<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Option<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&option, &bincode_deserialized);
            prop_assert_eq!(&option, &schema_deserialized);
        }

        #[test]
        fn test_option_container(option in proptest::option::of(any::<[u8; 32]>())) {
            let bincode_serialized = bincode::serialize(&option).unwrap();
            type Target = Option<Pod<[u8; 32]>>;
            let schema_serialized = Target::serialize(&option).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Option<[u8; 32]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Option<[u8; 32]> = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&option, &bincode_deserialized);
            prop_assert_eq!(&option, &schema_deserialized);
        }

        #[test]
        fn test_bool(val in any::<bool>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: bool = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: bool = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(val, bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }

        #[test]
        fn test_bool_invalid_bit_pattern(val in 2u8..=255) {
            let bincode_deserialized: Result<bool,_> = bincode::deserialize(&[val]);
            let schema_deserialized: Result<bool,_> = deserialize(&[val]);
            prop_assert!(bincode_deserialized.is_err());
            prop_assert!(schema_deserialized.is_err());
        }

        #[test]
        fn test_box(s in any::<StructStatic>()) {
            let data = Box::new(s);
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Box<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Box<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_rc(s in any::<StructStatic>()) {
            let data = Rc::new(s);
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Rc<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Rc<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_arc(s in any::<StructStatic>()) {
            let data = Arc::new(s);
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Arc<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Arc<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_boxed_slice_zero_copy(vec in proptest::collection::vec(any::<StructZeroCopy>(), 0..=100)) {
            let data = vec.into_boxed_slice();
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Box<[StructZeroCopy]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Box<[StructZeroCopy]> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_boxed_slice_static(vec in proptest::collection::vec(any::<StructStatic>(), 0..=100)) {
            let data = vec.into_boxed_slice();
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Box<[StructStatic]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Box<[StructStatic]> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_boxed_slice_non_static(vec in proptest::collection::vec(any::<StructNonStatic>(), 0..=16)) {
            let data = vec.into_boxed_slice();
            let bincode_serialized = bincode::serialize(&data).unwrap();
            type Target = Box<[StructNonStatic]>;
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Target = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Target = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_integers(
            val in (
                any::<u8>(),
                any::<i8>(),
                any::<u16>(),
                any::<i16>(),
                any::<u32>(),
                any::<i32>(),
                any::<usize>(),
                any::<isize>(),
                any::<u64>(),
                any::<i64>(),
                any::<u128>(),
                any::<i128>()
            )
        ) {
            type Target = (u8, i8, u16, i16, u32, i32, usize, isize, u64, i64, u128, i128);
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Target = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Target = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(val, bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }

        #[test]
        fn test_tuple_zero_copy(
            tuple in (
                any::<StructZeroCopy>(),
                any::<[u8; 32]>(),
            )
        ) {
            let bincode_serialized = bincode::serialize(&tuple).unwrap();
            let schema_serialized = serialize(&tuple).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&tuple, &bincode_deserialized);
            prop_assert_eq!(&tuple, &schema_deserialized);

        }

        #[test]
        fn test_tuple_static(
            tuple in (
                any::<StructStatic>(),
                any::<[u8; 32]>(),
            )
        ) {
            let bincode_serialized = bincode::serialize(&tuple).unwrap();
            let schema_serialized = serialize(&tuple).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&tuple, &bincode_deserialized);
            prop_assert_eq!(&tuple, &schema_deserialized);

        }

        #[test]
        fn test_tuple_non_static(
            tuple in (
                any::<StructNonStatic>(),
                any::<[u8; 32]>(),
                proptest::collection::vec(any::<StructStatic>(), 0..=100),
            )
        ) {
            let bincode_serialized = bincode::serialize(&tuple).unwrap();
            type BincodeTarget = (StructNonStatic, [u8; 32], Vec<StructStatic>);
            type Target = (StructNonStatic, Pod<[u8; 32]>, Vec<StructStatic>);
            let schema_serialized = Target::serialize(&tuple).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: BincodeTarget = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&tuple, &bincode_deserialized);
            prop_assert_eq!(&tuple, &schema_deserialized);

        }

        #[test]
        fn test_str(str in any::<String>()) {
            let bincode_serialized = bincode::serialize(&str).unwrap();
            let schema_serialized = serialize(&str).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: &str = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: &str = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&str, &bincode_deserialized);
            prop_assert_eq!(&str, &schema_deserialized);

            let bincode_deserialized: String = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: String = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&str, &bincode_deserialized);
            prop_assert_eq!(&str, &schema_deserialized);
        }

        #[test]
        fn test_struct_zero_copy(val in any::<StructZeroCopy>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&val, &bincode_deserialized);
            prop_assert_eq!(&val, &schema_deserialized);
        }

        #[test]
        fn test_struct_static(val in any::<StructStatic>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&val, &bincode_deserialized);
            prop_assert_eq!(&val, &schema_deserialized);
        }

        #[test]
        fn test_struct_non_static(val in any::<StructNonStatic>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&val, &bincode_deserialized);
            prop_assert_eq!(&val, &schema_deserialized);
        }

        #[test]
        fn test_floats(
            val in (
                any::<f32>(),
                any::<f64>(),
            )
        ) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: (f32, f64) = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: (f32, f64) = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(val, bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }
    }

    #[test]
    fn test_struct_zero_copy_refs() {
        // Owned zero-copy type.
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        #[repr(C)]
        struct Zc {
            a: u8,
            b: [u8; 64],
            c: i8,
            d: [i8; 64],
        }

        // `Zc`, mirrored with references.
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq)]
        #[wincode(internal)]
        #[repr(C)]
        struct ZcRefs<'a> {
            a: &'a u8,
            b: &'a [u8; 64],
            c: &'a i8,
            d: &'a [i8; 64],
        }

        // `Zc`, wrapped in a reference.
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq)]
        #[wincode(internal)]
        #[repr(transparent)]
        struct ZcWrapper<'a> {
            data: &'a Zc,
        }

        impl<'a> From<&'a ZcRefs<'a>> for Zc {
            fn from(value: &'a ZcRefs<'a>) -> Self {
                Self {
                    a: *value.a,
                    b: *value.b,
                    c: *value.c,
                    d: *value.d,
                }
            }
        }

        proptest!(proptest_cfg(), |(data in any::<Zc>())| {
            let serialized = serialize(&data).unwrap();
            let deserialized = Zc::deserialize(&serialized).unwrap();
            assert_eq!(data, deserialized);

            let serialized_ref = serialize(&ZcRefs { a: &data.a, b: &data.b, c: &data.c, d: &data.d }).unwrap();
            assert_eq!(serialized_ref, serialized);
            let deserialized_ref = ZcRefs::deserialize(&serialized_ref).unwrap();
            assert_eq!(data, (&deserialized_ref).into());

            let serialized_wrapper = serialize(&ZcWrapper { data: &data }).unwrap();
            assert_eq!(serialized_wrapper, serialized);
            let deserialized_wrapper = ZcWrapper::deserialize(&serialized_wrapper).unwrap();
            assert_eq!(data, *deserialized_wrapper.data);
        });
    }

    #[test]
    fn test_pod_zero_copy() {
        #[derive(Debug, PartialEq, Eq, proptest_derive::Arbitrary, Clone, Copy)]
        #[repr(transparent)]
        struct Address([u8; 64]);

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        #[repr(C)]
        struct MyStruct {
            #[wincode(with = "Pod<_>")]
            address: Address,
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq)]
        #[wincode(internal)]
        struct MyStructRef<'a> {
            inner: &'a MyStruct,
        }

        proptest!(proptest_cfg(), |(data in any::<MyStruct>())| {
            let serialized = serialize(&data).unwrap();
            let deserialized = MyStruct::deserialize(&serialized).unwrap();
            assert_eq!(data, deserialized);

            let serialized_ref = serialize(&MyStructRef { inner: &data }).unwrap();
            assert_eq!(serialized_ref, serialized);
            let deserialized_ref = MyStructRef::deserialize(&serialized_ref).unwrap();
            assert_eq!(data, *deserialized_ref.inner);
        });
    }

    #[test]
    fn test_pod_zero_copy_explicit_ref() {
        #[derive(Debug, PartialEq, Eq, proptest_derive::Arbitrary, Clone, Copy)]
        #[repr(transparent)]
        struct Address([u8; 64]);

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq)]
        #[wincode(internal)]
        struct MyStructRef<'a> {
            #[wincode(with = "&'a Pod<Address>")]
            address: &'a Address,
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, Eq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        struct MyStruct {
            #[wincode(with = "Pod<_>")]
            address: Address,
        }

        proptest!(proptest_cfg(), |(data in any::<MyStruct>())| {
            let serialized = serialize(&data).unwrap();
            let deserialized = MyStruct::deserialize(&serialized).unwrap();
            assert_eq!(data, deserialized);

            let serialized_ref = serialize(&MyStructRef { address: &data.address }).unwrap();
            assert_eq!(serialized_ref, serialized);
            let deserialized_ref = MyStructRef::deserialize(&serialized_ref).unwrap();
            assert_eq!(data.address, *deserialized_ref.address);
        });
    }

    #[test]
    fn test_result_basic() {
        proptest!(proptest_cfg(), |(value: Result<u64, String>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<u64, String> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<u64, String> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_result_bincode_equivalence() {
        use serde::{Deserialize, Serialize};

        #[derive(
            Serialize,
            Deserialize,
            Debug,
            PartialEq,
            Clone,
            proptest_derive::Arbitrary,
            SchemaWrite,
            SchemaRead,
        )]
        #[wincode(internal)]
        enum Error {
            NotFound,
            InvalidInput(String),
            Other(u32),
        }

        proptest!(proptest_cfg(), |(value: Result<Vec<u8>, Error>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<Vec<u8>, Error> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<Vec<u8>, Error> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_result_nested() {
        proptest!(proptest_cfg(), |(value: Result<Result<u64, String>, u32>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<Result<u64, String>, u32> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<Result<u64, String>, u32> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_result_with_complex_types() {
        use std::collections::HashMap;

        proptest!(proptest_cfg(), |(value: Result<HashMap<String, Vec<u32>>, bool>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<HashMap<String, Vec<u32>>, bool> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<HashMap<String, Vec<u32>>, bool> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_result_type_meta_static() {
        // Result<u64, u64> should be TypeMeta::Static because both T and E are Static with equal sizes
        assert!(matches!(
            <Result<u64, u64> as SchemaRead<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: 12,
                zero_copy: false
            }
        ));

        proptest!(proptest_cfg(), |(value: Result<u64, u64>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<u64, u64> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<u64, u64> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_result_type_meta_dynamic() {
        // Result<u64, String> should be TypeMeta::Dynamic because String is Dynamic
        assert!(matches!(
            <Result<u64, String> as SchemaRead<DefaultConfig>>::TYPE_META,
            TypeMeta::Dynamic
        ));

        proptest!(proptest_cfg(), |(value: Result<u64, String>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<u64, String> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<u64, String> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    #[test]
    fn test_result_type_meta_different_sizes() {
        // Result<u64, u32> should be TypeMeta::Dynamic because T and E have different sizes
        assert!(matches!(
            <Result<u64, u32> as SchemaRead<DefaultConfig>>::TYPE_META,
            TypeMeta::Dynamic
        ));

        proptest!(proptest_cfg(), |(value: Result<u64, u32>)| {
            let wincode_serialized = serialize(&value).unwrap();
            let bincode_serialized = bincode::serialize(&value).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let wincode_deserialized: Result<u64, u32> = deserialize(&wincode_serialized).unwrap();
            let bincode_deserialized: Result<u64, u32> = bincode::deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(&value, &wincode_deserialized);
            prop_assert_eq!(wincode_deserialized, bincode_deserialized);
        });
    }

    /// A buffer containing a single instance of type `T`,
    /// aligned for `T`.
    ///
    /// Implements [`Deref`] and [`DerefMut`] for `[u8]` such that it
    /// acts like a typical byte buffer, but aligned for `T`.
    struct BufAligned<T> {
        buf: Box<[T]>,
    }

    impl<T> Deref for BufAligned<T>
    where
        T: ZeroCopy,
    {
        type Target = [u8];

        fn deref(&self) -> &Self::Target {
            unsafe {
                core::slice::from_raw_parts(
                    self.buf.as_ptr() as *const u8,
                    self.buf.len() * size_of::<T>(),
                )
            }
        }
    }

    impl<T> DerefMut for BufAligned<T>
    where
        T: ZeroCopy,
    {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe {
                core::slice::from_raw_parts_mut(
                    self.buf.as_mut_ptr() as *mut u8,
                    self.buf.len() * size_of::<T>(),
                )
            }
        }
    }

    /// Serialize a single instance of type `T` into a buffer aligned for `T`.
    fn serialize_aligned<T>(src: &T) -> WriteResult<BufAligned<T>>
    where
        T: SchemaWrite<DefaultConfig, Src = T> + ZeroCopy,
    {
        assert_eq!(T::size_of(src)?, size_of::<T>());
        let mut b: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(1);
        let mut buf =
            unsafe { core::slice::from_raw_parts_mut(b.as_mut_ptr() as *mut u8, size_of::<T>()) };
        crate::serialize_into(&mut buf, src)?;
        Ok(BufAligned {
            buf: unsafe { b.assume_init() },
        })
    }

    #[test]
    fn test_zero_copy_mut_roundrip() {
        proptest!(proptest_cfg(), |(data: StructZeroCopy, data_rand: StructZeroCopy)| {
            let mut serialized = serialize_aligned(&data).unwrap();
            let deserialized: StructZeroCopy = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, data);


            // Mutate the serialized data in place
            {
                let ref_mut = StructZeroCopy::from_bytes_mut(&mut serialized).unwrap();
                *ref_mut = data_rand;
            }
            // Deserialize again on the same serialized data to
            // verify the changes were persisted
            let deserialized: StructZeroCopy = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, data_rand);
        });
    }

    #[test]
    fn test_deserialize_mut_roundrip() {
        proptest!(proptest_cfg(), |(data: StructZeroCopy, data_rand: StructZeroCopy)| {
            let mut serialized = serialize_aligned(&data).unwrap();
            let deserialized: StructZeroCopy = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, data);


            // Mutate the serialized data in place
            {
                let ref_mut: &mut StructZeroCopy = deserialize_mut(&mut serialized).unwrap();
                *ref_mut = data_rand;
            }
            // Deserialize again on the same serialized data to
            // verify the changes were persisted
            let deserialized: StructZeroCopy = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, data_rand);
        });
    }

    #[test]
    fn test_zero_copy_deserialize_ref() {
        proptest!(proptest_cfg(), |(data: StructZeroCopy)| {
            let serialized = serialize_aligned(&data).unwrap();
            let deserialized: StructZeroCopy = deserialize(&serialized).unwrap();
            prop_assert_eq!(deserialized, data);

            let ref_data = StructZeroCopy::from_bytes(&serialized).unwrap();
            prop_assert_eq!(ref_data, &data);
        });
    }

    #[test]
    fn test_custom_preallocation_size_limit() {
        let c = ConfigBuilder::default().with_preallocation_size_limit::<64>();
        proptest!(proptest_cfg(), |(value in proptest::collection::vec(any::<u8>(), 0..=128))| {
            let wincode_serialized = config::serialize(&value, c).unwrap();
            let wincode_deserialized: Result<Vec<u8>, _> = config::deserialize(&wincode_serialized, c);
            if value.len() <= 64 {
                prop_assert_eq!(value, wincode_deserialized.unwrap());
            } else {
                prop_assert!(wincode_deserialized.is_err());
            }
        });
    }

    #[test]
    fn test_custom_length_encoding() {
        let c = ConfigBuilder::default().with_length_encoding::<FixInt<u32>>();
        proptest!(proptest_cfg(), |(value: Vec<u8>)| {
            let wincode_serialized = serialize_with_config(&value, c).unwrap();
            let wincode_deserialized: Vec<u8> = deserialize_with_config(&wincode_serialized, c).unwrap();
            let len = value.len();
            prop_assert_eq!(len, u32::from_le_bytes(wincode_serialized[0..4].try_into().unwrap()) as usize);
            prop_assert_eq!(value, wincode_deserialized);
        });
    }
}
