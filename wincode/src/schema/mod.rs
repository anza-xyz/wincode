//! Schema traits.
//!
//! # Example
//!
//! ```
//! # #[cfg(all(feature = "solana-short-vec", feature = "alloc"))] {
//! # use rand::prelude::*;
//! # use wincode::{Serialize, Deserialize, len::{BincodeLen, ShortU16Len}, containers::{self, Pod}};
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
//!     #[wincode(with = "containers::Vec<Pod<_>, BincodeLen>")]
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
        error::{ReadResult, WriteResult},
        io::*,
        len::SeqLen,
        util::type_equal,
    },
    core::mem::{transmute, MaybeUninit},
};

pub mod containers;
mod impls;

/// Indicates what kind of assumptions can be made when encoding or decoding a type.
///
/// Readers and writers may use this to optimize their behavior.
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

/// Types that can be written (serialized) to a [`Writer`].
pub trait SchemaWrite {
    type Src: ?Sized;

    const TYPE_META: TypeMeta = TypeMeta::Dynamic;

    /// Get the serialized size of `Self::Src`.
    fn size_of(src: &Self::Src) -> WriteResult<usize>;
    /// Write `Self::Src` to `writer`.
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()>;
}

/// Types that can be read (deserialized) from a [`Reader`].
pub trait SchemaRead<'de> {
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

/// A type that can be read (deserialized) from a [`Reader`] without borrowing from it.
pub trait SchemaReadOwned: for<'de> SchemaRead<'de> {}
impl<T> SchemaReadOwned for T where T: for<'de> SchemaRead<'de> {}

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
fn size_of_elem_iter<'a, T, Len>(
    value: impl ExactSizeIterator<Item = &'a T::Src>,
) -> WriteResult<usize>
where
    Len: SeqLen,
    T: SchemaWrite + 'a,
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
fn size_of_elem_slice<T, Len>(value: &[T::Src]) -> WriteResult<usize>
where
    Len: SeqLen,
    T: SchemaWrite,
    T::Src: Sized,
{
    if type_equal::<T::Src, u8>() {
        return Ok(Len::write_bytes_needed(value.len())? + value.len());
    }
    size_of_elem_iter::<T, Len>(value.iter())
}

#[inline(always)]
fn write_elem_iter<'a, T, Len>(
    writer: &mut impl Writer,
    src: impl ExactSizeIterator<Item = &'a T::Src>,
) -> WriteResult<()>
where
    Len: SeqLen,
    T: SchemaWrite + 'a,
{
    if let TypeMeta::Static { size, .. } = T::TYPE_META {
        #[allow(clippy::arithmetic_side_effects)]
        let mut writer =
            writer.as_trusted_for(Len::write_bytes_needed(src.len())? + size * src.len())?;
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
fn write_elem_slice<T, Len>(writer: &mut impl Writer, src: &[T::Src]) -> WriteResult<()>
where
    Len: SeqLen,
    T: SchemaWrite,
    T::Src: Sized,
{
    if type_equal::<T::Src, u8>() {
        let writer = &mut writer.as_trusted_for(Len::write_bytes_needed(src.len())? + src.len())?;
        Len::write(writer, src.len())?;
        writer.write(unsafe { transmute::<&[T::Src], &[u8]>(src) })?;
        writer.finish()?;
        return Ok(());
    }
    write_elem_iter::<T, Len>(writer, src.iter())
}

#[cfg(all(test, feature = "std", feature = "derive"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects)]

    use {
        crate::{
            containers::{self, Elem, Pod},
            deserialize,
            error::{self, invalid_tag_encoding},
            io::{Reader, Writer},
            len::BincodeLen,
            proptest_config::proptest_cfg,
            serialize, Deserialize, ReadResult, SchemaRead, SchemaWrite, Serialize, TypeMeta,
            WriteResult,
        },
        core::marker::PhantomData,
        proptest::prelude::*,
        std::{
            cell::Cell,
            collections::{BinaryHeap, VecDeque},
            mem::MaybeUninit,
            rc::Rc,
            result::Result,
            sync::Arc,
        },
    };

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

    impl SchemaWrite for DropCounted {
        type Src = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn size_of(_src: &Self::Src) -> WriteResult<usize> {
            Ok(1)
        }
        fn write(writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
            u8::write(writer, &Self::TAG_BYTE)?;
            Ok(())
        }
    }

    impl<'de> SchemaRead<'de> for DropCounted {
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

    impl SchemaWrite for ErrorsOnRead {
        type Src = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn size_of(_src: &Self::Src) -> WriteResult<usize> {
            Ok(1)
        }

        fn write(writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
            u8::write(writer, &Self::TAG_BYTE)
        }
    }

    impl<'de> SchemaRead<'de> for ErrorsOnRead {
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

    impl SchemaWrite for DropCountedMaybeError {
        type Src = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn size_of(src: &Self::Src) -> WriteResult<usize> {
            match src {
                DropCountedMaybeError::DropCounted(v) => DropCounted::size_of(v),
                DropCountedMaybeError::ErrorsOnRead(v) => ErrorsOnRead::size_of(v),
            }
        }

        fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
            match src {
                DropCountedMaybeError::DropCounted(v) => DropCounted::write(writer, v),
                DropCountedMaybeError::ErrorsOnRead(v) => ErrorsOnRead::write(writer, v),
            }
        }
    }

    impl<'de> SchemaRead<'de> for DropCountedMaybeError {
        type Dst = Self;

        const TYPE_META: TypeMeta = TypeMeta::Static {
            size: 1,
            zero_copy: false,
        };

        fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
            let byte = u8::get(reader)?;
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
        let deserialized = <(DropCounted, DropCounted, ErrorsOnRead)>::deserialize(&serialized);
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
    fn test_phantom_data() {
        let val = PhantomData::<StructStatic>;
        let serialized = serialize(&val).unwrap();
        let bincode_serialized = bincode::serialize(&val).unwrap();
        assert_eq!(&serialized, &bincode_serialized);
        assert_eq!(
            PhantomData::<StructStatic>::size_of(&val).unwrap(),
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
            <()>::size_of(&()).unwrap(),
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

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_char(val in any::<char>()) {
            let bincode_serialized = bincode::serialize(&val).unwrap();
            let schema_serialized = serialize(&val).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            prop_assert_eq!(char::size_of(&val).unwrap(), bincode::serialized_size(&val).unwrap() as usize);
            let bincode_deserialized: char = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: char = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(val, bincode_deserialized);
            prop_assert_eq!(val, schema_deserialized);
        }

        #[test]
        fn test_vec_elem_static(vec in proptest::collection::vec(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::Vec<Elem<StructStatic>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }


        #[test]
        fn test_vec_elem_non_static(vec in proptest::collection::vec(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::Vec<Elem<StructNonStatic>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_elem_bytes(vec in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::Vec<Elem<u8>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<u8> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
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
            type Target = containers::Vec<Pod<[u8; 32]>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<[u8; 32]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_deque_elem_static(vec in proptest::collection::vec_deque(any::<StructStatic>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::VecDeque<Elem<StructStatic>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: VecDeque<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_deque_elem_non_static(vec in proptest::collection::vec_deque(any::<StructNonStatic>(), 0..=16)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::VecDeque<Elem<StructNonStatic>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: VecDeque<StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_deque_elem_bytes(vec in proptest::collection::vec_deque(any::<u8>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::VecDeque<Elem<u8>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: VecDeque<u8> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
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
        fn test_binary_heap_pod(heap in proptest::collection::binary_heap(any::<[u8; 32]>(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&heap).unwrap();
            type TargetPod = containers::BinaryHeap<Pod<[u8; 32]>>;
            type Target = containers::BinaryHeap<Elem<[u8; 32]>>;
            let schema_serialized_pod = TargetPod::serialize(&heap).unwrap();
            let schema_serialized = Target::serialize(&heap).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized_pod);
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: BinaryHeap<[u8; 32]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized_pod = TargetPod::deserialize(&schema_serialized_pod).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(heap.as_slice(), bincode_deserialized.as_slice());
            prop_assert_eq!(heap.as_slice(), schema_deserialized.as_slice());
            prop_assert_eq!(heap.as_slice(), schema_deserialized_pod.as_slice());
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
            type Target = [u8; 32];
            let schema_serialized = Target::serialize(&array).unwrap();
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
        fn test_box(ar in any::<[u8; 32]>(), s in any::<StructStatic>()) {
            let data = (Box::new(ar), Box::new(s));
            let bincode_serialized = bincode::serialize(&data).unwrap();
            type Target = (Box<[u8; 32]>, Box<StructStatic>);
            type SchemaPodTarget = (Box<Pod<[u8; 32]>>, Box<StructStatic>);
            let schema_serialized = Target::serialize(&data).unwrap();
            let schema_pod_serialized = SchemaPodTarget::serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            prop_assert_eq!(&bincode_serialized, &schema_pod_serialized);
            let bincode_deserialized: (Box<[u8; 32]>, Box<StructStatic>) = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: (Box<[u8; 32]>, Box<StructStatic>) = Target::deserialize(&schema_serialized).unwrap();
            let schema_pod_deserialized: (Box<[u8; 32]>, Box<StructStatic>) = SchemaPodTarget::deserialize(&schema_pod_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
            prop_assert_eq!(&data, &schema_pod_deserialized);
        }

        #[test]
        fn test_rc(ar in any::<StructStatic>()) {
            let data = Rc::new(ar);
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Rc<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Rc<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_arc(ar in any::<StructStatic>()) {
            let data = Arc::new(ar);
            let bincode_serialized = bincode::serialize(&data).unwrap();
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Arc<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Arc<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
        }

        #[test]
        fn test_boxed_slice_bytes(vec in proptest::collection::vec(any::<u8>(), 0..=100)) {
            let data = vec.into_boxed_slice();
            let bincode_serialized = bincode::serialize(&data).unwrap();
            type Target = Box<[u8]>;
            type TargetPod = containers::Box<[Pod<u8>]>;
            let schema_serialized = Target::serialize(&data).unwrap();
            let schema_pod_serialized = TargetPod::serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            prop_assert_eq!(&bincode_serialized, &schema_pod_serialized);
            let bincode_deserialized: Box<[u8]> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Box<[u8]> = Target::deserialize(&schema_serialized).unwrap();
            let schema_pod_deserialized: Box<[u8]> = TargetPod::deserialize(&schema_pod_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
            prop_assert_eq!(&data, &schema_pod_deserialized);
        }

        #[test]
        fn test_boxed_slice_static(vec in proptest::collection::vec(any::<u64>(), 0..=100)) {
            let data = vec.into_boxed_slice();
            let bincode_serialized = bincode::serialize(&data).unwrap();
            type Target = Box<[u64]>;
            let schema_serialized = serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Target = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Target = Target::deserialize(&schema_serialized).unwrap();
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
}
