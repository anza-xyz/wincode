//! Schema traits.
//!
//! # Example
//!
//! ```
//! # use rand::prelude::*;
//! # use wincode::{compound, Serialize, Deserialize, len::{BincodeLen, ShortU16Len}, containers::{self, Pod}};
//! # use std::array;
//!
//! # #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
//! #[repr(transparent)]
//! struct Signature([u8; 32]);
//! # #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
//! #[repr(transparent)]
//! struct Address([u8; 32]);
//!
//! # #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
//! struct MyStruct {
//!     signature: Vec<Signature>,
//!     #[serde(with = "solana_short_vec")]
//!     address: Vec<Address>,
//! }
//!
//! compound! {
//!     MyStruct {
//!         signature: containers::Vec<Pod<Signature>, BincodeLen>,
//!         address: containers::Vec<Pod<Address>, ShortU16Len>,
//!     }
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
//! ```
use {
    crate::{
        error::{Error, Result},
        io::*,
        len::SeqLen,
    },
    core::mem::MaybeUninit,
};

pub mod containers;
mod impls;

/// Types that can be written (serialized) to a byte buffer.
pub trait SchemaWrite {
    type Src: ?Sized;
    /// Get the serialized size of `Self::Src`.
    fn size_of(src: &Self::Src) -> Result<usize>;
    /// Write `Self::Src` to `writer`.
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()>;
}

/// Types that can be read (deserialized) from a byte buffer.
pub trait SchemaRead<'de> {
    type Dst;
    /// Read into `dst` from `reader`.
    ///
    /// # Safety
    ///
    /// - Implementation must properly initialize the `Self::Dst`.
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()>;

    /// Read `Self::Dst` from `reader` into a new `Self::Dst`.
    #[inline(always)]
    fn get(reader: &mut Reader<'de>) -> Result<Self::Dst> {
        let mut value = MaybeUninit::uninit();
        Self::read(reader, &mut value)?;
        // SAFETY: `read` must properly initialize the `Self::Dst`.
        Ok(unsafe { value.assume_init() })
    }
}

#[inline(always)]
fn size_of_elem_iter<'a, T, Len>(value: impl ExactSizeIterator<Item = &'a T::Src>) -> Result<usize>
where
    Len: SeqLen,
    T: SchemaWrite + 'a,
{
    Ok(Len::bytes_needed(value.len())?
        + value
            .map(T::size_of)
            .try_fold(0, |acc, x| Ok::<_, Error>(acc + x?))?)
}

#[inline(always)]
fn write_elem_iter<'a, T, Len>(
    writer: &mut Writer,
    src: impl ExactSizeIterator<Item = &'a T::Src>,
) -> Result<()>
where
    Len: SeqLen,
    T: SchemaWrite + 'a,
{
    Len::encode_len(writer, src.len())?;
    for item in src {
        T::write(writer, item)?;
    }
    Ok(())
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use {
        crate::{
            compound,
            containers::{self, Elem, Pod},
            deserialize,
            error::invalid_tag_encoding,
            io::{Reader, Writer},
            len::BincodeLen,
            serialize, Deserialize, SchemaRead, SchemaWrite, Serialize,
        },
        alloc::{boxed::Box, collections::VecDeque, string::String, vec::Vec},
        core::{cell::Cell, mem::MaybeUninit, result::Result},
        proptest::prelude::*,
    };

    #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
    struct SomeStruct {
        a: u64,
        b: u64,
    }

    compound! {
        SomeStruct {
            a: u64,
            b: u64,
        }
    }

    fn strat_some_struct() -> impl Strategy<Value = SomeStruct> {
        (0..=u64::MAX, 0..=u64::MAX).prop_map(|(a, b)| SomeStruct { a, b })
    }

    fn strat_byte_array() -> impl Strategy<Value = [u8; 32]> {
        any::<[u8; 32]>()
    }

    fn strat_byte_vec() -> impl Strategy<Value = Vec<u8>> {
        proptest::collection::vec(any::<u8>(), 0..=100)
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
        fn size_of(_src: &Self::Src) -> crate::Result<usize> {
            Ok(1)
        }
        fn write(writer: &mut Writer, _src: &Self::Src) -> crate::Result<()> {
            u8::write(writer, &Self::TAG_BYTE)?;
            Ok(())
        }
    }

    impl SchemaRead<'_> for DropCounted {
        type Dst = Self;

        fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> crate::Result<()> {
            reader.consume(1)?;
            // This will increment the counter.
            dst.write(DropCounted::new());
            Ok(())
        }
    }

    /// A `SchemaRead` that will always error on read.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct ErrorsOnRead;

    impl ErrorsOnRead {
        const TAG_BYTE: u8 = 1;
    }

    impl SchemaWrite for ErrorsOnRead {
        type Src = Self;

        fn size_of(_src: &Self::Src) -> crate::Result<usize> {
            Ok(1)
        }

        fn write(writer: &mut Writer, _src: &Self::Src) -> crate::Result<()> {
            u8::write(writer, &Self::TAG_BYTE)
        }
    }

    impl SchemaRead<'_> for ErrorsOnRead {
        type Dst = Self;

        fn read(reader: &mut Reader, _dst: &mut MaybeUninit<Self::Dst>) -> crate::Result<()> {
            reader.consume(1)?;
            Err(crate::error::Error::PointerSizedDecodeError)
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum DropCountedMaybeError {
        DropCounted(DropCounted),
        ErrorsOnRead(ErrorsOnRead),
    }

    impl SchemaWrite for DropCountedMaybeError {
        type Src = Self;

        fn size_of(src: &Self::Src) -> crate::Result<usize> {
            match src {
                DropCountedMaybeError::DropCounted(v) => DropCounted::size_of(v),
                DropCountedMaybeError::ErrorsOnRead(v) => ErrorsOnRead::size_of(v),
            }
        }

        fn write(writer: &mut Writer, src: &Self::Src) -> crate::Result<()> {
            match src {
                DropCountedMaybeError::DropCounted(v) => DropCounted::write(writer, v),
                DropCountedMaybeError::ErrorsOnRead(v) => ErrorsOnRead::write(writer, v),
            }
        }
    }

    impl SchemaRead<'_> for DropCountedMaybeError {
        type Dst = Self;
        fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> crate::Result<()> {
            let byte = u8::get(reader)?;
            match byte {
                DropCounted::TAG_BYTE => {
                    dst.write(DropCountedMaybeError::DropCounted(DropCounted::new()));
                    Ok(())
                }
                ErrorsOnRead::TAG_BYTE => Err(crate::error::Error::PointerSizedDecodeError),
                _ => Err(invalid_tag_encoding(byte as usize)),
            }
        }
    }

    fn strat_drop_counted_maybe_error() -> impl Strategy<Value = DropCountedMaybeError> {
        prop_oneof![
            Just(DropCountedMaybeError::DropCounted(DropCounted::new())),
            Just(DropCountedMaybeError::ErrorsOnRead(ErrorsOnRead)),
        ]
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
        let _deserialized: crate::Result<[DropCountedMaybeError; 2]> = deserialize(&serialized);
    }

    /// Test that the `compound!` macro handles drops of initialized fields on partially initialized structs.
    #[test]
    fn compound_handles_partial_drop() {
        /// Represents a struct that would leak if the `compound!` macro didn't handle drops of initialized fields
        /// on error.
        struct CouldLeak {
            // Increments by 1
            data: DropCounted,
            // Increments by 1
            data2: DropCounted,
            // Will trigger an error on `CouldLeak::read`, which will exercise the `compound!` macro's handling of
            // drops of initialized fields on error.
            err: ErrorsOnRead,
        }

        impl CouldLeak {
            fn new() -> Self {
                Self {
                    data: DropCounted::new(),
                    data2: DropCounted::new(),
                    err: ErrorsOnRead,
                }
            }
        }

        compound! {
            CouldLeak {
                data: DropCounted,
                data2: DropCounted,
                err: ErrorsOnRead,
            }
        }

        let _guard = TLDropGuard::new();
        let serialized = { serialize(&CouldLeak::new()).unwrap() };
        let deserialized = CouldLeak::deserialize(&serialized);
        assert!(deserialized.is_err());
    }

    #[test]
    fn tuple_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        let serialized =
            { serialize(&(DropCounted::new(), DropCounted::new(), ErrorsOnRead)).unwrap() };
        let deserialized = <(DropCounted, DropCounted, ErrorsOnRead)>::deserialize(&serialized);
        assert!(deserialized.is_err());
    }

    #[test]
    fn test_vec_handles_partial_drop() {
        let _guard = TLDropGuard::new();
        proptest!(|(vec in proptest::collection::vec(strat_drop_counted_maybe_error(), 0..100))| {
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
        proptest!(|(vec in proptest::collection::vec_deque(strat_drop_counted_maybe_error(), 0..100))| {
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
        proptest!(|(slice in proptest::collection::vec(strat_drop_counted_maybe_error(), 0..100).prop_map(|vec| vec.into_boxed_slice()))| {
            let serialized = serialize(&slice).unwrap();
            let deserialized = <Box<[DropCountedMaybeError]>>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(slice, deserialized);
            }
        });
    }

    #[test]
    fn test_array_handles_partial_drop() {
        let _guard = TLDropGuard::new();

        proptest!(|(array in proptest::array::uniform32(strat_drop_counted_maybe_error()))| {
            let serialized = serialize(&array).unwrap();
            let deserialized = <[DropCountedMaybeError; 32]>::deserialize(&serialized);
            if let Ok(deserialized) = deserialized {
                prop_assert_eq!(array, deserialized);
            }
        });
    }

    proptest! {
        #[test]
        fn test_vec_elem(vec in proptest::collection::vec(strat_some_struct(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::Vec<Elem<SomeStruct>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: Vec<SomeStruct> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_vec_pod(vec in proptest::collection::vec(strat_byte_array(), 0..=100)) {
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
        fn test_vec_deque_elem(vec in proptest::collection::vec_deque(strat_some_struct(), 0..=100)) {
            let bincode_serialized = bincode::serialize(&vec).unwrap();
            type Target = containers::VecDeque<Elem<SomeStruct>, BincodeLen>;
            let schema_serialized = Target::serialize(&vec).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: VecDeque<SomeStruct> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized = Target::deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&vec, &bincode_deserialized);
            prop_assert_eq!(vec, schema_deserialized);
        }

        #[test]
        fn test_array(array in strat_byte_array()) {
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
        fn test_option(option in proptest::option::of(strat_some_struct())) {
            let bincode_serialized = bincode::serialize(&option).unwrap();
            let schema_serialized = serialize(&option).unwrap();

            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            let bincode_deserialized: Option<SomeStruct> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: Option<SomeStruct> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&option, &bincode_deserialized);
            prop_assert_eq!(&option, &schema_deserialized);
        }

        #[test]
        fn test_option_container(option in proptest::option::of(strat_byte_array())) {
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
        fn test_box(ar in strat_byte_array(), s in strat_some_struct()) {
            let data = (Box::new(ar), Box::new(s));
            let bincode_serialized = bincode::serialize(&data).unwrap();
            type Target = (Box<[u8; 32]>, Box<SomeStruct>);
            type SchemaPodTarget = (Box<Pod<[u8; 32]>>, Box<SomeStruct>);
            let schema_serialized = Target::serialize(&data).unwrap();
            let schema_pod_serialized = SchemaPodTarget::serialize(&data).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            prop_assert_eq!(&bincode_serialized, &schema_pod_serialized);
            let bincode_deserialized: (Box<[u8; 32]>, Box<SomeStruct>) = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: (Box<[u8; 32]>, Box<SomeStruct>) = Target::deserialize(&schema_serialized).unwrap();
            let schema_pod_deserialized: (Box<[u8; 32]>, Box<SomeStruct>) = SchemaPodTarget::deserialize(&schema_pod_serialized).unwrap();
            prop_assert_eq!(&data, &bincode_deserialized);
            prop_assert_eq!(&data, &schema_deserialized);
            prop_assert_eq!(&data, &schema_pod_deserialized);
        }

        #[test]
        fn test_boxed_slice(vec in strat_byte_vec()) {
            let data = vec.into_boxed_slice();
            let bincode_serialized = bincode::serialize(&data).unwrap();
            type Target = Box<[u8]>;
            type TargetPod = containers::BoxedSlice<Pod<u8>>;
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
        fn test_tuple(
            tuple in (
                strat_some_struct(),
                strat_byte_array(),
                proptest::option::of(strat_some_struct()),
                proptest::collection::vec(strat_some_struct(), 0..=100),
                proptest::collection::vec_deque(strat_byte_array(), 0..=100)
            )
        ) {
            let bincode_serialized = bincode::serialize(&tuple).unwrap();
            type BincodeTarget = (SomeStruct, [u8; 32], Option<SomeStruct>, Vec<SomeStruct>, VecDeque<[u8; 32]>);
            type Target = (SomeStruct, Pod<[u8; 32]>, Option<SomeStruct>, Vec<SomeStruct>, containers::VecDeque<Pod<[u8; 32]>, BincodeLen>);
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
    }
}
