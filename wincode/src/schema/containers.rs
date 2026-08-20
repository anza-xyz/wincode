//! This module provides specialized implementations of standard library collection types that
//! provide control over the length encoding (see [`SeqLen`](crate::len::SeqLen)), as well
//! as special case opt-in raw-copy overrides (see [`pod_wrapper!`]).
//!
//! # Examples
//! Raw byte vec with `UseIntLen<u16>` length encoding:
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{containers, len::UseIntLen};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # use core::mem::size_of;
//! #[derive(SchemaWrite, SchemaRead, PartialEq, Debug)]
//! struct MyStruct {
//!     #[wincode(with = "containers::Vec<_, UseIntLen<u16>>")]
//!     vec: Vec<u8>,
//! }
//!
//! let my_struct = MyStruct { vec: vec![1, 2, 3] };
//! let bytes = wincode::serialize(&my_struct).unwrap();
//! assert_eq!(bytes.len(), size_of::<u16>() + my_struct.vec.len() * size_of::<u8>());
//! assert_eq!(my_struct, wincode::deserialize(&bytes).unwrap());
//! # }
//! ```
//!
//! Vector with struct elements and `UseIntLen<u16>` length encoding:
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{containers, len::UseIntLen};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # use core::mem::size_of;
//! #[derive(SchemaWrite, SchemaRead, PartialEq, Debug)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! #[derive(SchemaWrite, SchemaRead, PartialEq, Debug)]
//! struct MyStruct {
//!     #[wincode(with = "containers::Vec<Point, UseIntLen<u16>>")]
//!     vec: Vec<Point>,
//! }
//!
//! let my_struct = MyStruct {
//!     vec: vec![Point { x: 1, y: 2 }, Point { x: 3, y: 4 }],
//! };
//! let bytes = wincode::serialize(&my_struct).unwrap();
//! assert_eq!(bytes.len(), size_of::<u16>() + my_struct.vec.len() * size_of::<Point>());
//! assert_eq!(my_struct, wincode::deserialize(&bytes).unwrap());
//! # }
//! ```
//!
//! # Keyed collections
//!
//! The map and set containers additionally take a [`DuplicateKeyPolicy`]. All sequences
//! share one wire format, so an encoded sequence may repeat a key; by default the last
//! entry for a key wins, as it does for the plain `HashMap`/`BTreeMap`/… schemas.
//! [`CheckUniqueKeys`] rejects such input instead:
//!
//! ```
//! # #[cfg(feature = "alloc")] {
//! # use std::collections::BTreeSet;
//! # use wincode::{Deserialize, ReadError, containers, len::BincodeLen};
//! let bytes = wincode::serialize(&vec![1u32, 1, 2]).unwrap();
//!
//! type Lenient = containers::BTreeSet<u32, BincodeLen>;
//! type Strict = containers::BTreeSet<u32, BincodeLen, containers::CheckUniqueKeys>;
//!
//! assert_eq!(Lenient::deserialize(&bytes).unwrap(), BTreeSet::from([1, 2]));
//! assert!(matches!(Strict::deserialize(&bytes), Err(ReadError::DuplicateKey(_))));
//! # }
//! ```
//!
//! To flip the default for every keyed collection at once, see
//! [`enable_strict_map_set`](crate::config::Configuration::enable_strict_map_set).
#[cfg(all(feature = "alloc", target_has_atomic = "ptr"))]
use alloc::sync::Arc as AllocArc;
#[cfg(feature = "std")]
use core::hash::{BuildHasher, Hash};
#[cfg(all(feature = "indexmap", feature = "std"))]
use indexmap::{IndexMap as ExtIndexMap, IndexSet as ExtIndexSet};
#[cfg(feature = "std")]
use std::collections::{
    HashMap as StdHashMap, HashSet as StdHashSet, hash_map::RandomState as StdRandomState,
};
use {
    crate::{
        TypeMeta,
        config::ConfigCore,
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        len::SeqLen,
        schema::{SchemaRead, SchemaWrite, size_of_elem_iter, write_elem_iter},
    },
    core::{
        borrow::Borrow,
        marker::PhantomData,
        mem::{self, MaybeUninit},
        ptr,
    },
};
#[cfg(feature = "alloc")]
use {
    crate::{
        context,
        error::{duplicate_key, read_length_encoding_overflow},
        schema::{
            SchemaReadContext, impls::seq_capacity, size_of_elem_slice, size_of_kv_iter,
            write_elem_iter_prealloc_check, write_elem_slice_prealloc_check,
            write_kv_iter_prealloc_check,
        },
    },
    alloc::{
        boxed::Box as AllocBox,
        collections::{self, BTreeMap as AllocBTreeMap, BTreeSet as AllocBTreeSet},
        rc::Rc as AllocRc,
        vec,
    },
    core::any::type_name,
};

/// A [`Vec`](std::vec::Vec) with a customizable length encoding.
#[cfg(feature = "alloc")]
pub struct Vec<T, Len>(PhantomData<Len>, PhantomData<T>);

/// A [`VecDeque`](std::collections::VecDeque) with a customizable length encoding.
#[cfg(feature = "alloc")]
pub struct VecDeque<T, Len>(PhantomData<Len>, PhantomData<T>);

/// A [`Box<[T]>`](std::boxed::Box) with a customizable length encoding.
///
/// # Examples
///
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// # use wincode::{containers, len::UseIntLen};
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// # use core::{array, mem::size_of};
/// #[derive(SchemaWrite, SchemaRead, Clone, Copy, PartialEq, Debug)]
/// #[repr(transparent)]
/// struct Address([u8; 32]);
///
/// #[derive(SchemaWrite, SchemaRead, PartialEq, Debug)]
/// struct MyStruct {
///     #[wincode(with = "containers::Box<[Address], UseIntLen<u16>>")]
///     address: Box<[Address]>,
/// }
///
/// let my_struct = MyStruct {
///     address: vec![Address(array::from_fn(|i| i as u8)); 10].into_boxed_slice(),
/// };
/// let bytes = wincode::serialize(&my_struct).unwrap();
/// assert_eq!(bytes.len(), size_of::<u16>() + my_struct.address.len() * size_of::<Address>());
/// assert_eq!(my_struct, wincode::deserialize(&bytes).unwrap());
/// # }
/// ```
#[cfg(feature = "alloc")]
pub struct Box<T: ?Sized, Len>(PhantomData<T>, PhantomData<Len>);

#[cfg(feature = "alloc")]
/// Like [`Box`], for [`Rc`].
pub struct Rc<T: ?Sized, Len>(PhantomData<T>, PhantomData<Len>);

#[cfg(all(feature = "alloc", target_has_atomic = "ptr"))]
/// Like [`Box`], for [`Arc`].
pub struct Arc<T: ?Sized, Len>(PhantomData<T>, PhantomData<Len>);

/// Creates a wrapper type for a type that is represented by raw bytes and does not have any invalid
/// bit patterns.
///
/// By using `pod_wrapper!`, you are telling wincode that it can serialize and deserialize a type
/// with a single memcpy -- it wont pay attention to things like struct layout, endianness, or
/// anything else that would require validity or bit pattern checks. This is a very strong claim to
/// make, so be sure that your type adheres to those requirements.
///
/// Composable with sequence [`containers`](self) or compound types (structs, tuples) for
/// an optimized read/write implementation.
///
/// This can be useful outside of sequences as well, for example on newtype structs
/// containing byte arrays with `#[repr(transparent)]`.
///
/// ---
/// 💡 **Note:** as of `wincode` `0.2.0`, `pod_wrapper!` is no longer needed for types that wincode
/// can determine are "memcpy-safe".
///
/// This includes:
/// - [`u8`]
/// - [`[u8; N]`](prim@array)
/// - structs comprised of the above, and;
///     - annotated with `#[derive(SchemaWrite)]` or `#[derive(SchemaRead)]`, and;
///     - annotated with `#[repr(transparent)]` or `#[repr(C)]`.
///
/// Similarly, using built-in std collections like `Vec<T>` or `Box<[T]>` where `T` is one of the
/// above will also be automatically optimized.
///
/// You'll really only need to reach for [`pod_wrapper!`] when dealing with foreign types for which
/// you cannot derive `SchemaWrite` or `SchemaRead`. Or you're in a controlled scenario where you
/// explicitly want to avoid endianness or layout checks.
///
/// # Safety
///
/// - The type must allow any bit pattern (e.g., no `bool`s, no `char`s, etc.)
/// - If used on a compound type like a struct, all fields must be also be memcpy-able, its layout
///   must be guaranteed (via `#[repr(transparent)]` or `#[repr(C)]`), and the struct must not have
///   any padding.
/// - Must not contain references or pointers (includes types like `Vec` or `Box`).
///     - Note, you may use `pod_wrapper!` created types *inside* types like `Vec` or `Box`, e.g.,
///       `Vec<PodT>` or `Box<[PodT]>`, but using `pod_wrapper!` on the outer type is invalid.
///
/// # Examples
///
/// A repr-transparent newtype struct containing a byte array where you cannot derive `SchemaWrite`
/// or `SchemaRead`:
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// # use wincode::containers;
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// # use serde::{Serialize, Deserialize};
/// # use std::array;
/// #[derive(Serialize, Deserialize, Clone, Copy)]
/// #[repr(transparent)]
/// struct Address([u8; 32]);
///
/// wincode::pod_wrapper! {
///     unsafe struct PodAddress(Address);
/// }
///
/// #[derive(Serialize, Deserialize, SchemaWrite, SchemaRead)]
/// struct MyStruct {
///     #[wincode(with = "PodAddress")]
///     address: Address
/// }
///
/// let my_struct = MyStruct {
///     address: Address(array::from_fn(|i| i as u8)),
/// };
/// let wincode_bytes = wincode::serialize(&my_struct).unwrap();
/// let bincode_bytes = bincode::serialize(&my_struct).unwrap();
/// assert_eq!(wincode_bytes, bincode_bytes);
/// # }
/// ```
#[macro_export]
macro_rules! pod_wrapper {
    ($(unsafe struct $name:ident($type:ty);)*) => {$(
        struct $name where $type: Copy + 'static;

        // SAFETY:
        // - By using `pod_wrapper`, user asserts that the type is zero-copy, given the contract of
        //   pod_wrapper:
        //   - The type's in‑memory representation is exactly its serialized bytes.
        //   - It can be safely initialized by memcpy (no validation, no endianness/layout work).
        //   - Does not contain references or pointers.
        unsafe impl<C: $crate::config::ConfigCore> $crate::config::ZeroCopy<C> for $name {}

        unsafe impl<C: $crate::config::ConfigCore> $crate::SchemaWrite<C> for $name {
            type Src = $type;

            const TYPE_META: $crate::TypeMeta = $crate::TypeMeta::Static {
                size: size_of::<$type>(),
                zero_copy: true,
            };

            #[inline]
            fn size_of(_: &$type) -> $crate::WriteResult<usize> {
                Ok(size_of::<$type>())
            }

            #[inline]
            fn write(mut writer: impl $crate::io::Writer, src: &$type) -> $crate::WriteResult<()> {
                unsafe {
                    Ok(writer.write_t(src)?)
                }
            }
        }

        unsafe impl<'de, C: $crate::config::ConfigCore> $crate::SchemaRead<'de, C> for $name {
            type Dst = $type;

            const TYPE_META: $crate::TypeMeta = $crate::TypeMeta::Static {
                size: size_of::<$type>(),
                zero_copy: true,
            };

            fn read(mut reader: impl $crate::io::Reader<'de>, dst: &mut core::mem::MaybeUninit<$type>) -> $crate::ReadResult<()> {
                unsafe {
                    Ok(reader.copy_into_t(dst)?)
                }
            }
        }
    )*}
}
pub use pod_wrapper;

#[cfg(feature = "alloc")]
unsafe impl<T, Len, C: ConfigCore> SchemaWrite<C> for Vec<T, Len>
where
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = vec::Vec<T::Src>;

    #[inline(always)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, Len, C>(src)
    }

    #[inline(always)]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_slice_prealloc_check::<T, Len, C>(writer, src)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, Len, C: ConfigCore> SchemaRead<'de, C> for Vec<T, Len>
where
    Len: SeqLen<C>,
    T: SchemaRead<'de, C>,
{
    type Dst = vec::Vec<T::Dst>;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = Len::read_prealloc_check::<T::Dst>(reader.by_ref())?;
        <vec::Vec<T>>::read_with_context(context::Len(len), reader, dst)?;
        Ok(())
    }
}

pub(crate) struct SliceDropGuard<T> {
    ptr: *mut MaybeUninit<T>,
    initialized_len: usize,
}

impl<T> SliceDropGuard<T> {
    pub(crate) fn new(ptr: *mut MaybeUninit<T>) -> Self {
        Self {
            ptr,
            initialized_len: 0,
        }
    }

    #[inline(always)]
    #[allow(clippy::arithmetic_side_effects)]
    pub(crate) fn inc_len(&mut self) {
        if mem::needs_drop::<T>() {
            self.initialized_len += 1;
        }
    }
}

impl<T> Drop for SliceDropGuard<T> {
    #[cold]
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            unsafe {
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                    self.ptr.cast::<T>(),
                    self.initialized_len,
                ));
            }
        }
    }
}

/// Returns a mutable reference into the given Arc, without any check.
///
/// # Safety
///
/// If any other `Arc` or `Weak` pointers to the same allocation exist, then
/// they must not be dereferenced or have active borrows for the duration
/// of the returned borrow, and their inner type must be exactly the same as the
/// inner type of this Arc (including lifetimes). This is trivially the case if no
/// such pointers exist, for example immediately after `Arc::new`.
#[inline]
#[cfg(all(feature = "alloc", target_has_atomic = "ptr"))]
unsafe fn arc_get_mut_unchecked<T: ?Sized>(arc: &mut AllocArc<T>) -> &mut T {
    unsafe { &mut *AllocArc::as_ptr(arc).cast_mut() }
}

/// Returns a mutable reference into the given `Rc`,
/// without any check.
///
/// # Safety
///
/// If any other `Rc` or `Weak` pointers to the same allocation exist, then
/// they must not be dereferenced or have active borrows for the duration
/// of the returned borrow, and their inner type must be exactly the same as the
/// inner type of this Rc (including lifetimes). This is trivially the case if no
/// such pointers exist, for example immediately after `Rc::new`.
#[inline]
#[cfg(feature = "alloc")]
unsafe fn rc_get_mut_unchecked<T: ?Sized>(rc: &mut AllocRc<T>) -> &mut T {
    unsafe { &mut *AllocRc::as_ptr(rc).cast_mut() }
}

macro_rules! impl_heap_slice {
    ($container:ident => $target:ident, |$uninit:ident| $get_slice:expr) => {
        #[cfg(feature = "alloc")]
        unsafe impl<T, Len, C: ConfigCore> SchemaWrite<C> for $container<[T], Len>
        where
            Len: SeqLen<C>,
            T: SchemaWrite<C>,
            T::Src: Sized,
        {
            type Src = $target<[T::Src]>;

            #[inline(always)]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                size_of_elem_slice::<T, Len, C>(src)
            }

            #[inline(always)]
            fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
                write_elem_slice_prealloc_check::<T, Len, C>(writer, src)
            }
        }

        #[cfg(feature = "alloc")]
        unsafe impl<'de, T, Len, C: ConfigCore> SchemaRead<'de, C> for $container<[T], Len>
        where
            Len: SeqLen<C>,
            T: SchemaRead<'de, C>,
        {
            type Dst = $target<[T::Dst]>;

            #[inline(always)]
            fn read(
                mut reader: impl Reader<'de>,
                dst: &mut MaybeUninit<Self::Dst>,
            ) -> ReadResult<()> {
                let len = Len::read_prealloc_check::<T::Dst>(reader.by_ref())?;
                let mut $uninit = $target::<[T::Dst]>::new_uninit_slice(len);
                decode_into_slice_t::<T, C>(reader, $get_slice)?;
                // SAFETY: `decode_into_slice_t` initialized all elements on success.
                let container = unsafe { $uninit.assume_init() };
                dst.write(container);
                Ok(())
            }
        }
    };
}

impl_heap_slice!(Box => AllocBox, |uninit| &mut *uninit);
impl_heap_slice!(Rc  => AllocRc,  |uninit| unsafe { rc_get_mut_unchecked(&mut uninit) });
#[cfg(all(feature = "alloc", target_has_atomic = "ptr"))]
impl_heap_slice!(Arc => AllocArc, |uninit| unsafe { arc_get_mut_unchecked(&mut uninit) });

#[cfg(feature = "alloc")]
unsafe impl<T, Len, C: ConfigCore> SchemaWrite<C> for VecDeque<T, Len>
where
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = collections::VecDeque<T::Src>;

    #[inline(always)]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        size_of_elem_iter::<T, Len, C>(value.iter())
    }

    #[inline(always)]
    fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        if let TypeMeta::Static {
            size,
            zero_copy: true,
        } = T::TYPE_META
        {
            #[allow(clippy::arithmetic_side_effects)]
            let needed =
                Len::write_bytes_needed_prealloc_check::<T::Src>(src.len())? + src.len() * size;
            // SAFETY: `needed` is the size of the encoded length plus the size of the items.
            // `Len::write` and `len` writes of `T::Src` will write `needed` bytes,
            // fully initializing the trusted window.
            let mut writer = unsafe { writer.as_trusted_for(needed) }?;

            Len::write(writer.by_ref(), src.len())?;
            let (front, back) = src.as_slices();
            // SAFETY:
            // - `T` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
            // - `front` and `back` are valid non-overlapping slices.
            unsafe {
                writer.write_slice_t(front)?;
                writer.write_slice_t(back)?;
            }

            writer.finish()?;

            return Ok(());
        }

        write_elem_iter_prealloc_check::<T, Len, C>(writer, src.iter())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, Len, C: ConfigCore> SchemaRead<'de, C> for VecDeque<T, Len>
where
    Len: SeqLen<C>,
    T: SchemaRead<'de, C>,
{
    type Dst = collections::VecDeque<T::Dst>;

    #[inline(always)]
    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // Leverage the contiguous read optimization of `Vec`.
        // From<Vec<T>> for VecDeque<T> is basically free.
        let vec = <Vec<T, Len>>::get(reader)?;
        dst.write(vec.into());
        Ok(())
    }
}

#[cfg(feature = "alloc")]
/// A [`BinaryHeap`](alloc::collections::BinaryHeap) with a customizable length encoding.
pub struct BinaryHeap<T, Len>(PhantomData<Len>, PhantomData<T>);

#[cfg(feature = "alloc")]
unsafe impl<T, Len, C: ConfigCore> SchemaWrite<C> for BinaryHeap<T, Len>
where
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = collections::BinaryHeap<T::Src>;

    #[inline(always)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, Len, C>(src.as_slice())
    }

    #[inline(always)]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_slice_prealloc_check::<T, Len, C>(writer, src.as_slice())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, Len, C: ConfigCore> SchemaRead<'de, C> for BinaryHeap<T, Len>
where
    Len: SeqLen<C>,
    T: SchemaRead<'de, C>,
    T::Dst: Ord,
{
    type Dst = collections::BinaryHeap<T::Dst>;

    #[inline(always)]
    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let vec = <Vec<T, Len>>::get(reader)?;
        // Leverage the vec impl.
        dst.write(collections::BinaryHeap::from(vec));
        Ok(())
    }
}

/// How a keyed collection schema reacts when the encoded sequence repeats a key.
///
/// Default is [`UseConfig`], so naming a policy explicitly overrides the configuration.
///
/// See [`HashMap`] for an example.
pub trait DuplicateKeyPolicy {
    /// Whether a repeated key aborts the read with
    /// [`ReadError::DuplicateKey`](crate::error::ReadError::DuplicateKey).
    ///
    /// A method rather than an associated constant only because [`UseConfig`] needs `C`
    /// to answer; it resolves to a constant once monomorphized either way.
    fn reject_duplicates<C: ConfigCore>() -> bool;
}

/// Defer to [`ConfigCore::STRICT_MAP_SET`](crate::config::ConfigCore::STRICT_MAP_SET),
/// which is itself permissive by default.
pub struct UseConfig;

impl DuplicateKeyPolicy for UseConfig {
    #[inline(always)]
    fn reject_duplicates<C: ConfigCore>() -> bool {
        C::STRICT_MAP_SET
    }
}

/// A repeated key overwrites the entry decoded for it earlier (last one wins),
/// whatever the configuration says.
pub struct AllowDuplicateKeys;

impl DuplicateKeyPolicy for AllowDuplicateKeys {
    #[inline(always)]
    fn reject_duplicates<C: ConfigCore>() -> bool {
        false
    }
}

/// A repeated key aborts the read with
/// [`ReadError::DuplicateKey`](crate::error::ReadError::DuplicateKey), whatever the
/// configuration says.
///
/// Only constrains decoding; an already-keyed collection cannot encode a duplicate.
pub struct CheckUniqueKeys;

impl DuplicateKeyPolicy for CheckUniqueKeys {
    #[inline(always)]
    fn reject_duplicates<C: ConfigCore>() -> bool {
        true
    }
}

/// Read a length-prefixed sequence of key/value pairs into a map like collection,
/// where `insert` reports whether an entry for that key already existed.
#[cfg(feature = "alloc")]
#[inline]
pub(crate) fn read_kv_seq<'de, K, V, Len, Dup, C, M>(
    mut reader: impl Reader<'de>,
    capacity: impl FnOnce(usize) -> usize,
    make: impl FnOnce(usize) -> M,
    mut insert: impl FnMut(&mut M, K::Dst, V::Dst) -> bool,
) -> ReadResult<M>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    Dup: DuplicateKeyPolicy,
    K: SchemaRead<'de, C>,
    V: SchemaRead<'de, C>,
{
    let len = Len::read_prealloc_check::<(K::Dst, V::Dst)>(reader.by_ref())?;

    macro_rules! read_entries {
        ($reader:expr) => {{
            // Reserve capacity, capped for unique keys; iteration still uses `len`.
            let mut map = make(capacity(len));
            for _ in 0..len {
                let k = K::get($reader.by_ref())?;
                let v = V::get($reader.by_ref())?;
                let replaced = insert(&mut map, k, v);
                if Dup::reject_duplicates::<C>() && replaced {
                    return Err(duplicate_key(type_name::<K::Dst>()));
                }
            }
            map
        }};
    }

    let map = if let (
        TypeMeta::Static { size: key_size, .. },
        TypeMeta::Static {
            size: value_size, ..
        },
    ) = (K::TYPE_META, V::TYPE_META)
    {
        let Some(el_size) = key_size.checked_add(value_size) else {
            return Err(read_length_encoding_overflow("usize::MAX"));
        };
        // SAFETY: `K::TYPE_META` and `V::TYPE_META` specify static sizes, so `len` reads of
        // `(K::Dst, V::Dst)` will consume `el_size * len` bytes, fully consuming the
        // trusted window.
        let mut reader = unsafe { reader.as_trusted_for_seq(len, el_size) }?;
        read_entries!(reader)
    } else {
        read_entries!(reader)
    };

    Ok(map)
}

/// Variant of [`read_kv_seq`] for collections of standalone elements rather than pairs.
#[cfg(feature = "alloc")]
#[inline]
pub(crate) fn read_elem_seq<'de, T, Len, Dup, C, S>(
    mut reader: impl Reader<'de>,
    capacity: impl FnOnce(usize) -> usize,
    make: impl FnOnce(usize) -> S,
    mut insert: impl FnMut(&mut S, T::Dst) -> bool,
) -> ReadResult<S>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    Dup: DuplicateKeyPolicy,
    T: SchemaRead<'de, C>,
{
    let len = Len::read_prealloc_check::<T::Dst>(reader.by_ref())?;

    macro_rules! read_elems {
        ($reader:expr) => {{
            // Reserve capacity, capped for unique keys; iteration still uses `len`.
            let mut set = make(capacity(len));
            for _ in 0..len {
                let present = insert(&mut set, T::get($reader.by_ref())?);
                if Dup::reject_duplicates::<C>() && present {
                    return Err(duplicate_key(type_name::<T::Dst>()));
                }
            }
            set
        }};
    }

    let set = match T::TYPE_META {
        TypeMeta::Static { size, .. } => {
            // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
            // will consume `size * len` bytes, fully consuming the trusted window.
            let mut reader = unsafe { reader.as_trusted_for_seq(len, size) }?;
            read_elems!(reader)
        }
        TypeMeta::Dynamic => read_elems!(reader),
    };

    Ok(set)
}

/// Define a map container schema with a customizable length encoding and
/// [`DuplicateKeyPolicy`].
macro_rules! map_container {
    (
        #[cfg($cfg:meta)]
        $(#[$meta:meta])*
        $name:ident => $target:ident<$key:ident : $($constraint:path)|*, $value:ident
            $(, $state:ident : $($state_constraint:path)|* = $state_default:ty)?>,
        $with_capacity:expr
        $(, $cap_unique_keys:ident)?
    ) => {
        $(#[$meta])*
        #[cfg($cfg)]
        pub struct $name<$key, $value, Len, Dup = UseConfig $(, $state = $state_default)?>(
            PhantomData<($key, $value, Len, Dup $(, $state)?)>,
        );

        #[cfg($cfg)]
        unsafe impl<C: ConfigCore, $key, $value, Len, Dup $(, $state)?> SchemaWrite<C>
            for $name<$key, $value, Len, Dup $(, $state)?>
        where
            Len: SeqLen<C>,
            $key: SchemaWrite<C, Src: Sized>,
            $value: SchemaWrite<C, Src: Sized>,
            $($($state: $state_constraint,)*)?
        {
            type Src = $target<$key::Src, $value::Src $(, $state)?>;

            #[inline]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                size_of_kv_iter::<$key, $value, Len, C>(src.iter())
            }

            #[inline]
            fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
                write_kv_iter_prealloc_check::<$key, $value, Len, C>(writer, src.iter())
            }
        }

        #[cfg($cfg)]
        unsafe impl<'de, C: ConfigCore, $key, $value, Len, Dup $(, $state)?> SchemaRead<'de, C>
            for $name<$key, $value, Len, Dup $(, $state)?>
        where
            Len: SeqLen<C>,
            Dup: DuplicateKeyPolicy,
            $key: SchemaRead<'de, C>,
            $value: SchemaRead<'de, C>,
            $($key::Dst: $constraint,)*
            $($($state: $state_constraint,)*)?
        {
            type Dst = $target<$key::Dst, $value::Dst $(, $state)?>;

            #[inline]
            fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let map = read_kv_seq::<$key, $value, Len, Dup, C, _>(
                    reader,
                    |len| seq_capacity!($key::Dst, len $(, $cap_unique_keys)?),
                    |capacity| $with_capacity(capacity $(, <$state as Default>::default())?),
                    |map, k, v| map.insert(k, v).is_some(),
                )?;
                dst.write(map);
                Ok(())
            }
        }
    };
}

/// [`map_container!`] for set-like collections, which key on the element itself.
macro_rules! set_container {
    (
        #[cfg($cfg:meta)]
        $(#[$meta:meta])*
        $name:ident => $target:ident<$key:ident : $($constraint:path)|*
            $(, $state:ident : $($state_constraint:path)|* = $state_default:ty)?>,
        $with_capacity:expr
        $(, $cap_unique_keys:ident)?
    ) => {
        $(#[$meta])*
        #[cfg($cfg)]
        pub struct $name<$key, Len, Dup = UseConfig $(, $state = $state_default)?>(
            PhantomData<($key, Len, Dup $(, $state)?)>,
        );

        #[cfg($cfg)]
        unsafe impl<C: ConfigCore, $key, Len, Dup $(, $state)?> SchemaWrite<C>
            for $name<$key, Len, Dup $(, $state)?>
        where
            Len: SeqLen<C>,
            $key: SchemaWrite<C, Src: Sized>,
            $($($state: $state_constraint,)*)?
        {
            type Src = $target<$key::Src $(, $state)?>;

            #[inline]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                size_of_elem_iter::<$key, Len, C>(src.iter())
            }

            #[inline]
            fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
                write_elem_iter_prealloc_check::<$key, Len, C>(writer, src.iter())
            }
        }

        #[cfg($cfg)]
        unsafe impl<'de, C: ConfigCore, $key, Len, Dup $(, $state)?> SchemaRead<'de, C>
            for $name<$key, Len, Dup $(, $state)?>
        where
            Len: SeqLen<C>,
            Dup: DuplicateKeyPolicy,
            $key: SchemaRead<'de, C>,
            $($key::Dst: $constraint,)*
            $($($state: $state_constraint,)*)?
        {
            type Dst = $target<$key::Dst $(, $state)?>;

            #[inline]
            fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let set = read_elem_seq::<$key, Len, Dup, C, _>(
                    reader,
                    |len| seq_capacity!($key::Dst, len $(, $cap_unique_keys)?),
                    |capacity| $with_capacity(capacity $(, <$state as Default>::default())?),
                    // `insert` reports whether the value is new, so negate it.
                    |set, k| !set.insert(k),
                )?;
                dst.write(set);
                Ok(())
            }
        }
    };
}

map_container! {
    #[cfg(feature = "std")]
    /// A [`HashMap`](std::collections::HashMap) with a customizable length encoding and
    /// [`DuplicateKeyPolicy`].
    ///
    /// # Examples
    ///
    /// Reject an encoded map that repeats a key, rather than letting the last
    /// entry win:
    ///
    /// ```
    /// # #[cfg(all(feature = "std", feature = "derive"))] {
    /// # use std::collections::HashMap;
    /// # use wincode::{ReadError, containers, len::BincodeLen};
    /// # use wincode_derive::{SchemaWrite, SchemaRead};
    /// #[derive(SchemaWrite, SchemaRead, PartialEq, Debug)]
    /// struct MyStruct {
    ///     #[wincode(with = "containers::HashMap<u32, u64, BincodeLen, containers::CheckUniqueKeys>")]
    ///     map: HashMap<u32, u64>,
    /// }
    ///
    /// let my_struct = MyStruct { map: HashMap::from([(1, 10), (2, 20)]) };
    /// let bytes = wincode::serialize(&my_struct).unwrap();
    /// assert_eq!(my_struct, wincode::deserialize(&bytes).unwrap());
    ///
    /// // The same two entries, but keyed on `1` twice.
    /// let dupes = wincode::serialize(&vec![(1u32, 10u64), (1, 20)]).unwrap();
    /// assert!(matches!(
    ///     wincode::deserialize::<MyStruct>(&dupes),
    ///     Err(ReadError::DuplicateKey(_)),
    /// ));
    /// # }
    /// ```
    HashMap => StdHashMap<K: Hash | Eq, V, S: BuildHasher | Default = StdRandomState>,
    StdHashMap::with_capacity_and_hasher,
    cap_unique_keys
}

map_container! {
    #[cfg(feature = "alloc")]
    /// A [`BTreeMap`](alloc::collections::BTreeMap) with a customizable length encoding and
    /// [`DuplicateKeyPolicy`].
    ///
    /// See [`HashMap`] for an example.
    BTreeMap => AllocBTreeMap<K: Ord, V>,
    |_| AllocBTreeMap::new()
}

set_container! {
    #[cfg(feature = "std")]
    /// A [`HashSet`](std::collections::HashSet) with a customizable length encoding and
    /// [`DuplicateKeyPolicy`].
    ///
    /// A set keys on the element itself, so [`CheckUniqueKeys`] rejects an encoded
    /// sequence that repeats a value.
    ///
    /// See [`HashMap`] for an example.
    HashSet => StdHashSet<K: Hash | Eq, S: BuildHasher | Default = StdRandomState>,
    StdHashSet::with_capacity_and_hasher,
    cap_unique_keys
}

set_container! {
    #[cfg(feature = "alloc")]
    /// A [`BTreeSet`](alloc::collections::BTreeSet) with a customizable length encoding and
    /// [`DuplicateKeyPolicy`].
    ///
    /// See [`HashMap`] for an example.
    BTreeSet => AllocBTreeSet<K: Ord>,
    |_| AllocBTreeSet::new()
}

map_container! {
    #[cfg(all(feature = "indexmap", feature = "std"))]
    /// An [`IndexMap`](indexmap::IndexMap) with a customizable length encoding and
    /// [`DuplicateKeyPolicy`].
    ///
    /// Requires the `std` feature as well as `indexmap`, for the default hasher.
    ///
    /// See [`HashMap`] for an example.
    IndexMap => ExtIndexMap<K: Hash | Eq, V, S: BuildHasher | Default = StdRandomState>,
    ExtIndexMap::with_capacity_and_hasher,
    cap_unique_keys
}

set_container! {
    #[cfg(all(feature = "indexmap", feature = "std"))]
    /// An [`IndexSet`](indexmap::IndexSet) with a customizable length encoding and
    /// [`DuplicateKeyPolicy`].
    ///
    /// Requires the `std` feature as well as `indexmap`, for the default hasher.
    ///
    /// See [`HashMap`] for an example.
    IndexSet => ExtIndexSet<K: Hash | Eq, S: BuildHasher | Default = StdRandomState>,
    ExtIndexSet::with_capacity_and_hasher,
    cap_unique_keys
}

/// Newtype that collects a fallible iterator into `Result<C, E>` while preserving `size_hint`.
///
/// Unlike `collect::<Result<V, E>>()`, which loses the size hint on error, this type
/// drives `V::from_iter` through an adaptor that stops on the first error but keeps
/// `size_hint` accurate so that `V` can preallocate its full expected capacity.
struct ResultPrealloc<T, E>(Result<T, E>);

impl<A, E, V: FromIterator<A>> FromIterator<Result<A, E>> for ResultPrealloc<V, E> {
    fn from_iter<I: IntoIterator<Item = Result<A, E>>>(iter: I) -> ResultPrealloc<V, E> {
        struct Iter<I, E> {
            inner: I,
            error: Option<E>,
        }

        impl<I: Iterator<Item = Result<T, E>>, T, E> Iterator for Iter<I, E> {
            type Item = T;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next()?.map_err(|e| self.error = Some(e)).ok()
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
        }

        let mut iter = Iter {
            inner: iter.into_iter(),
            error: None,
        };
        let result = V::from_iter(&mut iter);
        ResultPrealloc(iter.error.map_or(Ok(result), Err))
    }
}

/// Extension trait that adds [`collect_result_prealloc`](CollectResultExt::collect_result_prealloc)
/// to any fallible iterator, collecting into `Result<B, E>` with preallocation-friendly size hints.
trait CollectResultExt<T, E>: Iterator<Item = Result<T, E>> {
    #[inline]
    fn collect_result_prealloc<B: FromIterator<T>>(self) -> Result<B, E>
    where
        Self: Sized,
    {
        self.collect::<ResultPrealloc<B, E>>().0
    }
}
impl<T, E, I> CollectResultExt<T, E> for I where I: Iterator<Item = Result<T, E>> {}

/// A generic sequence schema for custom collections that implement
/// [`FromIterator`] (for reading) and whose references implement
/// [`IntoIterator`] with an [`ExactSizeIterator`] (for writing).
///
/// Works for both element sequences and key-value maps:
/// - For element collections (sets, ordered sets, etc.) whose reference
///   iterators yield `&T`, the schema for `T` is used directly.
/// - For map like collections whose reference iterators yield `(&K, &V)` pairs,
///   the pair itself acts as the schema (automatically satisfied when `K` and
///   `V` implement `SchemaWrite<C>`).
///
/// Intended for external collection types that cannot have a dedicated
/// schema impl added directly. Unlike [`Vec`], [`VecDeque`], and [`BinaryHeap`], this
/// container relies on the collection's [`FromIterator`] impl rather than
/// writing directly into preallocated memory.
///
/// For manual [`SchemaWrite`] implementations that emit a sequence from an
/// ad-hoc iterator rather than a concrete collection, see
/// [`encode_from_iter_prealloc_check`] (and its check-skipping counterpart
/// [`encode_from_iter`]).
///
/// # Allocation efficiency
///
/// During deserialization, the iterator passed to [`FromIterator`] has a
/// precise [`size_hint`](Iterator::size_hint) matching the number of elements
/// produced, unless a read error is encountered. Collections whose
/// [`FromIterator`] implementation uses the size hint to preallocate capacity
/// will allocate optimally. Collections that do not use it will not benefit.
///
/// # Examples
///
/// ```ignore
/// use some_crate::{IndexSet, MyMap};
/// use wincode::{SchemaRead, SchemaWrite, containers::FromIntoIterator, len::BincodeLen};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// struct MyData {
///     #[wincode(with = "FromIntoIterator<IndexSet<u32>, BincodeLen>")]
///     items: IndexSet<u32>,
///     #[wincode(with = "FromIntoIterator<MyMap<u32, u64>, BincodeLen>")]
///     map: MyMap<u32, u64>,
/// }
/// ```
pub struct FromIntoIterator<Coll, Len>(PhantomData<(Coll, Len)>);

unsafe impl<Coll, Len, C: ConfigCore> SchemaWrite<C> for FromIntoIterator<Coll, Len>
where
    Len: SeqLen<C>,
    Coll: IntoIterator,
    for<'a> &'a Coll: IntoIterator<Item: SchemaWrite<C>, IntoIter: ExactSizeIterator>,
    for<'a> <&'a Coll as IntoIterator>::Item:
        Borrow<<<&'a Coll as IntoIterator>::Item as SchemaWrite<C>>::Src>,
{
    type Src = Coll;

    #[inline]
    fn size_of(src: &Coll) -> WriteResult<usize> {
        size_of_elem_iter::<<&Coll as IntoIterator>::Item, Len, C>(src.into_iter())
    }

    #[inline]
    fn write(writer: impl Writer, src: &Coll) -> WriteResult<()> {
        let iter = src.into_iter();
        Len::prealloc_check::<Coll::Item>(iter.len())?;
        write_elem_iter::<<&Coll as IntoIterator>::Item, Len, C>(writer, iter)
    }
}

unsafe impl<'de, Coll, Len, C: ConfigCore> SchemaRead<'de, C> for FromIntoIterator<Coll, Len>
where
    Len: SeqLen<C>,
    Coll: IntoIterator<Item: SchemaRead<'de, C>>,
    Coll: FromIterator<<Coll::Item as SchemaRead<'de, C>>::Dst>,
{
    type Dst = Coll;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Coll>) -> ReadResult<()> {
        let len =
            Len::read_prealloc_check::<<Coll::Item as SchemaRead<'de, C>>::Dst>(reader.by_ref())?;

        let coll = if let TypeMeta::Static { size, .. } = Coll::Item::TYPE_META {
            // SAFETY: `Item::TYPE_META` specifies a static size, so `len` reads of `Item::Dst`
            // will consume `size * len` bytes, fully consuming the trusted window.
            let mut reader = unsafe { reader.as_trusted_for_seq(len, size) }?;
            (0..len)
                .map(|_| Coll::Item::get(reader.by_ref()))
                .collect_result_prealloc()?
        } else {
            (0..len)
                .map(|_| Coll::Item::get(reader.by_ref()))
                .collect_result_prealloc()?
        };
        dst.write(coll);
        Ok(())
    }
}

/// Decode `slice.len()` items of `T` into contiguous, uninitialized memory.
///
/// Errors if fewer than `slice.len()` items are available in the [`Reader`]
/// or any item fails to decode.
///
/// On success, every slot in `slice` is initialized.
/// On error or panic, any elements that were initialized before failure are
/// dropped, and the remaining slots stay uninitialized.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::containers::decode_into_slice_t;
/// # use wincode::config::DefaultConfig;
/// # type C = DefaultConfig;
/// let data = [1u64, 2, 3, 4, 5, 6];
/// let serialized = wincode::serialize(&data).unwrap();
///
/// let mut dst: Vec<u64> = Vec::with_capacity(6);
///
/// decode_into_slice_t::<u64, C>(
///     &serialized[..],
///     &mut dst.spare_capacity_mut()[..6],
/// )
/// .unwrap();
///
/// unsafe { dst.set_len(6) }
///
/// assert_eq!(dst, data);
/// # }
/// ```
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// # use wincode::containers::decode_into_slice_t;
/// # use wincode::config::DefaultConfig;
/// # type C = DefaultConfig;
/// let data = [1u64, 2, 3, 4, 5, 6];
/// let serialized = wincode::serialize(&data).unwrap();
///
/// let mut dst: Vec<u64> = Vec::with_capacity(7);
///
/// let result = decode_into_slice_t::<u64, C>(
///     &serialized[..],
///     &mut dst.spare_capacity_mut()[..7],
/// );
///
/// // Only 6 elements were serialized.
/// assert!(result.is_err());
/// # }
/// ```
#[inline]
pub fn decode_into_slice_t<'de, T, C>(
    mut reader: impl Reader<'de>,
    slice: &mut [MaybeUninit<T::Dst>],
) -> ReadResult<()>
where
    T: SchemaRead<'de, C>,
    C: ConfigCore,
{
    let base = slice.as_mut_ptr();
    let len = slice.len();
    let mut guard = SliceDropGuard::<T::Dst>::new(base);

    match T::TYPE_META {
        TypeMeta::Static {
            zero_copy: true, ..
        } => {
            // SAFETY: `zero_copy: true` guarantees `T::Dst` is zero-copy eligible
            // (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
            unsafe { reader.copy_into_slice_t(slice) }?
        }
        TypeMeta::Static {
            size,
            zero_copy: false,
        } => {
            // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
            // will consume `size * len` bytes, fully consuming the trusted window.
            let mut reader = unsafe { reader.as_trusted_for_seq(len, size) }?;
            for i in 0..len {
                // SAFETY: `i < len` and `base` is valid for `len` elements.
                let slot = unsafe { &mut *base.add(i) };
                T::read(reader.by_ref(), slot)?;
                guard.inc_len();
            }
        }
        TypeMeta::Dynamic => {
            for i in 0..len {
                // SAFETY: `i < len` and `base` is valid for `len` elements.
                let slot = unsafe { &mut *base.add(i) };
                T::read(reader.by_ref(), slot)?;
                guard.inc_len();
            }
        }
    }

    mem::forget(guard);
    Ok(())
}

/// Encode a sequence of `T` from an iterator into the [`Writer`].
///
/// Writes the sequence length (encoded per `Len`) followed by each item
/// yielded by `src`. This is the encoding counterpart of the full sequence
/// read performed by container types such as [`Vec`]: the produced wire format
/// is identical to serializing a `Vec<T::Src>` (or any other sequence) with the
/// same element type `T`, length encoding `Len`, and configuration `C`.
///
/// `src` is any [`IntoIterator`] whose iterator is an [`ExactSizeIterator`], so
/// a sequence can be encoded directly from a lazily-produced iterator (a range,
/// a `map`/`filter` chain, borrowed views into several sources, …) without
/// first materializing it into a collection.
///
/// # Comparison with [`FromIntoIterator`]
///
/// [`FromIntoIterator`] is a [`with`](crate)-adapter: it plugs an existing
/// collection type that exposes the standard [`IntoIterator`]/[`FromIterator`]
/// trait shape into a derived [`SchemaWrite`]/[`SchemaRead`] impl. Reach for it
/// when you have a concrete container to (de)serialize through a field
/// attribute.
///
/// `encode_from_iter_prealloc_check` is the lower-level building block for
/// *manual* [`SchemaWrite`] implementations: it lets you emit a sequence from an
/// ad-hoc iterator without needing a collection that implements those traits.
///
/// # Preallocation check
///
/// Before encoding, this validates the length against the configured
/// preallocation limit (see [`SeqLen::prealloc_check`]) and returns an error if
/// it would be exceeded. This mirrors [`SeqLen::read_prealloc_check`], which is
/// applied on deserialization, so a wire format produced here is guaranteed to
/// be accepted on read-back under the *same* configuration `C` and length
/// encoding `Len`. This is the recommended entry point; use
/// [`encode_from_iter`] only when the check is undesirable or has already been
/// performed.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// use wincode::config::{Config, DefaultConfig};
/// use wincode::containers::encode_from_iter_prealloc_check;
/// use wincode::io::Writer;
///
/// type C = DefaultConfig;
/// type Len = <C as Config>::LengthEncoding;
///
/// // Encode 0², 1², … 5² straight from a lazy iterator — the sequence is
/// // never materialized into an intermediate `Vec`.
/// let mut buf = Vec::new();
/// encode_from_iter_prealloc_check::<u32, Len, C>(buf.by_ref(), (0u32..6).map(|i| i * i))
///     .unwrap();
///
/// assert_eq!(wincode::deserialize::<Vec<u32>>(&buf).unwrap(), [0, 1, 4, 9, 16, 25]);
/// # }
/// ```
#[cfg(feature = "alloc")]
#[inline]
pub fn encode_from_iter_prealloc_check<T, Len, C>(
    writer: impl Writer,
    src: impl IntoIterator<IntoIter: ExactSizeIterator, Item: Borrow<T::Src>>,
) -> WriteResult<()>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    write_elem_iter_prealloc_check::<T, Len, C>(writer, src.into_iter())
}

/// Like [`encode_from_iter_prealloc_check`], but **skips** the preallocation
/// size check.
///
/// Use this only when the check is undesirable, or when you have already
/// validated the length yourself via [`SeqLen::prealloc_check`]. Because no
/// check is performed here, the produced length may exceed the configured
/// preallocation limit and be rejected on deserialization by
/// [`SeqLen::read_prealloc_check`]; prefer [`encode_from_iter_prealloc_check`]
/// unless you specifically need to bypass the check.
///
/// See [`encode_from_iter_prealloc_check`] for details on the wire format and
/// how this relates to [`FromIntoIterator`].
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// use wincode::config::{Config, DefaultConfig};
/// use wincode::containers::encode_from_iter;
/// use wincode::io::Writer;
/// use wincode::len::SeqLen;
///
/// type C = DefaultConfig;
/// type Len = <C as Config>::LengthEncoding;
///
/// let squares = (0u32..6).map(|i| i * i);
///
/// // The caller is responsible for the preallocation check when using this
/// // variant, so the same configuration accepts the result on deserialization.
/// assert!(<Len as SeqLen<C>>::prealloc_check::<u32>(squares.len()).is_ok());
///
/// let mut buf = Vec::new();
/// encode_from_iter::<u32, Len, C>(buf.by_ref(), squares).unwrap();
///
/// assert_eq!(wincode::deserialize::<Vec<u32>>(&buf).unwrap(), [0, 1, 4, 9, 16, 25]);
/// # }
/// ```
#[inline]
pub fn encode_from_iter<T, Len, C>(
    writer: impl Writer,
    src: impl IntoIterator<IntoIter: ExactSizeIterator, Item: Borrow<T::Src>>,
) -> WriteResult<()>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
{
    write_elem_iter::<T, Len, C>(writer, src.into_iter())
}

#[cfg(all(test, feature = "std"))]
mod keyed_tests {
    use {
        crate::{
            Deserialize, ReadError, Serialize, containers,
            containers::CheckUniqueKeys,
            deserialize,
            len::{BincodeLen, UseIntLen},
            serialize,
        },
        std::collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    };

    /// Two entries keyed on `1`.
    fn dup_key_map_bytes() -> Vec<u8> {
        serialize(&vec![(1u32, 10u64), (1, 20)]).unwrap()
    }

    /// Two identical elements.
    fn dup_elem_set_bytes() -> Vec<u8> {
        serialize(&vec![7u32, 7]).unwrap()
    }

    #[test]
    fn allows_duplicates_by_default() {
        let bytes = dup_key_map_bytes();

        // The default policy matches the plain `HashMap` schema: last entry wins.
        let plain: HashMap<u32, u64> = deserialize(&bytes).unwrap();
        let loose = <containers::HashMap<u32, u64, BincodeLen>>::deserialize(&bytes).unwrap();
        assert_eq!(loose, HashMap::from([(1, 20)]));
        assert_eq!(loose, plain);

        let bytes = dup_elem_set_bytes();
        let plain: HashSet<u32> = deserialize(&bytes).unwrap();
        let loose = <containers::HashSet<u32, BincodeLen>>::deserialize(&bytes).unwrap();
        assert_eq!(loose, HashSet::from([7]));
        assert_eq!(loose, plain);
    }

    #[test]
    fn strict_maps_reject_duplicate_keys() {
        let bytes = dup_key_map_bytes();

        assert!(matches!(
            <containers::HashMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));
        assert!(matches!(
            <containers::BTreeMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));
    }

    #[test]
    fn strict_sets_reject_duplicate_elements() {
        let bytes = dup_elem_set_bytes();

        assert!(matches!(
            <containers::HashSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));
        assert!(matches!(
            <containers::BTreeSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));
    }

    #[test]
    fn strict_decoding_accepts_unique_keys() {
        let map = BTreeMap::from([(1u32, 10u64), (2, 20), (3, 30)]);
        let bytes = serialize(&map).unwrap();
        let strict =
            <containers::BTreeMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes)
                .unwrap();
        assert_eq!(strict, map);

        let set = BTreeSet::from([1u32, 2, 3]);
        let bytes = serialize(&set).unwrap();
        let strict =
            <containers::BTreeSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes).unwrap();
        assert_eq!(strict, set);
    }

    /// Statically sized elements read through a trusted window and dynamic ones do not,
    /// so the check has to hold on both paths.
    #[test]
    fn strict_decoding_covers_dynamically_sized_keys() {
        let bytes = serialize(&vec![("a".to_string(), 1u64), ("a".to_string(), 2)]).unwrap();
        assert!(matches!(
            <containers::BTreeMap<String, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));

        let bytes = serialize(&vec!["a".to_string(), "a".to_string()]).unwrap();
        assert!(matches!(
            <containers::BTreeSet<String, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));
    }

    #[test]
    fn keyed_containers_encode_like_the_plain_schemas() {
        // `BTreeMap`/`BTreeSet` iterate deterministically, so the bytes are comparable.
        let map = BTreeMap::from([(1u32, 10u64), (2, 20)]);
        let container = <containers::BTreeMap<u32, u64, BincodeLen>>::serialize(&map).unwrap();
        assert_eq!(container, serialize(&map).unwrap());
        assert_eq!(container, bincode::serialize(&map).unwrap());

        let set = BTreeSet::from([1u32, 2]);
        let container = <containers::BTreeSet<u32, BincodeLen>>::serialize(&set).unwrap();
        assert_eq!(container, serialize(&set).unwrap());
        assert_eq!(container, bincode::serialize(&set).unwrap());
    }

    #[test]
    fn keyed_containers_customize_the_length_encoding() {
        type ShortMap = containers::BTreeMap<u32, u64, UseIntLen<u16>>;

        let map = BTreeMap::from([(1u32, 10u64), (2, 20)]);
        let bytes = ShortMap::serialize(&map).unwrap();
        assert_eq!(
            bytes.len(),
            size_of::<u16>() + map.len() * (size_of::<u32>() + size_of::<u64>()),
        );
        assert_eq!(ShortMap::deserialize(&bytes).unwrap(), map);

        // The `u16` prefix is not interchangeable with the default `u64` one.
        assert!(<containers::BTreeMap<u32, u64, BincodeLen>>::deserialize(&bytes).is_err());
    }

    /// Nested so that only the configuration-aware `Deserialize` is in scope; the outer
    /// module imports the `DefaultConfig`-only one of the same name.
    mod config_knob {
        use {
            super::{dup_elem_set_bytes, dup_key_map_bytes},
            crate::{
                ReadError,
                config::{DefaultConfig, Deserialize},
                containers::{self, AllowDuplicateKeys, CheckUniqueKeys},
                deserialize,
                len::BincodeLen,
                serialize,
            },
            std::collections::{BTreeMap, BTreeSet, HashMap, HashSet},
        };

        /// A bare `HashMap<u32, u64>` field has no attribute to hang a policy on, so the
        /// configuration has to reach the plain schemas.
        #[test]
        fn config_drives_the_plain_schemas() {
            let strict = DefaultConfig::new().enable_strict_map_set();
            let bytes = dup_key_map_bytes();

            assert_eq!(deserialize::<HashMap<u32, u64>>(&bytes).unwrap().len(), 1);
            assert!(matches!(
                <HashMap<u32, u64>>::deserialize(&bytes, strict),
                Err(ReadError::DuplicateKey(_)),
            ));
            assert!(matches!(
                <BTreeMap<u32, u64>>::deserialize(&bytes, strict),
                Err(ReadError::DuplicateKey(_)),
            ));

            let bytes = dup_elem_set_bytes();
            assert!(matches!(
                <HashSet<u32>>::deserialize(&bytes, strict),
                Err(ReadError::DuplicateKey(_)),
            ));
            assert!(matches!(
                <BTreeSet<u32>>::deserialize(&bytes, strict),
                Err(ReadError::DuplicateKey(_)),
            ));

            // Unique input is unaffected.
            let map = BTreeMap::from([(1u32, 10u64), (2, 20)]);
            let bytes = serialize(&map).unwrap();
            assert_eq!(
                <BTreeMap<u32, u64>>::deserialize(&bytes, strict).unwrap(),
                map,
            );
        }

        /// The knob composes with the rest of the builder in either order.
        #[test]
        fn config_knob_composes() {
            let bytes = dup_key_map_bytes();

            let strict_then_varint = DefaultConfig::new()
                .enable_strict_map_set()
                .with_varint_encoding();
            let varint_then_strict = DefaultConfig::new()
                .with_varint_encoding()
                .enable_strict_map_set();
            let round_tripped_off = varint_then_strict.disable_strict_map_set();

            // Varint changes the encoding, so re-encode under the same configuration.
            let varint_bytes =
                crate::config::serialize(&vec![(1u32, 10u64), (1, 20)], strict_then_varint)
                    .unwrap();

            assert!(matches!(
                <BTreeMap<u32, u64>>::deserialize(&varint_bytes, strict_then_varint),
                Err(ReadError::DuplicateKey(_)),
            ));
            assert!(matches!(
                <BTreeMap<u32, u64>>::deserialize(&varint_bytes, varint_then_strict),
                Err(ReadError::DuplicateKey(_)),
            ));
            assert_eq!(
                <BTreeMap<u32, u64>>::deserialize(&varint_bytes, round_tripped_off)
                    .unwrap()
                    .len(),
                1,
            );

            assert!(matches!(
                <BTreeMap<u32, u64>>::deserialize(
                    &bytes,
                    DefaultConfig::new().enable_strict_map_set(),
                ),
                Err(ReadError::DuplicateKey(_)),
            ));
        }

        /// A named policy overrides the configuration in both directions; the
        /// `UseConfig` default follows it.
        #[test]
        fn field_policy_overrides_the_config() {
            let lenient = DefaultConfig::new();
            let strict = DefaultConfig::new().enable_strict_map_set();
            let bytes = dup_key_map_bytes();

            type Follows = containers::BTreeMap<u32, u64, BincodeLen>;
            type AlwaysStrict = containers::BTreeMap<u32, u64, BincodeLen, CheckUniqueKeys>;
            type AlwaysLenient = containers::BTreeMap<u32, u64, BincodeLen, AllowDuplicateKeys>;

            assert!(Follows::deserialize(&bytes, lenient).is_ok());
            assert!(matches!(
                Follows::deserialize(&bytes, strict),
                Err(ReadError::DuplicateKey(_)),
            ));

            // Explicit policies ignore the configuration.
            assert!(matches!(
                AlwaysStrict::deserialize(&bytes, lenient),
                Err(ReadError::DuplicateKey(_)),
            ));
            assert!(AlwaysLenient::deserialize(&bytes, strict).is_ok());
        }
    }

    #[cfg(feature = "indexmap")]
    #[test]
    fn indexmap_containers_check_uniqueness_and_preserve_order() {
        use indexmap::{IndexMap, IndexSet};

        let bytes = dup_key_map_bytes();
        assert!(matches!(
            <containers::IndexMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes),
            Err(ReadError::DuplicateKey(_)),
        ));
        assert!(matches!(
            <containers::IndexSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(
                &dup_elem_set_bytes()
            ),
            Err(ReadError::DuplicateKey(_)),
        ));

        let map = IndexMap::from_iter([(3u32, 30u64), (1, 10), (2, 20)]);
        let bytes = <containers::IndexMap<u32, u64, BincodeLen>>::serialize(&map).unwrap();
        let decoded =
            <containers::IndexMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes)
                .unwrap();
        assert_eq!(decoded.keys().copied().collect::<Vec<_>>(), vec![3, 1, 2]);

        let set = IndexSet::from_iter([3u32, 1, 2]);
        let bytes = <containers::IndexSet<u32, BincodeLen>>::serialize(&set).unwrap();
        let decoded =
            <containers::IndexSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes).unwrap();
        assert_eq!(decoded.iter().copied().collect::<Vec<_>>(), vec![3, 1, 2]);
    }
}
