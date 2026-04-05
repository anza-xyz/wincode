//! This module provides specialized implementations of standard library collection types that
//! provide control over the length encoding (see [`SeqLen`](crate::len::SeqLen)), as well
//! as special case opt-in raw-copy overrides (see [`pod_wrapper!`]).
//!
//! # Examples
//! Raw byte vec with solana short vec length encoding:
//!
//! ```
//! # #[cfg(all(feature = "solana-short-vec", feature = "alloc"))] {
//! # use wincode::{containers::self, len::ShortU16};
//! # use wincode_derive::SchemaWrite;
//! # use serde::Serialize;
//! # use solana_short_vec;
//! #[derive(Serialize, SchemaWrite)]
//! struct MyStruct {
//!     #[serde(with = "solana_short_vec")]
//!     #[wincode(with = "containers::Vec<_, ShortU16>")]
//!     vec: Vec<u8>,
//! }
//!
//! let my_struct = MyStruct {
//!     vec: vec![1, 2, 3],
//! };
//! let wincode_bytes = wincode::serialize(&my_struct).unwrap();
//! let bincode_bytes = bincode::serialize(&my_struct).unwrap();
//! assert_eq!(wincode_bytes, bincode_bytes);
//! # }
//! ```
//!
//! Vector with struct elements and custom length encoding:
//!
//! ```
//! # #[cfg(all(feature = "solana-short-vec", feature = "alloc", feature = "derive"))] {
//! # use wincode_derive::SchemaWrite;
//! # use wincode::{containers::self, len::ShortU16};
//! # use serde::Serialize;
//! # use solana_short_vec;
//! #[derive(Serialize, SchemaWrite)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! #[derive(Serialize, SchemaWrite)]
//! struct MyStruct {
//!     #[serde(with = "solana_short_vec")]
//!     #[wincode(with = "containers::Vec<Point, ShortU16>")]
//!     vec: Vec<Point>,
//! }
//!
//! let my_struct = MyStruct {
//!     vec: vec![Point { x: 1, y: 2 }, Point { x: 3, y: 4 }],
//! };
//! let wincode_bytes = wincode::serialize(&my_struct).unwrap();
//! let bincode_bytes = bincode::serialize(&my_struct).unwrap();
//! assert_eq!(wincode_bytes, bincode_bytes);
//! # }
//! ```
#[cfg(all(feature = "alloc", target_has_atomic = "ptr"))]
use alloc::sync::Arc as AllocArc;
use {
    crate::{TypeMeta, config::ConfigCore, error::ReadResult, io::Reader, schema::SchemaRead},
    core::{
        mem::{self, MaybeUninit},
        ptr,
    },
};
#[cfg(feature = "alloc")]
use {
    crate::{
        context,
        error::{ReadError, WriteResult},
        io::Writer,
        len::SeqLen,
        schema::{
            SchemaReadContext, SchemaWrite, size_of_elem_iter, size_of_elem_slice, write_elem_iter,
            write_elem_iter_prealloc_check, write_elem_slice_prealloc_check,
        },
    },
    alloc::{boxed::Box as AllocBox, collections, rc::Rc as AllocRc, vec},
    core::marker::PhantomData,
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
/// # #[cfg(all(feature = "alloc", feature = "derive", feature = "solana-short-vec"))] {
/// # use wincode::{containers, len::ShortU16};
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// # use serde::{Serialize, Deserialize};
/// # use std::array;
/// #[derive(Serialize, SchemaWrite, Clone, Copy)]
/// #[repr(transparent)]
/// struct Address([u8; 32]);
///
/// #[derive(Serialize, SchemaWrite)]
/// struct MyStruct {
///     #[serde(with = "solana_short_vec")]
///     #[wincode(with = "containers::Box<[Address], ShortU16>")]
///     address: Box<[Address]>
/// }
///
/// let my_struct = MyStruct {
///     address: vec![Address(array::from_fn(|i| i as u8)); 10].into_boxed_slice(),
/// };
/// let wincode_bytes = wincode::serialize(&my_struct).unwrap();
/// let bincode_bytes = bincode::serialize(&my_struct).unwrap();
/// assert_eq!(wincode_bytes, bincode_bytes);
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
            let needed = Len::write_bytes_needed_prealloc_check::<T>(src.len())? + src.len() * size;
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

        write_elem_iter::<T, Len, C>(writer, src.iter())
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

/// Iterator that reads `T` items from a [`Reader`] via [`SchemaRead::get`],
/// storing the first error for later inspection.
///
/// Unlike `collect::<Result<C, _>>()` this preserves `remaining` in `size_hint`
/// so that collections can preallocate the expected capacity.
#[cfg(feature = "alloc")]
struct SchemaReadIter<'de, T, C, R> {
    reader: R,
    remaining: usize,
    error: Option<ReadError>,
    #[allow(clippy::type_complexity)]
    _marker: PhantomData<fn() -> (&'de (), T, C)>,
}

#[cfg(feature = "alloc")]
impl<'de, T, C, R> SchemaReadIter<'de, T, C, R>
where
    T: SchemaRead<'de, C>,
    C: ConfigCore,
    R: Reader<'de>,
{
    fn collect_result<Coll: FromIterator<T::Dst>>(reader: R, remaining: usize) -> ReadResult<Coll> {
        let mut iter = Self {
            reader,
            remaining,
            error: None,
            _marker: PhantomData,
        };
        let coll = Coll::from_iter(&mut iter);
        match iter.error {
            Some(e) => Err(e),
            None => Ok(coll),
        }
    }
}

#[cfg(feature = "alloc")]
impl<'de, T, C, R> Iterator for SchemaReadIter<'de, T, C, R>
where
    T: SchemaRead<'de, C>,
    C: ConfigCore,
    R: Reader<'de>,
{
    type Item = T::Dst;

    #[inline]
    fn next(&mut self) -> Option<T::Dst> {
        self.remaining = self.remaining.checked_sub(1)?;
        match T::get(self.reader.by_ref()) {
            Ok(v) => Some(v),
            Err(e) => {
                self.error = Some(e);
                self.remaining = 0;
                None
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

/// A generic sequence schema for custom collections that implement
/// [`FromIterator`] (for reading) and whose references implement
/// [`IntoIterator`] with an [`ExactSizeIterator`] (for writing).
///
/// Intended for external collection types that cannot have a dedicated
/// schema impl added directly. Unlike [`Vec`], [`VecDeque`], and [`BinaryHeap`], this
/// container relies on the collection's [`FromIterator`] impl rather than
/// writing directly into preallocated memory.
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
/// use some_crate::IndexSet;
/// use wincode::{SchemaRead, SchemaWrite, containers::Seq, len::BincodeLen};
///
/// #[derive(SchemaRead, SchemaWrite)]
/// struct MyData {
///     #[wincode(with = "Seq<IndexSet<u32>, BincodeLen>")]
///     items: IndexSet<u32>,
/// }
/// ```
#[cfg(feature = "alloc")]
pub struct Seq<Coll, Len>(PhantomData<(Coll, Len)>);

#[cfg(feature = "alloc")]
unsafe impl<Coll, Len, C: ConfigCore> SchemaWrite<C> for Seq<Coll, Len>
where
    Len: SeqLen<C>,
    Coll: IntoIterator,
    Coll::Item: SchemaWrite<C>,
    for<'a> &'a Coll: IntoIterator<Item = &'a <Coll::Item as SchemaWrite<C>>::Src>,
    for<'a> <&'a Coll as IntoIterator>::IntoIter: ExactSizeIterator,
{
    type Src = Coll;

    #[inline]
    fn size_of(src: &Coll) -> WriteResult<usize> {
        size_of_elem_iter::<Coll::Item, Len, C>(src.into_iter())
    }

    #[inline]
    fn write(writer: impl Writer, src: &Coll) -> WriteResult<()> {
        write_elem_iter_prealloc_check::<Coll::Item, Len, C>(writer, src.into_iter())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, Coll, Len, C: ConfigCore> SchemaRead<'de, C> for Seq<Coll, Len>
where
    Len: SeqLen<C>,
    Coll: IntoIterator,
    Coll::Item: SchemaRead<'de, C>,
    Coll: FromIterator<<Coll::Item as SchemaRead<'de, C>>::Dst>,
{
    type Dst = Coll;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Coll>) -> ReadResult<()> {
        let len =
            Len::read_prealloc_check::<<Coll::Item as SchemaRead<'de, C>>::Dst>(reader.by_ref())?;
        let result = if let TypeMeta::Static { size, .. } = <Coll::Item as SchemaRead<C>>::TYPE_META
        {
            #[allow(clippy::arithmetic_side_effects)]
            // SAFETY: `Coll::Item::TYPE_META` specifies a static size, so `len` reads will
            // consume `size * len` bytes, fully consuming the trusted window.
            let reader = unsafe { reader.as_trusted_for(size * len) }?;
            SchemaReadIter::<Coll::Item, C, _>::collect_result(reader, len)
        } else {
            SchemaReadIter::<Coll::Item, C, _>::collect_result(reader, len)
        };
        dst.write(result?);
        Ok(())
    }
}

/// A generic key-value sequence schema for custom map-like collections that
/// implement [`FromIterator<(K::Dst, V::Dst)>`](FromIterator) (for reading)
/// and whose references implement [`IntoIterator`] yielding
/// `(&K::Src, &V::Src)` pairs with an [`ExactSizeIterator`] (for writing).
///
/// Intended for external map types that cannot have a dedicated schema impl
/// added directly.
///
/// # Allocation efficiency
///
/// During deserialization, the iterator passed to [`FromIterator`] has a
/// precise [`size_hint`](Iterator::size_hint) matching the number of pairs to
/// be read, unless a read error is encountered. Collections whose
/// [`FromIterator`] implementation uses the size hint to preallocate capacity
/// will allocate optimally. Collections that do not use it will not benefit.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// use wincode::{Deserialize, Serialize, containers::SeqKv, len::BincodeLen};
///
/// #[derive(PartialEq, Debug)]
/// struct MyMap<K, V>(Vec<(K, V)>);
///
/// impl<K, V> FromIterator<(K, V)> for MyMap<K, V> {
///     fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
///         MyMap(iter.into_iter().collect())
///     }
/// }
///
/// struct MyMapIter<'a, K, V>(core::slice::Iter<'a, (K, V)>);
///
/// impl<'a, K, V> Iterator for MyMapIter<'a, K, V> {
///     type Item = (&'a K, &'a V);
///     fn next(&mut self) -> Option<Self::Item> { self.0.next().map(|(k, v)| (k, v)) }
///     fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
/// }
///
/// impl<'a, K, V> ExactSizeIterator for MyMapIter<'a, K, V> {}
///
/// impl<'a, K, V> IntoIterator for &'a MyMap<K, V> {
///     type Item = (&'a K, &'a V);
///     type IntoIter = MyMapIter<'a, K, V>;
///     fn into_iter(self) -> Self::IntoIter { MyMapIter(self.0.iter()) }
/// }
///
/// let data: MyMap<u32, u64> = [(1, 10), (2, 20)].into_iter().collect();
/// let bytes = <SeqKv<MyMap<u32, u64>, u32, u64, BincodeLen>>::serialize(&data).unwrap();
/// let out: MyMap<u32, u64> =
///     <SeqKv<MyMap<u32, u64>, u32, u64, BincodeLen>>::deserialize(&bytes).unwrap();
/// assert_eq!(data, out);
/// # }
/// ```
#[cfg(feature = "alloc")]
pub struct SeqKv<Coll, K, V, Len>(PhantomData<(Coll, K, V, Len)>);

#[cfg(feature = "alloc")]
unsafe impl<Coll, K, V, Len, C: ConfigCore> SchemaWrite<C> for SeqKv<Coll, K, V, Len>
where
    Len: SeqLen<C>,
    K: SchemaWrite<C>,
    V: SchemaWrite<C>,
    for<'a> &'a Coll: IntoIterator<Item = (&'a K::Src, &'a V::Src)>,
    for<'a> <&'a Coll as IntoIterator>::IntoIter: ExactSizeIterator,
{
    type Src = Coll;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Coll) -> WriteResult<usize> {
        let mut src = src.into_iter();
        if let (TypeMeta::Static { size: ks, .. }, TypeMeta::Static { size: vs, .. }) = (
            <K as SchemaWrite<C>>::TYPE_META,
            <V as SchemaWrite<C>>::TYPE_META,
        ) {
            return Ok(<Len>::write_bytes_needed(src.len())? + (ks + vs) * src.len());
        }
        Ok(<Len>::write_bytes_needed(src.len())?
            + src.try_fold(0usize, |acc, (k, v)| -> WriteResult<usize> {
                Ok(acc + <K>::size_of(k)? + <V>::size_of(v)?)
            })?)
    }

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn write(writer: impl Writer, src: &Coll) -> WriteResult<()> {
        let src = src.into_iter();
        <Len>::prealloc_check::<(K, V)>(src.len())?;
        let mut writer = writer;
        if let (TypeMeta::Static { size: ks, .. }, TypeMeta::Static { size: vs, .. }) = (
            <K as SchemaWrite<C>>::TYPE_META,
            <V as SchemaWrite<C>>::TYPE_META,
        ) {
            let needed = <Len>::write_bytes_needed(src.len())? + (ks + vs) * src.len();
            // SAFETY: `needed` is the size of the encoded length plus the sizes of the key-value
            // pairs. `Len::write` and `len` writes of `(K::Src, V::Src)` will write `needed` bytes,
            // fully initializing the trusted window.
            let mut writer = unsafe { writer.as_trusted_for(needed) }?;
            <Len>::write(writer.by_ref(), src.len())?;
            for (k, v) in src {
                <K>::write(writer.by_ref(), k)?;
                <V>::write(writer.by_ref(), v)?;
            }
            writer.finish()?;
            return Ok(());
        }

        <Len>::write(writer.by_ref(), src.len())?;
        for (k, v) in src {
            <K>::write(writer.by_ref(), k)?;
            <V>::write(writer.by_ref(), v)?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, Coll, K, V, Len, C: ConfigCore> SchemaRead<'de, C> for SeqKv<Coll, K, V, Len>
where
    Len: SeqLen<C>,
    K: SchemaRead<'de, C>,
    V: SchemaRead<'de, C>,
    Coll: FromIterator<(K::Dst, V::Dst)>,
{
    type Dst = Coll;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Coll>) -> ReadResult<()> {
        let len = Len::read_prealloc_check::<(K::Dst, V::Dst)>(reader.by_ref())?;
        let result = if let TypeMeta::Static { size, .. } = <(K, V) as SchemaRead<C>>::TYPE_META {
            #[allow(clippy::arithmetic_side_effects)]
            // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
            // will consume `size * len` bytes, fully consuming the trusted window.
            let reader = unsafe { reader.as_trusted_for(size * len) }?;
            SchemaReadIter::<(K, V), C, _>::collect_result(reader, len)
        } else {
            SchemaReadIter::<(K, V), C, _>::collect_result(reader, len)
        };
        dst.write(result?);
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
            #[allow(clippy::arithmetic_side_effects)]
            // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
            // will consume `size * len` bytes, fully consuming the trusted window.
            let mut reader = unsafe { reader.as_trusted_for(size * len) }?;
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
