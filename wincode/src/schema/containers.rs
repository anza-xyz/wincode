//! This module provides specialized implementations of standard library collection types that
//! provide control over the length encoding (see [`SeqLen`](crate::len::SeqLen)), as well
//! as special case opt-in raw-copy overrides (see [`Pod`]).
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
use {
    crate::{
        config::{ConfigCore, ZeroCopy},
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
        TypeMeta,
    },
    core::{marker::PhantomData, mem::MaybeUninit, ptr},
};
#[cfg(feature = "alloc")]
use {
    crate::{
        len::SeqLen,
        schema::{
            size_of_elem_iter, size_of_elem_slice, write_elem_iter, write_elem_slice_prealloc_check,
        },
    },
    alloc::{boxed::Box as AllocBox, collections, rc::Rc as AllocRc, sync::Arc as AllocArc, vec},
    core::mem::{self, ManuallyDrop},
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

#[cfg(feature = "alloc")]
/// Like [`Box`], for [`Arc`].
pub struct Arc<T: ?Sized, Len>(PhantomData<T>, PhantomData<Len>);

/// Indicates that the type is an element of a sequence, composable with [`containers`](self).
///
/// Prefer [`Pod`] for types representable as raw bytes.
#[deprecated(
    since = "0.2.0",
    note = "Elem is no longer needed for container usage. Use `T` directly instead."
)]
pub struct Elem<T>(PhantomData<T>);

/// Indicates that the type is represented by raw bytes and does not have any invalid bit patterns.
///
/// By opting into `Pod`, you are telling wincode that it can serialize and deserialize a type
/// with a single memcpy -- it wont pay attention to things like struct layout, endianness, or anything
/// else that would require validity or bit pattern checks. This is a very strong claim to make,
/// so be sure that your type adheres to those requirements.
///
/// Composable with sequence [`containers`](self) or compound types (structs, tuples) for
/// an optimized read/write implementation.
///
///
/// This can be useful outside of sequences as well, for example on newtype structs
/// containing byte arrays with `#[repr(transparent)]`.
///
/// ---
/// 💡 **Note:** as of `wincode` `0.2.0`, `Pod` is no longer needed for types that wincode can determine
/// are "Pod-safe".
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
/// You'll really only need to reach for [`Pod`] when dealing with foreign types for which you cannot
/// derive `SchemaWrite` or `SchemaRead`. Or you're in a controlled scenario where you explicitly
/// want to avoid endianness or layout checks.
///
/// # Safety
///
/// - The type must allow any bit pattern (e.g., no `bool`s, no `char`s, etc.)
/// - If used on a compound type like a struct, all fields must be also be `Pod`, its
///   layout must be guaranteed (via `#[repr(transparent)]` or `#[repr(C)]`), and the struct
///   must not have any padding.
/// - Must not contain references or pointers (includes types like `Vec` or `Box`).
///     - Note, you may use `Pod` *inside* types like `Vec` or `Box`, e.g., `Vec<Pod<T>>` or `Box<[Pod<T>]>`,
///       but specifying `Pod` on the outer type is invalid.
///
/// # Examples
///
/// A repr-transparent newtype struct containing a byte array where you cannot derive `SchemaWrite` or `SchemaRead`:
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// # use wincode::{containers::{self, Pod}};
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// # use serde::{Serialize, Deserialize};
/// # use std::array;
/// #[derive(Serialize, Deserialize, Clone, Copy)]
/// #[repr(transparent)]
/// struct Address([u8; 32]);
///
/// #[derive(Serialize, Deserialize, SchemaWrite, SchemaRead)]
/// struct MyStruct {
///     #[wincode(with = "Pod<_>")]
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
pub struct Pod<T: Copy + 'static>(PhantomData<T>);

// SAFETY:
// - By using `Pod`, user asserts that the type is zero-copy, given the contract of Pod:
//   - The type's in‑memory representation is exactly its serialized bytes.
//   - It can be safely initialized by memcpy (no validation, no endianness/layout work).
//   - Does not contain references or pointers.
unsafe impl<T, C: ConfigCore> ZeroCopy<C> for Pod<T> where T: Copy + 'static {}

unsafe impl<T, C: ConfigCore> SchemaWrite<C> for Pod<T>
where
    T: Copy + 'static,
{
    type Src = T;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: size_of::<T>(),
        zero_copy: true,
    };

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(size_of::<T>())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        // SAFETY: `T` is plain ol' data.
        unsafe { Ok(writer.write_t(src)?) }
    }
}

unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for Pod<T>
where
    T: Copy + 'static,
{
    type Dst = T;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: size_of::<T>(),
        zero_copy: true,
    };

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // SAFETY: `T` is plain ol' data.
        unsafe { Ok(reader.copy_into_t(dst)?) }
    }
}

// Provide `SchemaWrite` implementation for `Elem<T>` for backwards compatibility.
//
// Container impls use blanket implementations over `T` where `T` is `SchemaWrite`,
// so this preserves existing behavior, such that `Elem<T>` behaves exactly like `T`.
#[allow(deprecated)]
unsafe impl<T, C: ConfigCore> SchemaWrite<C> for Elem<T>
where
    T: SchemaWrite<C>,
{
    type Src = T::Src;

    const TYPE_META: TypeMeta = T::TYPE_META;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        T::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        T::write(writer, src)
    }
}

// Provide `SchemaRead` implementation for `Elem<T>` for backwards compatibility.
//
// Container impls use blanket implementations over `T` where `T` is `SchemaRead`,
// so this preserves existing behavior, such that `Elem<T>` behaves exactly like `T`.
#[allow(deprecated)]
unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for Elem<T>
where
    T: SchemaRead<'de, C>,
{
    type Dst = T::Dst;

    const TYPE_META: TypeMeta = T::TYPE_META;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        T::read(reader, dst)
    }
}

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
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
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

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = Len::read_prealloc_check::<T::Dst>(reader)?;
        let mut vec: vec::Vec<T::Dst> = vec::Vec::with_capacity(len);

        match T::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => {
                let spare_capacity = vec.spare_capacity_mut();
                // SAFETY: T::Dst is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                unsafe { reader.copy_into_slice_t(spare_capacity)? };
                // SAFETY: `copy_into_slice_t` fills the entire spare capacity or errors.
                unsafe { vec.set_len(len) };
            }
            TypeMeta::Static {
                size,
                zero_copy: false,
            } => {
                let mut ptr = vec.as_mut_ptr().cast::<MaybeUninit<T::Dst>>();
                #[allow(clippy::arithmetic_side_effects)]
                // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
                // will consume `size * len` bytes, fully consuming the trusted window.
                let mut reader = unsafe { reader.as_trusted_for(size * len) }?;
                for i in 0..len {
                    T::read(&mut reader, unsafe { &mut *ptr })?;
                    unsafe {
                        ptr = ptr.add(1);
                        #[allow(clippy::arithmetic_side_effects)]
                        // i <= len
                        vec.set_len(i + 1);
                    }
                }
            }
            TypeMeta::Dynamic => {
                let mut ptr = vec.as_mut_ptr().cast::<MaybeUninit<T::Dst>>();
                for i in 0..len {
                    T::read(reader, unsafe { &mut *ptr })?;
                    unsafe {
                        ptr = ptr.add(1);
                        #[allow(clippy::arithmetic_side_effects)]
                        // i <= len
                        vec.set_len(i + 1);
                    }
                }
            }
        }

        dst.write(vec);
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
        self.initialized_len += 1;
    }
}

impl<T> Drop for SliceDropGuard<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.ptr.cast::<T>(),
                self.initialized_len,
            ));
        }
    }
}

macro_rules! impl_heap_slice {
    ($container:ident => $target:ident) => {
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
            fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
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
                reader: &mut impl Reader<'de>,
                dst: &mut MaybeUninit<Self::Dst>,
            ) -> ReadResult<()> {
                /// Drop guard for `TypeMeta::Static { zero_copy: true }` types.
                ///
                /// In this case we do not need to drop items individually, as
                /// the container will be initialized by a single memcpy.
                struct DropGuardRawCopy<T>(*mut [MaybeUninit<T>]);
                impl<T> Drop for DropGuardRawCopy<T> {
                    #[inline]
                    fn drop(&mut self) {
                        // SAFETY:
                        // - `self.0` is a valid pointer to the container created
                        //   by `$target::into_raw`.
                        // - `drop` is only called in this drop guard, and the drop guard
                        //   is forgotten if reading succeeds.
                        let container = unsafe { $target::from_raw(self.0) };
                        drop(container);
                    }
                }

                /// Drop guard for `TypeMeta::Static { zero_copy: false } | TypeMeta::Dynamic` types.
                ///
                /// In this case we need to drop items individually, as
                /// the container will be initialized by a series of reads.
                struct DropGuardElemCopy<T> {
                    inner: ManuallyDrop<SliceDropGuard<T>>,
                    fat: *mut [MaybeUninit<T>],
                }

                impl<T> DropGuardElemCopy<T> {
                    #[inline(always)]
                    fn new(fat: *mut [MaybeUninit<T>], raw: *mut MaybeUninit<T>) -> Self {
                        Self {
                            inner: ManuallyDrop::new(SliceDropGuard::new(raw)),
                            // We need to store the fat pointer to deallocate the container.
                            fat,
                        }
                    }
                }

                impl<T> Drop for DropGuardElemCopy<T> {
                    #[inline]
                    fn drop(&mut self) {
                        // SAFETY: `ManuallyDrop::drop` is only called in this drop guard.
                        unsafe {
                            // Drop the initialized elements first.
                            ManuallyDrop::drop(&mut self.inner);
                        }

                        // SAFETY:
                        // - `self.fat` is a valid pointer to the container created with `$target::into_raw`.
                        // - `drop` is only called in this drop guard, and the drop guard is forgotten if read succeeds.
                        let container = unsafe { $target::from_raw(self.fat) };
                        drop(container);
                    }
                }

                let len = Len::read_prealloc_check::<T::Dst>(reader)?;
                let mem = $target::<[T::Dst]>::new_uninit_slice(len);
                let fat = $target::into_raw(mem) as *mut [MaybeUninit<T::Dst>];

                match T::TYPE_META {
                    TypeMeta::Static {
                        zero_copy: true, ..
                    } => {
                        let guard = DropGuardRawCopy(fat);
                        // SAFETY: `fat` is a valid pointer to the container created with `$target::into_raw`.
                        let dst = unsafe { &mut *fat };
                        // SAFETY: T is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                        unsafe { reader.copy_into_slice_t(dst)? };
                        mem::forget(guard);
                    }
                    TypeMeta::Static {
                        size,
                        zero_copy: false,
                    } => {
                        // SAFETY: `fat` is a valid pointer to the container created with `$target::into_raw`.
                        let raw_base = unsafe { (*fat).as_mut_ptr() };
                        let mut guard: DropGuardElemCopy<T::Dst> =
                            DropGuardElemCopy::new(fat, raw_base);

                        // SAFETY: `T::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
                        // will consume `size * len` bytes, fully consuming the trusted window.
                        #[allow(clippy::arithmetic_side_effects)]
                        let reader = &mut unsafe { reader.as_trusted_for(size * len) }?;
                        for i in 0..len {
                            // SAFETY:
                            // - `raw_base` is a valid pointer to the container created with `$target::into_raw`.
                            // - The container is initialized with capacity for `len` elements, and `i` is guaranteed to be
                            //   less than `len`.
                            let slot = unsafe { &mut *raw_base.add(i) };
                            T::read(reader, slot)?;
                            guard.inner.inc_len();
                        }

                        mem::forget(guard);
                    }
                    TypeMeta::Dynamic => {
                        // SAFETY: `fat` is a valid pointer to the container created with `$target::into_raw`.
                        let raw_base = unsafe { (*fat).as_mut_ptr() };
                        let mut guard: DropGuardElemCopy<T::Dst> =
                            DropGuardElemCopy::new(fat, raw_base);

                        for i in 0..len {
                            // SAFETY:
                            // - `raw_base` is a valid pointer to the container created with `$target::into_raw`.
                            // - The container is initialized with capacity for `len` elements, and `i` is guaranteed to be
                            //   less than `len`.
                            let slot = unsafe { &mut *raw_base.add(i) };
                            T::read(reader, slot)?;
                            guard.inner.inc_len();
                        }

                        mem::forget(guard);
                    }
                }

                // SAFETY:
                // - `fat` is a valid pointer to the container created with `$target::into_raw`.
                // - the pointer memory is only deallocated in the drop guard, and the drop guard
                //   is forgotten if reading succeeds.
                let container = unsafe { $target::from_raw(fat) };
                // SAFETY: `container` is fully initialized if read succeeds.
                let container = unsafe { container.assume_init() };

                dst.write(container);
                Ok(())
            }
        }
    };
}

impl_heap_slice!(Box => AllocBox);
impl_heap_slice!(Rc => AllocRc);
impl_heap_slice!(Arc => AllocArc);

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
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
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
            let writer = &mut unsafe { writer.as_trusted_for(needed) }?;

            Len::write(writer, src.len())?;
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
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
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
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let vec = <Vec<T, Len>>::get(reader)?;
        // Leverage the vec impl.
        dst.write(collections::BinaryHeap::from(vec));
        Ok(())
    }
}
