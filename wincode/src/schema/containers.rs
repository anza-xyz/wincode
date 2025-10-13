//! This module provides specialized implementations of standard library collection types that
//! provide control over how elements are traversed and initialized (see [`Pod`] and [`Elem`]),
//! as well control over the length encoding (see [`SeqLen`](crate::len::SeqLen)).
//!
//! # Examples
//! Pod-newtype vec with default bincode length encoding:
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode_derive::SchemaWrite;
//! # use wincode::{containers::{self, Pod}};
//! # use serde::Serialize;
//! #[repr(transparent)]
//! #[derive(Serialize, Clone, Copy)]
//! struct Address([u8; 32]);
//!
//! #[derive(Serialize, SchemaWrite)]
//! struct MyStruct {
//!     #[wincode(with = "containers::Vec<Pod<_>>")]
//!     vec: Vec<Address>,
//! }
//!
//! let my_struct = MyStruct {
//!     vec: vec![Address([0; 32]), Address([1; 32])],
//! };
//! let wincode_bytes = wincode::serialize(&my_struct).unwrap();
//! let bincode_bytes = bincode::serialize(&my_struct).unwrap();
//! assert_eq!(wincode_bytes, bincode_bytes);
//! # }
//! ```
//!
//! Raw byte vec with solana short vec length encoding:
//!
//! ```
//! # #[cfg(all(feature = "solana-short-vec", feature = "alloc"))] {
//! # use wincode::{containers::{self, Pod}, len::ShortU16Len};
//! # use wincode_derive::SchemaWrite;
//! # use serde::Serialize;
//! # use solana_short_vec;
//! #[derive(Serialize, SchemaWrite)]
//! struct MyStruct {
//!     #[serde(with = "solana_short_vec")]
//!     #[wincode(with = "containers::Vec<Pod<_>, ShortU16Len>")]
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
//! Vector with non-POD elements and custom length encoding:
//!
//! ```
//! # #[cfg(all(feature = "solana-short-vec", feature = "alloc", feature = "derive"))] {
//! # use wincode_derive::SchemaWrite;
//! # use wincode::{containers::{self, Elem}, len::ShortU16Len};
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
//!     #[wincode(with = "containers::Vec<Elem<Point>, ShortU16Len>")]
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
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
    },
    core::{marker::PhantomData, mem::MaybeUninit, ptr},
};
#[cfg(feature = "alloc")]
use {
    crate::{
        len::{BincodeLen, SeqLen},
        schema::{size_of_elem_iter, size_of_elem_slice, write_elem_iter, write_elem_slice},
        util::type_equal,
    },
    alloc::{boxed::Box as AllocBox, collections, rc::Rc as AllocRc, sync::Arc as AllocArc, vec},
    core::mem::{self, transmute, ManuallyDrop},
};

/// A [`Vec`](std::vec::Vec) with a customizable length encoding and optimized
/// read/write implementation for [`Pod`].
#[cfg(feature = "alloc")]
pub struct Vec<T, Len = BincodeLen>(PhantomData<Len>, PhantomData<T>);

/// A [`VecDeque`](std::collections::VecDeque) with a customizable length encoding and optimized
/// read/write implementation for [`Pod`].
#[cfg(feature = "alloc")]
pub struct VecDeque<T, Len = BincodeLen>(PhantomData<Len>, PhantomData<T>);

/// A [`Box<[T]>`](std::boxed::Box) with a customizable length encoding and optimized
/// read/write implementation for [`Pod`].
///
/// # Examples
///
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
///     #[wincode(with = "containers::Box<[Pod<Address>]>")]
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
pub struct Box<T: ?Sized, Len = BincodeLen>(PhantomData<T>, PhantomData<Len>);

#[cfg(feature = "alloc")]
/// Like [`Box`], for [`Rc`].
pub struct Rc<T: ?Sized, Len = BincodeLen>(PhantomData<T>, PhantomData<Len>);

#[cfg(feature = "alloc")]
/// Like [`Box`], for [`Arc`].
pub struct Arc<T: ?Sized, Len = BincodeLen>(PhantomData<T>, PhantomData<Len>);

/// Indicates that the type is an element of a sequence, composable with [`containers`](self).
///
/// Prefer [`Pod`] for types representable as raw bytes.
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
/// Use [`Elem`] with [`containers`](self) that aren't comprised of POD.
///
/// This can be useful outside of sequences as well, for example on newtype structs
/// containing byte arrays with `#[repr(transparent)]`.
///
/// # Safety
///
/// - The type must allow any bit pattern (e.g., no `bool`s, no `char`s, etc.)
/// - If used on a compound type like a struct or tuple, all fields must be also be `Pod` and its
///   layout must be guaranteed (via `#[repr(transparent)]` or `#[repr(C)]`).
/// - Must not contain references or pointers (includes types like `Vec` or `Box`).
///     - Note, you may use `Pod` *inside* types like `Vec` or `Box`, e.g., `Vec<Pod<T>>` or `Box<[Pod<T>]>`,
///       but specifying `Pod` on the outer type is invalid.
///
/// # Notes on composing with collections
///
/// It is perfectly valid to specify `Pod` within the definition of struct newtypes:
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// use wincode::{containers::Pod, SchemaWrite, SchemaRead};
///
/// #[derive(SchemaWrite, SchemaRead)]
/// #[repr(transparent)]
/// struct Address(#[wincode(with = "Pod<_>")] [u8; 32]);
/// # }
/// ```
///
/// And you may be tempted to use it like the following and assume you're getting an optimized read/write implementation:
/// ```
/// # #[cfg(feature = "derive")] {
/// use wincode::{containers::Pod, SchemaWrite, SchemaRead};
///
/// #[derive(SchemaWrite, SchemaRead)]
/// #[repr(transparent)]
/// struct Address(#[wincode(with = "Pod<_>")] [u8; 32]);
///
/// #[derive(SchemaWrite, SchemaRead)]
/// struct MyStruct {
///     addresses: Vec<Address>,
/// }
/// # }
/// ```
///
/// But this is not quite what you want. While individual reads of `Address` will be optimized, reads of `Vec<Address>`
/// will still visit `Address`es individually. This is because the blanket implementation of alloc `Vec` cannot inspect the
/// "PODness" of its inner type (unless that type is strictly `u8`), and must assume it should visit element-wise. The
/// rule of thumb is that when you want optimized implementations when using collection types, you should explicitly opt
/// into the [`container`](self) version and explicitly annotate with `Pod` (unless the inner type is strictly `u8` --
/// blanket implementations _will_ detect this).
///
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// use wincode::{containers::{self, Pod}, SchemaWrite, SchemaRead};
///
/// #[derive(Clone, Copy)]
/// #[repr(transparent)]
/// struct Address([u8; 32]);
///
/// #[derive(SchemaWrite, SchemaRead)]
/// struct MyStruct {
///     #[wincode(with = "containers::Vec<Pod<_>>")]
///     addresses: Vec<Address>,
/// }
/// # }
/// ```
///
/// # Examples
///
/// A repr-transparent newtype struct with a byte array:
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

impl<T> SchemaWrite for Pod<T>
where
    T: Copy + 'static,
{
    type Src = T;

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(size_of::<T>())
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        // SAFETY: `T` is plain ol' data.
        unsafe { Ok(writer.write_t(src)?) }
    }
}

impl<T> SchemaRead<'_> for Pod<T>
where
    T: Copy + 'static,
{
    type Dst = T;

    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // SAFETY: `T` is plain ol' data.
        unsafe { Ok(reader.read_t(dst)?) }
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for Vec<Elem<T>, Len>
where
    Len: SeqLen,
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = vec::Vec<T::Src>;

    #[inline(always)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, Len>(src)
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_slice::<T, Len>(writer, src)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T, Len> SchemaRead<'de> for Vec<Elem<T>, Len>
where
    Len: SeqLen,
    T: SchemaRead<'de>,
{
    type Dst = vec::Vec<T::Dst>;

    /// Read a sequence of `T::Dst`s from `reader` into `dst`.
    ///
    /// This provides a `*mut T::Dst` for each slot in the allocated Vec
    /// to facilitate in-place writing of Vec memory.
    ///
    /// Prefer [`Vec<Pod<T>, Len>`] for sequences representable as raw bytes.
    ///
    /// # Safety
    ///
    /// - `T::read` must properly initialize elements.
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        if type_equal::<T::Dst, u8>() {
            return <Vec<Pod<u8>, Len>>::read(reader, unsafe {
                transmute::<&mut MaybeUninit<vec::Vec<T::Dst>>, &mut MaybeUninit<vec::Vec<u8>>>(dst)
            });
        }

        let len = Len::read::<T::Dst>(reader)?;
        let mut vec: vec::Vec<T::Dst> = vec::Vec::with_capacity(len);
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

        dst.write(vec);
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for Vec<Pod<T>, Len>
where
    Len: SeqLen,
    T: Copy + 'static,
{
    type Src = vec::Vec<T>;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        Ok(Len::write_bytes_needed(src.len())? + size_of_val(src.as_slice()))
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        Len::write(writer, src.len())?;
        // SAFETY: Caller ensures `src` is plain ol' data.
        unsafe { Ok(writer.write_slice_t(src.as_slice())?) }
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaRead<'_> for Vec<Pod<T>, Len>
where
    Len: SeqLen,
    T: Copy + 'static,
{
    type Dst = vec::Vec<T>;

    /// Read a sequence of bytes or a sequence of fixed length byte arrays from the reader into `dst`.
    ///
    /// This reads the entire sequence at once, rather than yielding each element to the caller.
    ///
    /// Should be used with types representable by raw bytes, like `Vec<u8>` or `Vec<[u8; N]>`.
    ///
    /// # Safety
    ///
    /// - `T` must be plain ol' data, valid for writes of `size_of::<T>()` bytes.
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = Len::read::<T>(reader)?;
        let mut vec = vec::Vec::with_capacity(len);
        let spare_capacity = vec.spare_capacity_mut();
        unsafe { reader.read_slice_t(spare_capacity)? };
        // SAFETY: Caller ensures `T` is plain ol' data and can be initialized by raw byte reads.
        unsafe { vec.set_len(len) }
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
        impl<T, Len> SchemaWrite for $container<[Pod<T>], Len>
        where
            Len: SeqLen,
            T: Copy + 'static,
        {
            type Src = $target<[T]>;

            #[inline]
            #[allow(clippy::arithmetic_side_effects)]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
                Ok(Len::write_bytes_needed(src.len())? + size_of_val(&src[..]))
            }

            #[inline]
            fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
                Len::write(writer, src.len())?;
                // SAFETY: Caller ensures `T` is plain ol' data.
                unsafe { Ok(writer.write_slice_t(&src[..])?) }
            }
        }

        #[cfg(feature = "alloc")]
        impl<T, Len> SchemaRead<'_> for $container<[Pod<T>], Len>
        where
            Len: SeqLen,
            T: Copy + 'static,
        {
            type Dst = $target<[T]>;

            #[inline(always)]
            fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                struct DropGuard<T>(*mut [MaybeUninit<T>]);
                impl<T> Drop for DropGuard<T> {
                    fn drop(&mut self) {
                        drop(unsafe { $target::from_raw(self.0) });
                    }
                }

                let len = Len::read::<T>(reader)?;
                let mem = <$target<[T]>>::new_uninit_slice(len);
                let ptr = $target::into_raw(mem) as *mut [MaybeUninit<T>];
                let guard = DropGuard(ptr);

                unsafe {
                    reader.read_slice_t(&mut *ptr)?;
                }

                mem::forget(guard);

                // SAFETY: Caller ensures `T` is plain ol' data and can be initialized by raw byte reads.
                unsafe { dst.write($target::from_raw(ptr).assume_init()) };
                Ok(())
            }
        }

        #[cfg(feature = "alloc")]
        impl<T, Len> SchemaWrite for $container<[Elem<T>], Len>
        where
            Len: SeqLen,
            T: SchemaWrite,
            T::Src: Sized,
        {
            type Src = $target<[T::Src]>;

            #[inline(always)]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                size_of_elem_slice::<T, Len>(src)
            }

            #[inline(always)]
            fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
                write_elem_slice::<T, Len>(writer, src)
            }
        }

        #[cfg(feature = "alloc")]
        impl<'de, T, Len> SchemaRead<'de> for $container<[Elem<T>], Len>
        where
            Len: SeqLen,
            T: SchemaRead<'de>,
        {
            type Dst = $target<[T::Dst]>;

            #[inline(always)]
            fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                if type_equal::<T::Dst, u8>() {
                    return <$container<[Pod<u8>], Len>>::read(reader, unsafe {
                        transmute::<
                            &mut MaybeUninit<$target<[T::Dst]>>,
                            &mut MaybeUninit<$target<[u8]>>,
                        >(dst)
                    });
                }

                struct DropGuard<T> {
                    inner: ManuallyDrop<SliceDropGuard<T>>,
                    fat: *mut [MaybeUninit<T>],
                }

                impl<T> DropGuard<T> {
                    #[inline(always)]
                    fn new(fat: *mut [MaybeUninit<T>], raw: *mut MaybeUninit<T>) -> Self {
                        Self {
                            inner: ManuallyDrop::new(SliceDropGuard::new(raw)),
                            // We need to store the fat pointer to deallocate the container.
                            fat,
                        }
                    }
                }

                impl<T> Drop for DropGuard<T> {
                    #[inline]
                    fn drop(&mut self) {
                        unsafe {
                            // Drop the initialized elements first.
                            ManuallyDrop::drop(&mut self.inner);
                            // Deallocate the container last.
                            drop($target::from_raw(self.fat));
                        }
                    }
                }

                let len = Len::read::<T::Dst>(reader)?;
                let mem = $target::<[T::Dst]>::new_uninit_slice(len);
                let fat = $target::into_raw(mem) as *mut [MaybeUninit<T::Dst>];
                let raw_base = unsafe { (*fat).as_mut_ptr() };
                let mut guard: DropGuard<T::Dst> = DropGuard::new(fat, raw_base);

                for i in 0..len {
                    let slot = unsafe { &mut *raw_base.add(i) };
                    T::read(reader, slot)?;
                    guard.inner.inc_len();
                }

                mem::forget(guard);

                unsafe { dst.write($target::from_raw(fat).assume_init()) };
                Ok(())
            }
        }
    };
}

impl_heap_slice!(Box => AllocBox);
impl_heap_slice!(Rc => AllocRc);
impl_heap_slice!(Arc => AllocArc);

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for VecDeque<Pod<T>, Len>
where
    Len: SeqLen,
    T: Copy + 'static,
{
    type Src = collections::VecDeque<T>;

    #[inline(always)]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        Ok(Len::write_bytes_needed(src.len())? + size_of::<T>() * src.len())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        Len::write(writer, src.len())?;
        let (front, back) = src.as_slices();
        unsafe {
            // SAFETY:
            // - Caller ensures given `T` is plain ol' data.
            // - `front` and `back` are valid non-overlapping slices.
            writer.write_slice_t(front)?;
            writer.write_slice_t(back)?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaRead<'_> for VecDeque<Pod<T>, Len>
where
    Len: SeqLen,
    T: Copy + 'static,
{
    type Dst = collections::VecDeque<T>;

    #[inline(always)]
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // Leverage the contiguous read optimization of `Vec`.
        // From<Vec<T>> for VecDeque<T> is basically free.
        let vec = <Vec<Pod<T>, Len>>::get(reader)?;
        dst.write(vec.into());
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for VecDeque<Elem<T>, Len>
where
    Len: SeqLen,
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = collections::VecDeque<T::Src>;

    #[inline(always)]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        if type_equal::<T::Src, u8>() {
            return <VecDeque<Pod<u8>, Len>>::size_of(unsafe {
                transmute::<&collections::VecDeque<T::Src>, &collections::VecDeque<u8>>(value)
            });
        }
        size_of_elem_iter::<T, Len>(value.iter())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        if type_equal::<T::Src, u8>() {
            return <VecDeque<Pod<u8>, Len>>::write(writer, unsafe {
                transmute::<&collections::VecDeque<T::Src>, &collections::VecDeque<u8>>(src)
            });
        }
        write_elem_iter::<T, Len>(writer, src.iter())
    }
}

#[cfg(feature = "alloc")]
impl<'de, T, Len> SchemaRead<'de> for VecDeque<Elem<T>, Len>
where
    Len: SeqLen,
    T: SchemaRead<'de>,
{
    type Dst = collections::VecDeque<T::Dst>;

    #[inline(always)]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // Leverage the contiguous read optimization of `Vec`.
        // From<Vec<T>> for VecDeque<T> is basically free.
        let vec = <Vec<Elem<T>, Len>>::get(reader)?;
        dst.write(vec.into());
        Ok(())
    }
}

#[cfg(feature = "alloc")]
/// A [`BinaryHeap`](alloc::collections::BinaryHeap) with a customizable length encoding and optimized
/// read/write implementation for [`Pod`].
pub struct BinaryHeap<T, Len = BincodeLen>(PhantomData<Len>, PhantomData<T>);

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for BinaryHeap<Elem<T>, Len>
where
    Len: SeqLen,
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = collections::BinaryHeap<T::Src>;

    #[inline(always)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, Len>(src.as_slice())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_slice::<T, Len>(writer, src.as_slice())
    }
}

#[cfg(feature = "alloc")]
impl<'de, T, Len> SchemaRead<'de> for BinaryHeap<Elem<T>, Len>
where
    Len: SeqLen,
    T: SchemaRead<'de>,
    T::Dst: Ord,
{
    type Dst = collections::BinaryHeap<T::Dst>;

    #[inline(always)]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let vec = <Vec<Elem<T>, Len>>::get(reader)?;
        // Leverage the vec impl.
        dst.write(collections::BinaryHeap::from(vec));
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for BinaryHeap<Pod<T>, Len>
where
    T: Copy + 'static,
    Len: SeqLen,
{
    type Src = collections::BinaryHeap<T>;

    #[inline(always)]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        Ok(Len::write_bytes_needed(src.len())? + size_of_val(src.as_slice()))
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> WriteResult<()> {
        Len::write(writer, src.len())?;
        // SAFETY: Caller ensures `T` is plain ol' data.
        unsafe { writer.write_slice_t(src.as_slice())? }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaRead<'_> for BinaryHeap<Pod<T>, Len>
where
    Len: SeqLen,
    T: Ord + Copy + 'static,
{
    type Dst = collections::BinaryHeap<T>;

    #[inline(always)]
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let vec = <Vec<Pod<T>, Len>>::get(reader)?;
        // Leverage the vec impl.
        dst.write(collections::BinaryHeap::from(vec));
        Ok(())
    }
}
