//! This module provides specialized "container" types that can be used to opt
//! into optimized read/write implementations or specialized length encodings.
//!
//! # Examples
//! Raw byte vec with default bincode length encoding:
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode_derive::SchemaWrite;
//! # use wincode::{containers::{self, Pod}};
//! # use serde::Serialize;
//! #[derive(Serialize, SchemaWrite)]
//! struct MyStruct {
//!     #[wincode(with = "containers::Vec<Pod<_>>")]
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
        error::Result,
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
    },
    core::{marker::PhantomData, mem::MaybeUninit},
};
#[cfg(feature = "alloc")]
use {
    crate::{
        len::{BincodeLen, SeqLen},
        schema::{size_of_elem_iter, write_elem_iter},
    },
    alloc::{boxed::Box as AllocBox, collections, rc::Rc, sync::Arc, vec},
    core::ptr,
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
/// # use wincode::{containers::{self, BoxedSlice, Pod}};
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// # use serde::{Serialize, Deserialize};
/// # use std::array;
/// #[derive(Serialize, Deserialize, Clone, Copy)]
/// #[repr(transparent)]
/// struct Address([u8; 32]);
///
/// #[derive(Serialize, Deserialize, SchemaWrite, SchemaRead)]
/// struct MyStruct {
///     #[wincode(with = "containers::BoxedSlice<Pod<Address>>")]
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
pub struct BoxedSlice<T, Len = BincodeLen>(PhantomData<T>, PhantomData<Len>);

#[cfg(feature = "alloc")]
/// Like [`BoxedSlice`], for [`Rc`].
pub struct RcSlice<T, Len = BincodeLen>(PhantomData<T>, PhantomData<Len>);

#[cfg(feature = "alloc")]
/// Like [`BoxedSlice`], for [`Arc`].
pub struct ArcSlice<T, Len = BincodeLen>(PhantomData<T>, PhantomData<Len>);

/// Indicates that the type is an element of a sequence, composable with [`containers`](self).
///
/// Prefer [`Pod`] for types representable as raw bytes.
pub struct Elem<T>(PhantomData<T>);

/// Indicates that the type is represented by raw bytes, composable with sequence [`containers`](self)
/// or compound types (structs, tuples) for an optimized read/write implementation.
///
/// Use [`Elem`] with [`containers`](self) that aren't comprised of POD.
///
/// This can be useful outside of sequences as well, for example on newtype structs
/// containing byte arrays / vectors with `#[repr(transparent)]`.
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
/// #[derive(Serialize, Deserialize)]
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
pub struct Pod<T>(PhantomData<T>);

impl<T> SchemaWrite for Pod<T> {
    type Src = T;

    #[inline]
    fn size_of(_src: &Self::Src) -> Result<usize> {
        Ok(size_of::<T>())
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        // SAFETY: `T` is plain ol' data.
        unsafe { writer.write_t(src) }
    }
}

impl<T> SchemaRead<'_> for Pod<T> {
    type Dst = T;

    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        // SAFETY: `T` is plain ol' data.
        unsafe { reader.read_t(dst) }
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
    fn size_of(src: &Self::Src) -> Result<usize> {
        size_of_elem_iter::<T, Len>(src.iter())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        write_elem_iter::<T, Len>(writer, src.iter())
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
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let len = Len::size_hint_cautious::<T::Dst>(reader)?;
        let mut vec = vec::Vec::with_capacity(len);
        // Get a raw pointer to the Vec memory to facilitate in-place writing.
        let capacity = vec.spare_capacity_mut();
        for (i, slot) in capacity.iter_mut().enumerate() {
            // Yield the current slot to the caller.
            if let Err(e) = T::read(reader, slot) {
                // SAFETY: we've read at least `i` elements.
                unsafe { vec.set_len(i) };
                return Err(e);
            }
        }
        // SAFETY: Caller ensures `T::read` properly initializes elements.
        unsafe { vec.set_len(len) }
        dst.write(vec);
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for Vec<Pod<T>, Len>
where
    Len: SeqLen,
{
    type Src = vec::Vec<T>;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        Ok(Len::bytes_needed(src.len())? + size_of_val(src.as_slice()))
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        Len::encode_len(writer, src.len())?;
        // SAFETY: Caller ensures `src` is plain ol' data.
        unsafe { writer.write_slice_t(src.as_slice()) }
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaRead<'_> for Vec<Pod<T>, Len>
where
    Len: SeqLen,
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
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let len = Len::size_hint_cautious::<T>(reader)?;
        let mut vec = vec::Vec::with_capacity(len);
        let spare_capacity = vec.spare_capacity_mut();
        unsafe { reader.read_slice_t(spare_capacity)? };
        // SAFETY: Caller ensures `T` is plain ol' data and can be initialized by raw byte reads.
        unsafe { vec.set_len(len) }
        dst.write(vec);
        Ok(())
    }
}

macro_rules! impl_heap_slice {
    ($container:ident => $target:ident) => {
        #[cfg(feature = "alloc")]
        impl<T, Len> SchemaWrite for $container<Pod<T>, Len>
        where
            Len: SeqLen,
        {
            type Src = $target<[T]>;

            #[inline]
            fn size_of(src: &Self::Src) -> Result<usize> {
                Ok(Len::bytes_needed(src.len())? + size_of_val(&src[..]))
            }

            #[inline]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                Len::encode_len(writer, src.len())?;
                // SAFETY: Caller ensures `T` is plain ol' data.
                unsafe { writer.write_slice_t(&src[..]) }
            }
        }

        #[cfg(feature = "alloc")]
        impl<T, Len> SchemaRead<'_> for $container<Pod<T>, Len>
        where
            Len: SeqLen,
        {
            type Dst = $target<[T]>;

            #[inline(always)]
            fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                let len = Len::size_hint_cautious::<T>(reader)?;
                let mem = <$target<[T]>>::new_uninit_slice(len);
                let ptr = $target::into_raw(mem) as *mut [MaybeUninit<T>];

                unsafe {
                    if let Err(e) = reader.read_slice_t(&mut *ptr) {
                        drop($target::from_raw(ptr));
                        return Err(e);
                    }
                }

                // SAFETY: Caller ensures `T` is plain ol' data and can be initialized by raw byte reads.
                unsafe { dst.write($target::from_raw(ptr).assume_init()) };
                Ok(())
            }
        }

        #[cfg(feature = "alloc")]
        impl<T, Len> SchemaWrite for $container<Elem<T>, Len>
        where
            Len: SeqLen,
            T: SchemaWrite,
            T::Src: Sized,
        {
            type Src = $target<[T::Src]>;

            #[inline(always)]
            fn size_of(src: &Self::Src) -> Result<usize> {
                size_of_elem_iter::<T, Len>(src.iter())
            }

            #[inline(always)]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                write_elem_iter::<T, Len>(writer, src.iter())
            }
        }

        #[cfg(feature = "alloc")]
        impl<'de, T, Len> SchemaRead<'de> for $container<Elem<T>, Len>
        where
            Len: SeqLen,
            T: SchemaRead<'de>,
        {
            type Dst = $target<[T::Dst]>;

            #[inline(always)]
            fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                let len = Len::size_hint_cautious::<T::Dst>(reader)?;
                let mem = <$target<[T::Dst]>>::new_uninit_slice(len);
                let ptr = $target::into_raw(mem) as *mut [MaybeUninit<T::Dst>];

                for (i, slot) in unsafe { &mut (*ptr) }.iter_mut().enumerate() {
                    if let Err(e) = T::read(reader, slot) {
                        // SAFETY: we've read and initialized at least `i` elements.
                        unsafe {
                            // use drop for [T::Dst]
                            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                                ptr.cast::<T::Dst>(),
                                i,
                            ));
                        }
                        return Err(e);
                    }
                }
                unsafe { dst.write($target::from_raw(ptr).assume_init()) };
                Ok(())
            }
        }
    };
}

impl_heap_slice!(BoxedSlice => AllocBox);
impl_heap_slice!(RcSlice => Rc);
impl_heap_slice!(ArcSlice => Arc);

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for VecDeque<Pod<T>, Len>
where
    Len: SeqLen,
{
    type Src = collections::VecDeque<T>;

    #[inline(always)]
    fn size_of(src: &Self::Src) -> Result<usize> {
        Ok(Len::bytes_needed(src.len())? + size_of::<T>() * src.len())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        Len::encode_len(writer, src.len())?;
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
{
    type Dst = collections::VecDeque<T>;

    #[inline(always)]
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let mut vec = MaybeUninit::uninit();
        // Leverage the contiguous read optimization of `Vec`.
        // From<Vec<T>> for VecDeque<T> is basically free.
        <Vec<Pod<T>, Len>>::read(reader, &mut vec)?;

        // SAFETY: The given `SchemaRead` must properly initialize the dst.
        unsafe { dst.write(vec.assume_init().into()) };
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
    fn size_of(value: &Self::Src) -> Result<usize> {
        size_of_elem_iter::<T, Len>(value.iter())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
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
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let mut vec = MaybeUninit::uninit();
        // Leverage the contiguous read optimization of `Vec`.
        // From<Vec<T>> for VecDeque<T> is basically free.
        <Vec<Elem<T>, Len>>::read(reader, &mut vec)?;

        // SAFETY: The given `SchemaRead` must properly initialize the dst.
        unsafe { dst.write(vec.assume_init().into()) };

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
    fn size_of(src: &Self::Src) -> Result<usize> {
        size_of_elem_iter::<T, Len>(src.iter())
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        write_elem_iter::<T, Len>(writer, src.iter())
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
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let mut vec = MaybeUninit::uninit();
        // Leverage the vec impl.
        <Vec<Elem<T>, Len>>::read(reader, &mut vec)?;
        dst.write(collections::BinaryHeap::from(unsafe { vec.assume_init() }));
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaWrite for BinaryHeap<Pod<T>, Len>
where
    Len: SeqLen,
{
    type Src = collections::BinaryHeap<T>;

    #[inline(always)]
    fn size_of(src: &Self::Src) -> Result<usize> {
        Ok(Len::bytes_needed(src.len())? + size_of_val(src.as_slice()))
    }

    #[inline(always)]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        Len::encode_len(writer, src.len())?;
        // SAFETY: Caller ensures `T` is plain ol' data.
        unsafe { writer.write_slice_t(src.as_slice())? }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T, Len> SchemaRead<'_> for BinaryHeap<Pod<T>, Len>
where
    Len: SeqLen,
    T: Ord,
{
    type Dst = collections::BinaryHeap<T>;

    #[inline(always)]
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let mut vec = MaybeUninit::uninit();
        // Leverage the vec impl.
        <Vec<Pod<T>, Len>>::read(reader, &mut vec)?;
        dst.write(collections::BinaryHeap::from(unsafe { vec.assume_init() }));
        Ok(())
    }
}
