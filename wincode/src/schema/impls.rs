//! Blanket implementations for std types.
//!
//! Because the blanket implementations must be entirely general (e.g., we
//! need to support `Vec<T>` for any `T`), we can't make any assumptions about
//! the "Plain Old Data" nature of `T`, so all sequences will treat constituent
//! elements of `T` as opaque. Of course users can use `std::vec::Vec<Pod<T>>`,
//! which will certainly speed things up for POD elements of sequences, but
//! the optimization will only be _per_ element.
//!
//! Additionally, we have to assume [`BincodeLen`] for all sequences, because
//! there is no way to specify a different length encoding without one of the
//! [`containers`].
#[cfg(feature = "std")]
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};
#[cfg(feature = "alloc")]
use {
    crate::containers::{self, Elem},
    alloc::{
        boxed::Box,
        collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque},
        rc::Rc,
        string::String,
        sync::Arc,
        vec::Vec,
    },
};
use {
    crate::{
        error::{
            invalid_bool_encoding, invalid_tag_encoding, invalid_utf8_encoding,
            pointer_sized_decode_error, Error, Result,
        },
        io::{Reader, Writer},
        len::{BincodeLen, SeqLen},
        schema::{size_of_elem_iter, write_elem_iter, SchemaRead, SchemaWrite},
    },
    core::{
        mem::{transmute, MaybeUninit},
        ptr,
    },
};

macro_rules! impl_int {
    ($type:ty) => {
        impl SchemaWrite for $type {
            type Src = $type;

            #[inline(always)]
            fn size_of(_src: &Self::Src) -> Result<usize> {
                Ok(size_of::<$type>())
            }

            #[inline(always)]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                #[cfg(target_endian = "little")]
                {
                    // SAFETY: int is plain ol' data.
                    unsafe { writer.write_t(src)? };
                }
                // bincode defaults to little endian encoding.
                #[cfg(target_endian = "big")]
                {
                    // SAFETY: int is plain ol' data.
                    unsafe { writer.write_t(&src.to_le_bytes())? };
                }
                Ok(())
            }
        }

        impl SchemaRead<'_> for $type {
            type Dst = $type;

            #[inline(always)]
            fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                #[cfg(target_endian = "little")]
                {
                    // SAFETY: integer is plain ol' data.
                    unsafe { reader.read_t(dst) }?;
                }
                // bincode defaults to little endian encoding.
                #[cfg(target_endian = "big")]
                {
                    let val = <$type>::from_le_bytes(unsafe { reader.get_t() }?);
                    dst.write(val);
                }

                Ok(())
            }
        }
    };

    ($type:ty as $cast:ty) => {
        impl SchemaWrite for $type {
            type Src = $type;

            #[inline]
            fn size_of(_src: &Self::Src) -> Result<usize> {
                Ok(size_of::<$cast>())
            }

            #[inline]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                let src = *src as $cast;
                // bincode defaults to little endian encoding.
                // noop on LE machines.
                unsafe {
                    // SAFETY: int is plain ol' data.
                    writer.write_t(&src.to_le_bytes())?;
                }
                Ok(())
            }
        }

        impl SchemaRead<'_> for $type {
            type Dst = $type;

            #[inline]
            fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                // SAFETY: integer is plain ol' data.
                let casted = unsafe { reader.get_t::<$cast>() }?;
                let val = <$type>::from_le(
                    casted
                        .try_into()
                        .map_err(|_| pointer_sized_decode_error())?,
                );

                dst.write(val);

                Ok(())
            }
        }
    };
}

impl_int!(u16);
impl_int!(i16);
impl_int!(u32);
impl_int!(i32);
impl_int!(u64);
impl_int!(i64);
impl_int!(u128);
impl_int!(i128);
impl_int!(usize as u64);
impl_int!(isize as i64);

macro_rules! impl_pod {
    ($type:ty) => {
        impl SchemaWrite for $type {
            type Src = $type;

            #[inline]
            fn size_of(_src: &Self::Src) -> Result<usize> {
                Ok(size_of::<$type>())
            }

            #[inline(always)]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                // SAFETY: `$type` is plain ol' data.
                unsafe { writer.write_t(src) }
            }
        }

        impl SchemaRead<'_> for $type {
            type Dst = $type;

            #[inline]
            fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                // SAFETY: `$type` is plain ol' data.
                unsafe { reader.read_t(dst) }
            }
        }
    };
}

impl_pod!(u8);
impl_pod!(i8);

impl SchemaWrite for bool {
    type Src = bool;

    #[inline]
    fn size_of(_src: &Self::Src) -> Result<usize> {
        Ok(size_of::<u8>())
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        unsafe { writer.write_t(&(*src as u8)) }
    }
}

impl SchemaRead<'_> for bool {
    type Dst = bool;

    #[inline]
    fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        // SAFETY: u8 is plain ol' data.
        let byte = unsafe { reader.get_t::<u8>() }?;
        match byte {
            0 => {
                dst.write(false);
            }
            1 => {
                dst.write(true);
            }
            _ => return Err(invalid_bool_encoding(byte)),
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<T> SchemaWrite for Vec<T>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = Vec<T::Src>;

    #[inline]
    fn size_of(value: &Self::Src) -> Result<usize> {
        <containers::Vec<Elem<T>, BincodeLen>>::size_of(value)
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        <containers::Vec<Elem<T>, BincodeLen>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Vec<T>
where
    T: SchemaRead<'de>,
{
    type Dst = Vec<T::Dst>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        <containers::Vec<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
impl<T> SchemaWrite for VecDeque<T>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = VecDeque<T::Src>;

    #[inline]
    fn size_of(value: &Self::Src) -> Result<usize> {
        <containers::VecDeque<Elem<T>, BincodeLen>>::size_of(value)
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        <containers::VecDeque<Elem<T>, BincodeLen>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for VecDeque<T>
where
    T: SchemaRead<'de>,
{
    type Dst = VecDeque<T::Dst>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        <containers::VecDeque<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}

impl<T> SchemaWrite for [T]
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = [T::Src];

    #[inline]
    fn size_of(value: &Self::Src) -> Result<usize> {
        size_of_elem_iter::<T, BincodeLen>(value.iter())
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        write_elem_iter::<T, BincodeLen>(writer, value.iter())
    }
}

impl<'de, T, const N: usize> SchemaRead<'de> for [T; N]
where
    T: SchemaRead<'de>,
{
    type Dst = [T::Dst; N];

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        // SAFETY: MaybeUninit<[T::Dst; N]> trivially converts to [MaybeUninit<T::Dst>; N].
        let dst =
            unsafe { transmute::<&mut MaybeUninit<Self::Dst>, &mut [MaybeUninit<T::Dst>; N]>(dst) };

        for (i, slot) in dst.iter_mut().enumerate() {
            if let Err(e) = T::read(reader, slot) {
                // SAFETY: we've read at least `i` elements and assume T::read properly initializes the elements.
                unsafe {
                    // use drop for [T::Dst]
                    ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                        dst.as_mut_ptr().cast::<T::Dst>(),
                        i,
                    ));
                }
                return Err(e);
            }
        }
        Ok(())
    }
}

impl<T, const N: usize> SchemaWrite for [T; N]
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = [T::Src; N];

    #[inline]
    fn size_of(value: &Self::Src) -> Result<usize> {
        value
            .iter()
            .map(T::size_of)
            .try_fold(0, |acc, x| Ok::<_, Error>(acc + x?))
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        for item in value {
            T::write(writer, item)?;
        }
        Ok(())
    }
}

impl<'de, T> SchemaRead<'de> for Option<T>
where
    T: SchemaRead<'de>,
{
    type Dst = Option<T::Dst>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let variant = u8::get(reader)?;
        match variant {
            0 => {
                dst.write(Option::None);
            }
            1 => {
                let mut value = MaybeUninit::uninit();
                T::read(reader, &mut value)?;
                // SAFETY:
                // - `T::read` must properly initialize the `T::Dst`.
                unsafe {
                    dst.write(Option::Some(value.assume_init()));
                }
            }
            _ => return Err(invalid_tag_encoding(variant as usize)),
        }

        Ok(())
    }
}

impl<T> SchemaWrite for Option<T>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = Option<T::Src>;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        match src {
            Option::Some(value) => Ok(1 + T::size_of(value)?),
            Option::None => Ok(1),
        }
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        match value {
            Option::Some(value) => {
                u8::write(writer, &1)?;
                T::write(writer, value)
            }
            Option::None => u8::write(writer, &0),
        }
    }
}

impl<'a, T> SchemaWrite for &'a T
where
    T: SchemaWrite,
    T: ?Sized,
{
    type Src = &'a T::Src;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        T::size_of(*src)
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        T::write(writer, *value)
    }
}

macro_rules! impl_heap_container {
    ($container:ident) => {
        #[cfg(feature = "alloc")]
        impl<T> SchemaWrite for $container<T>
        where
            T: SchemaWrite,
        {
            type Src = $container<T::Src>;

            #[inline]
            fn size_of(src: &Self::Src) -> Result<usize> {
                T::size_of(src)
            }

            #[inline]
            fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
                T::write(writer, value)
            }
        }

        #[cfg(feature = "alloc")]
        impl<'de, T> SchemaRead<'de> for $container<T>
        where
            T: SchemaRead<'de>,
        {
            type Dst = $container<T::Dst>;

            #[inline]
            fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                let mem: $container<MaybeUninit<T::Dst>> = $container::new_uninit();
                let ptr = $container::into_raw(mem) as *mut MaybeUninit<T::Dst>;
                if let Err(e) = T::read(reader, unsafe { &mut *ptr }) {
                    drop(unsafe { $container::from_raw(ptr) });
                    return Err(e);
                }
                unsafe {
                    // SAFETY: `T::read` must properly initialize the `T::Dst`.
                    dst.write($container::from_raw(ptr).assume_init());
                }
                Ok(())
            }
        }
    };
}

impl_heap_container!(Box);
impl_heap_container!(Rc);
impl_heap_container!(Arc);

#[cfg(feature = "alloc")]
impl<T> SchemaWrite for Box<[T]>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = Box<[T::Src]>;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        <containers::BoxedSlice<Elem<T>, BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        <containers::BoxedSlice<Elem<T>, BincodeLen>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
impl<T> SchemaWrite for Rc<[T]>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = Rc<[T::Src]>;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        <containers::RcSlice<Elem<T>, BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        <containers::RcSlice<Elem<T>, BincodeLen>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
impl<T> SchemaWrite for Arc<[T]>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = Arc<[T::Src]>;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        <containers::ArcSlice<Elem<T>, BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut Writer, value: &Self::Src) -> Result<()> {
        <containers::ArcSlice<Elem<T>, BincodeLen>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Box<[T]>
where
    T: SchemaRead<'de>,
{
    type Dst = Box<[T::Dst]>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        <containers::BoxedSlice<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Rc<[T]>
where
    T: SchemaRead<'de>,
{
    type Dst = Rc<[T::Dst]>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        <containers::RcSlice<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Arc<[T]>
where
    T: SchemaRead<'de>,
{
    type Dst = Arc<[T::Dst]>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        <containers::ArcSlice<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}

impl SchemaWrite for str {
    type Src = str;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        Ok(<BincodeLen>::bytes_needed(src.len())? + src.len())
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        <BincodeLen>::encode_len(writer, src.len())?;
        writer.write_exact(src.as_bytes())
    }
}

#[cfg(feature = "alloc")]
impl SchemaWrite for String {
    type Src = String;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        <str>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        <str>::write(writer, src)
    }
}

impl<'de> SchemaRead<'de> for &'de str {
    type Dst = &'de str;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let len = <BincodeLen>::size_hint_cautious::<u8>(reader)?;
        let bytes = reader.read_borrowed(len)?;
        match core::str::from_utf8(bytes) {
            Ok(s) => {
                dst.write(s);
                Ok(())
            }
            Err(e) => Err(invalid_utf8_encoding(e)),
        }
    }
}

#[cfg(feature = "alloc")]
impl SchemaRead<'_> for String {
    type Dst = String;

    #[inline]
    fn read(reader: &mut Reader<'_>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let len = <BincodeLen>::size_hint_cautious::<u8>(reader)?;
        match String::from_utf8(reader.read_borrowed(len)?.to_vec()) {
            Ok(s) => {
                dst.write(s);
                Ok(())
            }
            Err(e) => Err(invalid_utf8_encoding(e.utf8_error())),
        }
    }
}

/// Implement `SchemaWrite` and `SchemaRead` for types that may be iterated over sequentially.
///
/// Generally this should only be used on types for which we cannot provide an optimized implementation,
/// and where the most optimal implementation is simply iterating over the type to write or collecting
/// to read -- typically non-contiguous sequences like `HashMap` or `BTreeMap` (or their set variants).
macro_rules! impl_seq {
    ($feature: literal, $target: ident<$key: ident : $($constraint:path)|*, $value: ident>) => {
        #[cfg(feature = $feature)]
        impl<$key, $value> SchemaWrite for $target<$key, $value>
        where
            $key: SchemaWrite,
            $key::Src: Sized,
            $value: SchemaWrite,
            $value::Src: Sized,
        {
            type Src = $target<$key::Src, $value::Src>;

            #[inline]
            fn size_of(src: &Self::Src) -> Result<usize> {
                Ok(<BincodeLen>::bytes_needed(src.len())?
                    + src
                        .iter()
                        .try_fold(
                            0,
                            |acc, (k, v)|
                                Ok::<_, crate::Error>(acc + $key::size_of(k)? + $value::size_of(v)?)
                        )?
                    )
            }

            #[inline]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                <BincodeLen>::encode_len(writer, src.len())?;
                for (k, v) in src.iter() {
                    $key::write(writer, k)?;
                    $value::write(writer, v)?;
                }
                Ok(())
            }
        }

        #[cfg(feature = $feature)]
        impl<'de, $key, $value> SchemaRead<'de> for $target<$key, $value>
        where
            $key: SchemaRead<'de>,
            $value: SchemaRead<'de>
            $(,$key::Dst: $constraint+)*,
        {
            type Dst = $target<$key::Dst, $value::Dst>;

            #[inline]
            fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                let len = <BincodeLen>::size_hint_cautious::<($key::Dst, $value::Dst)>(reader)?;
                let map = (0..len)
                    .map(|_| {
                        let k = $key::get(reader)?;
                        let v = $value::get(reader)?;
                        Ok::<_, crate::Error>((k, v))
                    })
                    .collect::<Result<_>>()?;

                dst.write(map);
                Ok(())
            }
        }
    };

    ($feature: literal, $target: ident <$key: ident : $($constraint:path)|*>) => {
        #[cfg(feature = $feature)]
        impl<$key: SchemaWrite> SchemaWrite for $target<$key>
        where
            $key::Src: Sized,
        {
            type Src = $target<$key::Src>;

            #[inline]
            fn size_of(src: &Self::Src) -> Result<usize> {
                size_of_elem_iter::<$key, BincodeLen>(src.iter())
            }

            #[inline]
            fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
                write_elem_iter::<$key, BincodeLen>(writer, src.iter())
            }
        }

        #[cfg(feature = $feature)]
        impl<'de, $key> SchemaRead<'de> for $target<$key>
        where
            $key: SchemaRead<'de>
            $(,$key::Dst: $constraint+)*,
        {
            type Dst = $target<$key::Dst>;

            #[inline]
            fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
                let len = <BincodeLen>::size_hint_cautious::<$key::Dst>(reader)?;
                let map = (0..len)
                    .map(|_| $key::get(reader))
                    .collect::<Result<_>>()?;

                dst.write(map);
                Ok(())
            }
        }
    };
}

impl_seq! { "alloc", BTreeMap<K: Ord, V> }
impl_seq! { "std", HashMap<K: Hash | Eq, V> }
impl_seq! { "alloc", BTreeSet<K: Ord> }
impl_seq! { "std", HashSet<K: Hash | Eq> }
impl_seq! { "alloc", LinkedList<K:> }

#[cfg(feature = "alloc")]
impl<T> SchemaWrite for BinaryHeap<T>
where
    T: SchemaWrite,
    T::Src: Sized,
{
    type Src = BinaryHeap<T::Src>;

    #[inline]
    fn size_of(src: &Self::Src) -> Result<usize> {
        <containers::BinaryHeap<Elem<T>, BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut Writer, src: &Self::Src) -> Result<()> {
        <containers::BinaryHeap<Elem<T>, BincodeLen>>::write(writer, src)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for BinaryHeap<T>
where
    T: SchemaRead<'de>,
    T::Dst: Ord,
{
    type Dst = BinaryHeap<T::Dst>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        <containers::BinaryHeap<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}

// Recursively drop the given initialized fields in reverse order.
#[macro_export]
#[doc(hidden)]
macro_rules! __drop_rev {
    // Done
    ($dst_ptr:expr,) => {};
    ($dst_ptr:expr, $head:tt $($rest:tt)*) => {
        unsafe { core::ptr::drop_in_place(&mut (*$dst_ptr).$head); }
        $crate::__drop_rev!($dst_ptr, $($rest)*);
    };
}

/// Recursive read of struct / tuple fields in order, accumulating a list of initialized fields on step.
/// This allows us to expand out to code that will drop the fields that have been initialized successfully
/// when a subsequent `read` encounters an error.
#[macro_export]
#[doc(hidden)]
macro_rules! __read_fields_with_drop {
    // Done
    ($dst_ptr:expr, $reader:expr; [$($done:tt)*] ; ) => {};

    // Step
    ($dst_ptr:expr, $reader:expr; [$($done:tt)*] ;
        $field:tt : $schema:ty $(, $rest_field:tt : $rest_schema:ty )* ) => {
        // Clippy will warn about using `?` on the first `read` because it doesn't have any fields to drop,
        // and its block will just contain `return Err(e)`.
        #[allow(clippy::question_mark)]
        if let Err(e) = <$schema as $crate::SchemaRead>::read(
            $reader,
            // Cast the *mut pointer of the struct field to a &mut MaybeUninit.
            unsafe { &mut *(&raw mut (*$dst_ptr).$field).cast() },
        ) {
            // Drop the fields that have been initialized successfully.
            $crate::__drop_rev!($dst_ptr, $($done)*);
            return Err(e);
        }
        // Recurse.
        $crate::__read_fields_with_drop!($dst_ptr, $reader; [$field $($done)*] ; $( $rest_field : $rest_schema ),* );
    };
}

macro_rules! impl_tuple {
    ($($schema:ident: $field:tt),+) => {
        impl<$($schema),+> $crate::SchemaWrite for ($($schema),+)
        where
            $($schema: $crate::SchemaWrite),+,
            $($schema::Src: Sized),+
        {
            type Src = ($($schema::Src),+);

            #[inline]
            fn size_of(value: &Self::Src) -> $crate::error::Result<usize> {
                Ok(0 $(+ <$schema as $crate::SchemaWrite>::size_of(&value.$field)?)+)
            }

            #[inline]
            fn write(writer: &mut $crate::io::Writer, value: &Self::Src) -> $crate::error::Result<()> {
                $(<$schema as $crate::SchemaWrite>::write(writer, &value.$field)?;)+
                Ok(())
            }
        }

        impl<'de, $($schema),+> $crate::SchemaRead<'de> for ($($schema),+)
        where
            $($schema: $crate::SchemaRead<'de>),+,
        {
            type Dst = ($($schema::Dst),+);

            #[inline]
            fn read(reader: &mut $crate::io::Reader<'de>, dst: &mut core::mem::MaybeUninit<Self::Dst>) -> $crate::error::Result<()> {
                let dst_ptr = dst.as_mut_ptr();
                $crate::__read_fields_with_drop!(dst_ptr, reader; [] ; $($field: $schema),+);
                Ok(())
            }
        }
    };
}

impl_tuple! { A: 0, B: 1 }
impl_tuple! { A: 0, B: 1, C: 2 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9, K: 10 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9, K: 10, L: 11 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9, K: 10, L: 11, M: 12 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9, K: 10, L: 11, M: 12, N: 13 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9, K: 10, L: 11, M: 12, N: 13, O: 14 }
impl_tuple! { A: 0, B: 1, C: 2, D: 3, E: 4, F: 5, G: 6, H: 7, I: 8, J: 9, K: 10, L: 11, M: 12, N: 13, O: 14, P: 15 }
