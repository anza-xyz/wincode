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
use {
    crate::{
        containers::SliceDropGuard,
        error::{
            invalid_bool_encoding, invalid_char_lead, invalid_tag_encoding, invalid_utf8_encoding,
            pointer_sized_decode_error, ReadResult, WriteResult,
        },
        io::{Reader, Writer},
        len::{BincodeLen, SeqLen},
        schema::{size_of_elem_slice, write_elem_slice, SchemaRead, SchemaWrite},
        util::type_equal,
    },
    core::{
        marker::PhantomData,
        mem::{self, transmute, MaybeUninit},
    },
};
#[cfg(feature = "alloc")]
use {
    crate::{
        containers::{self, Elem},
        error::WriteError,
        schema::{size_of_elem_iter, write_elem_iter},
    },
    alloc::{
        boxed::Box,
        collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque},
        rc::Rc,
        string::String,
        sync::Arc,
        vec::Vec,
    },
};

macro_rules! impl_int {
    ($type:ty) => {
        impl SchemaWrite for $type {
            type Src = $type;

            #[inline(always)]
            fn size_of(_src: &Self::Src) -> WriteResult<usize> {
                Ok(size_of::<$type>())
            }

            #[inline(always)]
            fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                Ok(writer.write(&src.to_le_bytes())?)
            }
        }

        impl<'de> SchemaRead<'de> for $type {
            type Dst = $type;

            #[inline(always)]
            fn read(
                reader: &mut impl Reader<'de>,
                dst: &mut MaybeUninit<Self::Dst>,
            ) -> ReadResult<()> {
                // SAFETY: integer is plain ol' data.
                let bytes = reader.fill_array::<{ size_of::<$type>() }>()?;
                // bincode defaults to little endian encoding.
                dst.write(<$type>::from_le_bytes(*bytes));
                unsafe { reader.consume_unchecked(size_of::<$type>()) };

                Ok(())
            }
        }
    };

    ($type:ty as $cast:ty) => {
        impl SchemaWrite for $type {
            type Src = $type;

            #[inline]
            fn size_of(_src: &Self::Src) -> WriteResult<usize> {
                Ok(size_of::<$cast>())
            }

            #[inline]
            fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                let src = *src as $cast;
                // bincode defaults to little endian encoding.
                // noop on LE machines.
                Ok(writer.write(&src.to_le_bytes())?)
            }
        }

        impl<'de> SchemaRead<'de> for $type {
            type Dst = $type;

            #[inline]
            fn read(
                reader: &mut impl Reader<'de>,
                dst: &mut MaybeUninit<Self::Dst>,
            ) -> ReadResult<()> {
                let casted = <$cast>::get(reader)?;
                let val = casted
                    .try_into()
                    .map_err(|_| pointer_sized_decode_error())?;

                dst.write(val);

                Ok(())
            }
        }
    };
}

impl_int!(u8);
impl_int!(i8);
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

impl SchemaWrite for bool {
    type Src = bool;

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(size_of::<u8>())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        unsafe { Ok(writer.write_t(&(*src as u8))?) }
    }
}

impl<'de> SchemaRead<'de> for bool {
    type Dst = bool;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // SAFETY: u8 is plain ol' data.
        let byte = u8::get(reader)?;
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

impl SchemaWrite for char {
    type Src = char;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        let mut buf = [0; 4];
        let str = src.encode_utf8(&mut buf);
        Ok(str.len())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        let mut buf = [0; 4];
        let str = src.encode_utf8(&mut buf);
        writer.write(str.as_bytes())?;
        Ok(())
    }
}

impl<'de> SchemaRead<'de> for char {
    type Dst = char;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let b0 = *reader.peek()?;

        let len = match b0 {
            0x00..=0x7F => 1,
            0xC2..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xF4 => 4,
            _ => return Err(invalid_char_lead(b0)),
        };

        if len == 1 {
            unsafe { reader.consume_unchecked(1) };
            dst.write(b0 as char);
            return Ok(());
        }

        let buf = reader.fill_exact(len)?;
        // TODO: Could implement a manual decoder that avoids UTF-8 validate + chars()
        // and instead performs the UTF-8 validity checks and produces a `char` directly.
        // Some quick micro-benchmarking revealed a roughly 2x speedup is possible,
        // but this is on the order of a 1-2ns/byte delta.
        let str = core::str::from_utf8(buf).map_err(invalid_utf8_encoding)?;
        let c = str.chars().next().unwrap();
        unsafe { reader.consume_unchecked(len) };
        dst.write(c);
        Ok(())
    }
}

impl<T> SchemaWrite for PhantomData<T> {
    type Src = PhantomData<T>;

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(0)
    }

    #[inline]
    fn write(_writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
        Ok(())
    }
}

impl<'de, T> SchemaRead<'de> for PhantomData<T> {
    type Dst = PhantomData<T>;

    #[inline]
    fn read(_reader: &mut impl Reader<'de>, _dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        Ok(())
    }
}

impl SchemaWrite for () {
    type Src = ();

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(0)
    }

    #[inline]
    fn write(_writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
        Ok(())
    }
}

impl<'de> SchemaRead<'de> for () {
    type Dst = ();

    #[inline]
    fn read(_reader: &mut impl Reader<'de>, _dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        <containers::Vec<Elem<T>, BincodeLen>>::size_of(value)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
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
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        <containers::VecDeque<Elem<T>, BincodeLen>>::size_of(value)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
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
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, BincodeLen>(value)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        write_elem_slice::<T, BincodeLen>(writer, value)
    }
}

impl<'de> SchemaRead<'de> for &'de [u8] {
    type Dst = &'de [u8];

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = <BincodeLen>::read::<u8>(reader)?;
        dst.write(reader.borrow_exact(len)?);
        Ok(())
    }
}

impl<'de, T, const N: usize> SchemaRead<'de> for [T; N]
where
    T: SchemaRead<'de>,
{
    type Dst = [T::Dst; N];

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        if type_equal::<T::Dst, u8>() {
            unsafe {
                reader.copy_into_array(transmute::<
                    &mut MaybeUninit<Self::Dst>,
                    &mut MaybeUninit<[u8; N]>,
                >(dst))?
            };
            return Ok(());
        }
        // SAFETY: MaybeUninit<[T::Dst; N]> trivially converts to [MaybeUninit<T::Dst>; N].
        let dst =
            unsafe { transmute::<&mut MaybeUninit<Self::Dst>, &mut [MaybeUninit<T::Dst>; N]>(dst) };
        let base = dst.as_mut_ptr();
        let mut guard = SliceDropGuard::<T::Dst>::new(base);
        // Avoid slice reborrow of `dst` (triggered by `dst.iter_mut()`)
        for i in 0..N {
            let slot = unsafe { &mut *base.add(i) };
            T::read(reader, slot)?;
            guard.inc_len();
        }
        mem::forget(guard);
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
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        if type_equal::<T::Src, u8>() {
            return Ok(N);
        }
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        value
            .iter()
            .map(T::size_of)
            .try_fold(0usize, |acc, x| x.map(|x| acc + x))
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        if type_equal::<T::Src, u8>() {
            unsafe { writer.write(transmute::<&[T::Src; N], &[u8; N]>(value))? };
            return Ok(());
        }
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
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        match src {
            // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
            Option::Some(value) => Ok(1 + T::size_of(value)?),
            Option::None => Ok(1),
        }
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
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
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        T::size_of(*src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
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
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                T::size_of(src)
            }

            #[inline]
            fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
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
            fn read(
                reader: &mut impl Reader<'de>,
                dst: &mut MaybeUninit<Self::Dst>,
            ) -> ReadResult<()> {
                struct DropGuard<T>(*mut MaybeUninit<T>);
                impl<T> Drop for DropGuard<T> {
                    #[inline]
                    fn drop(&mut self) {
                        drop(unsafe { $container::from_raw(self.0) });
                    }
                }

                let mem = $container::<T::Dst>::new_uninit();
                let ptr = $container::into_raw(mem) as *mut _;
                let guard: DropGuard<T::Dst> = DropGuard(ptr);
                T::read(reader, unsafe { &mut *ptr })?;

                mem::forget(guard);

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
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::Box<[Elem<T>], BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Box<[Elem<T>], BincodeLen>>::write(writer, value)
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
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::Rc<[Elem<T>], BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Rc<[Elem<T>], BincodeLen>>::write(writer, value)
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
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::Arc<[Elem<T>], BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Arc<[Elem<T>], BincodeLen>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Box<[T]>
where
    T: SchemaRead<'de>,
{
    type Dst = Box<[T::Dst]>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Box<[Elem<T>], BincodeLen>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Rc<[T]>
where
    T: SchemaRead<'de>,
{
    type Dst = Rc<[T::Dst]>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Rc<[Elem<T>], BincodeLen>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
impl<'de, T> SchemaRead<'de> for Arc<[T]>
where
    T: SchemaRead<'de>,
{
    type Dst = Arc<[T::Dst]>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Arc<[Elem<T>], BincodeLen>>::read(reader, dst)
    }
}

impl SchemaWrite for str {
    type Src = str;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        Ok(<BincodeLen>::write_bytes_needed(src.len())? + src.len())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        <BincodeLen>::write(writer, src.len())?;
        writer.write(src.as_bytes())?;
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl SchemaWrite for String {
    type Src = String;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <str>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        <str>::write(writer, src)
    }
}

impl<'de> SchemaRead<'de> for &'de str {
    type Dst = &'de str;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = <BincodeLen>::read::<u8>(reader)?;
        let bytes = reader.borrow_exact(len)?;
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
impl<'de> SchemaRead<'de> for String {
    type Dst = String;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = <BincodeLen>::read::<u8>(reader)?;
        let bytes = reader.fill_exact(len)?.to_vec();
        unsafe { reader.consume_unchecked(len) };
        match String::from_utf8(bytes) {
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
            #[allow(clippy::arithmetic_side_effects)]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                Ok(<BincodeLen>::write_bytes_needed(src.len())? +
                    src
                        .iter()
                        .try_fold(
                            0usize,
                            |acc, (k, v)|
                            Ok::<_, WriteError>(
                                acc
                                + $key::size_of(k)?
                                + $value::size_of(v)?
                            )
                    )?
                )
            }

            #[inline]
            fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                <BincodeLen>::write(writer, src.len())?;
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
            fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let len = <BincodeLen>::read::<($key::Dst, $value::Dst)>(reader)?;
                let map = (0..len)
                    .map(|_| {
                        let k = $key::get(reader)?;
                        let v = $value::get(reader)?;
                        Ok::<_, crate::ReadError>((k, v))
                    })
                    .collect::<ReadResult<_>>()?;

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
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                size_of_elem_iter::<$key, BincodeLen>(src.iter())
            }

            #[inline]
            fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
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
            fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let len = <BincodeLen>::read::<$key::Dst>(reader)?;
                let map = (0..len)
                    .map(|_| $key::get(reader))
                    .collect::<ReadResult<_>>()?;

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
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::BinaryHeap<Elem<T>, BincodeLen>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
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
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::BinaryHeap<Elem<T>, BincodeLen>>::read(reader, dst)
    }
}
