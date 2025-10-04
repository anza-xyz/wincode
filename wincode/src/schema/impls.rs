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
#[cfg(feature = "alloc")]
use {
    crate::containers::{self, Elem},
    alloc::{boxed::Box, collections::VecDeque, vec::Vec},
};
use {
    crate::{
        error::{
            invalid_bool_encoding, invalid_tag_encoding, pointer_sized_decode_error, Error, Result,
        },
        io::{Reader, Writer},
        len::BincodeLen,
        schema::{size_of_elem_iter, write_elem_iter, SchemaRead, SchemaWrite},
    },
    core::{
        hint::unreachable_unchecked,
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
                let ptr = dst.as_mut_ptr().cast::<Option<MaybeUninit<T::Dst>>>();
                unsafe {
                    ptr.write(Option::Some(MaybeUninit::uninit()));
                    match &mut *ptr {
                        Some(dst) => T::read(reader, dst)?,
                        None => unreachable_unchecked(),
                    }
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
{
    type Src = &'a T::Src;

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
impl<T> SchemaWrite for Box<T>
where
    T: SchemaWrite,
{
    type Src = Box<T::Src>;

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
impl<'de, T> SchemaRead<'de> for Box<T>
where
    T: SchemaRead<'de>,
{
    type Dst = Box<T::Dst>;

    #[inline]
    fn read(reader: &mut Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> Result<()> {
        let mut mem = Box::new_uninit();
        T::read(reader, &mut mem)?;
        unsafe {
            // SAFETY: `T::read` must properly initialize the `T::Dst`.
            dst.write(mem.assume_init());
        }
        Ok(())
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

/// Implement [`SchemaWrite`] and [`SchemaRead`] for a struct by specifying its constituent field schemas.
///
/// Note using this on packed structs is UB.
///
/// # Examples
///
/// ```
/// use wincode::compound;
///
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// compound! {
///     Point {
///         x: u64,
///         y: u64,
///     }
/// }
///
/// struct MyStruct {
///     point: Point,
/// }
///
/// compound! {
///     MyStruct {
///         point: Point,
///     }
/// }
/// ```
///
/// This macro also supports creating intermediate `#[repr(transparent)]` newtype structs that map to a target type.
/// This is useful when the target type is foreign (defined outside the crate).
///
/// ```
/// # use wincode::{containers::Pod, compound, Serialize, Deserialize};
/// // Imagine this is a struct defined outside our crate.
/// # #[derive(Debug, PartialEq, Eq)]
/// struct ForeignStruct {
///     pub field: [u8; 32],
/// }
///
/// compound! {
///     struct OurStruct => ForeignStruct {
///         field: Pod<[u8; 32]>,
///     }
/// }
///
/// let foreign_struct = ForeignStruct {
///     field: [0; 32],
/// };
/// let bytes = OurStruct::serialize(&foreign_struct).unwrap();
/// let deserialized = OurStruct::deserialize(&bytes).unwrap();
/// assert_eq!(foreign_struct, deserialized);
/// ```
///
/// Omitting the `struct` keyword will allow you to define the newtype yourself.
/// ```
///  # use wincode::{containers::Pod, compound, Serialize, Deserialize};
/// // Imagine this is a struct defined outside our crate.
/// # #[derive(Debug, PartialEq, Eq)]
/// struct ForeignStruct {
///     pub field: [u8; 32],
/// }
///
/// #[repr(transparent)]
/// struct OurStruct(ForeignStruct);
///
/// compound! {
///     OurStruct => ForeignStruct {
///         field: Pod<[u8; 32]>,
///     }
/// }
///
/// let foreign_struct = ForeignStruct {
///     field: [0; 32],
/// };
/// let bytes = OurStruct::serialize(&foreign_struct).unwrap();
/// let deserialized = OurStruct::deserialize(&bytes).unwrap();
/// assert_eq!(foreign_struct, deserialized);
/// ```
#[macro_export]
macro_rules! compound {
    ($vis:vis $src:ident { $($field:ident : $schema:ty),+ $(,)? }) => {
        $crate::compound! { $src => $src { $($field: $schema),+ } }
    };
    ($vis:vis struct $src:ident => $target:ty { $($field:ident : $schema:ty),+ $(,)? }) => {
        #[repr(transparent)]
        $vis struct $src($vis $target);

        $crate::compound! {
            $vis $src => $target {
                $($field: $schema),+
            }
        }
    };
    ($vis:vis $src:ident => $target:ty { $($field:ident : $schema:ty),+ $(,)? }) => {
        $crate::__private::paste! {
            #[allow(unused)]
            $vis trait [<$src Ext>] {
                $(
                    /// Get a mutable [`MaybeUninit`](core::mem::MaybeUninit) to the corresponding slot in `dst` for the field.
                    fn [<get_uninit_ $field _mut>](dst: &mut core::mem::MaybeUninit<$target>) -> &mut core::mem::MaybeUninit<<$schema as $crate::SchemaRead<'_>>::Dst>;
                    /// Read the field into the corresponding slot in `dst` from `reader`.
                    ///
                    /// # Safety
                    ///
                    /// - Corresponding field schema must properly initialize the field.
                    fn [<read_ $field>](reader: &mut $crate::io::Reader, dst: &mut core::mem::MaybeUninit<$target>) -> $crate::error::Result<()>;
                    /// Write an initialized instance of the field into the corresponding slot in `dst`.
                    fn [<write_uninit_ $field>](val: <$schema as $crate::SchemaRead>::Dst, dst: &mut core::mem::MaybeUninit<$target>);
                )+
            }

            impl [<$src Ext>] for $src {
                #[inline]
                $(fn [<get_uninit_ $field _mut>](dst: &mut core::mem::MaybeUninit<$target>) -> &mut core::mem::MaybeUninit<<$schema as $crate::SchemaRead<'_>>::Dst> {
                    unsafe { &mut *(&raw mut (*dst.as_mut_ptr()).$field).cast() }
                })+
                #[inline]
                $(fn [<read_ $field>](reader: &mut $crate::io::Reader, dst: &mut core::mem::MaybeUninit<$target>) -> $crate::error::Result<()> {
                    <$schema as $crate::SchemaRead>::read(reader, Self::[<get_uninit_ $field _mut>](dst) )
                })+
                #[inline]
                $(fn [<write_uninit_ $field>](val: <$schema as $crate::SchemaRead>::Dst, dst: &mut core::mem::MaybeUninit<$target>) {
                    Self::[<get_uninit_ $field _mut>](dst).write(val);
                })+
            }
        }

        impl $crate::SchemaWrite for $src {
            type Src = $target;

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
        // Compile time alignment check (prevent packed structs).
        $(
            #[allow(clippy::arithmetic_side_effects, clippy::modulo_one)]
            const _: () = {
                const OFFSET: usize = core::mem::offset_of!($target, $field);
                const ALIGN: usize = core::mem::align_of::<<$schema as $crate::SchemaRead>::Dst>();
                assert!(
                    OFFSET % ALIGN == 0,
                    concat!(stringify!($target), "::", stringify!($field), " is not naturally aligned (packed?)")
                );
            };
        )+

        impl $crate::SchemaRead<'_> for $src {
            type Dst = $target;

            #[inline]
            fn read(reader: &mut $crate::io::Reader, dst: &mut core::mem::MaybeUninit<Self::Dst>) -> $crate::error::Result<()> {
                let dst_ptr = dst.as_mut_ptr();
                $crate::__read_fields_with_drop!(dst_ptr, reader; []; $($field: $schema ),+);
                Ok(())
            }
        }
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
