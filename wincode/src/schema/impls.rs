//! Blanket implementations for std types.
#[cfg(feature = "std")]
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    time::{SystemTime, UNIX_EPOCH},
};
use {
    crate::{
        config::{Config, ConfigCore, ZeroCopy},
        containers::SliceDropGuard,
        error::{
            invalid_bool_encoding, invalid_char_lead, invalid_tag_encoding, invalid_utf8_encoding,
            invalid_value, pointer_sized_decode_error, read_length_encoding_overflow,
            unaligned_pointer_read, ReadResult, WriteResult,
        },
        int_encoding::{ByteOrder, Endian, IntEncoding, PlatformEndian},
        io::{Reader, Writer},
        len::SeqLen,
        schema::{size_of_elem_slice, write_elem_slice, SchemaRead, SchemaWrite},
        tag_encoding::TagEncoding,
        TypeMeta,
    },
    core::{
        marker::PhantomData,
        mem::{self, transmute, MaybeUninit},
        net::{IpAddr, Ipv4Addr, Ipv6Addr},
        time::Duration,
    },
    pastey::paste,
};
#[cfg(feature = "alloc")]
use {
    crate::{
        containers::{self},
        error::WriteError,
        schema::{size_of_elem_iter, write_elem_iter_prealloc_check},
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

macro_rules! impl_int_config_dependent {
    ($($type:ty),*) => {
        paste! {
            $(
                unsafe impl<C: ConfigCore> ZeroCopy<C> for $type where C::IntEncoding: ZeroCopy<C> {}

                unsafe impl<C: ConfigCore> SchemaWrite<C> for $type {
                    type Src = $type;

                    const TYPE_META: TypeMeta = if C::IntEncoding::STATIC {
                        TypeMeta::Static {
                            size: size_of::<$type>(),
                            zero_copy: C::IntEncoding::ZERO_COPY,
                        }
                    } else {
                        TypeMeta::Dynamic
                    };

                    #[inline(always)]
                    fn size_of(src: &Self::Src) -> WriteResult<usize> {
                        Ok(C::IntEncoding::[<size_of_ $type>](*src))
                    }

                    #[inline(always)]
                    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                        C::IntEncoding::[<encode_ $type>](*src, writer)
                    }
                }

                unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for $type {
                    type Dst = $type;

                    const TYPE_META: TypeMeta = if C::IntEncoding::STATIC {
                        TypeMeta::Static {
                            size: size_of::<$type>(),
                            zero_copy: C::IntEncoding::ZERO_COPY,
                        }
                    } else {
                        TypeMeta::Dynamic
                    };

                    #[inline(always)]
                    fn read(
                        reader: &mut impl Reader<'de>,
                        dst: &mut MaybeUninit<Self::Dst>,
                    ) -> ReadResult<()> {
                        let val = C::IntEncoding::[<decode_ $type>](reader)?;
                        dst.write(val);
                        Ok(())
                    }
                }
            )*
        }
    };
}

impl_int_config_dependent!(u16, u32, u64, u128, i16, i32, i64, i128);

/// Implementations for `f32` and `f64` using fixed-width encoding and the
/// configured byte order.
///
/// This matches bincode: floats are always fixed-width, independent of integer
/// encoding choices.
/// - Varint saves space when small values map to small bit-patterns. IEEE-754
///   floats do not have that property, so varint rarely (if ever) helps and costs more.
/// - Exact bit patterns must round-trip (-0.0, NaN payloads, subnormals), which
///   fixed-width preserves without extra rules or validation.
macro_rules! impl_float {
    ($($ty:ty),*) => {
        $(
            unsafe impl<C: ConfigCore> ZeroCopy<C> for $ty where C::ByteOrder: PlatformEndian {}

            unsafe impl<C: ConfigCore> SchemaWrite<C> for $ty {
                type Src = $ty;

                const TYPE_META: TypeMeta = TypeMeta::Static {
                    size: size_of::<$ty>(),
                    #[cfg(target_endian = "big")]
                    zero_copy: matches!(C::ByteOrder::ENDIAN, Endian::Big),
                    #[cfg(target_endian = "little")]
                    zero_copy: matches!(C::ByteOrder::ENDIAN, Endian::Little),
                };

                #[inline(always)]
                fn size_of(_val: &Self::Src) -> WriteResult<usize> {
                    Ok(size_of::<$ty>())
                }

                #[inline(always)]
                fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                    let bytes = match C::ByteOrder::ENDIAN {
                        Endian::Big => src.to_be_bytes(),
                        Endian::Little => src.to_le_bytes(),
                    };
                    writer.write(&bytes)?;
                    Ok(())
                }
            }

            unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for $ty {
                type Dst = $ty;

                const TYPE_META: TypeMeta = TypeMeta::Static {
                    size: size_of::<$ty>(),
                    #[cfg(target_endian = "big")]
                    zero_copy: matches!(C::ByteOrder::ENDIAN, Endian::Big),
                    #[cfg(target_endian = "little")]
                    zero_copy: matches!(C::ByteOrder::ENDIAN, Endian::Little),
                };

                #[inline(always)]
                fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                    let bytes = *reader.fill_array::<{ size_of::<$ty>() }>()?;
                    // SAFETY: fill_array is guaranteed to consume `size_of::<$ty>()` bytes.
                    unsafe { reader.consume_unchecked(size_of::<$ty>()) };
                    let val = match C::ByteOrder::ENDIAN {
                        Endian::Big => <$ty>::from_be_bytes(bytes),
                        Endian::Little => <$ty>::from_le_bytes(bytes),
                    };
                    dst.write(val);
                    Ok(())
                }
            }
        )*
    };
}

impl_float!(f32, f64);

macro_rules! impl_pointer_width {
    ($($type:ty => $target:ty),*) => {
        $(
            unsafe impl<C: ConfigCore> SchemaWrite<C> for $type {
                type Src = $type;

                const TYPE_META: TypeMeta = if C::IntEncoding::STATIC {
                    TypeMeta::Static {
                        size: size_of::<$target>(),
                        zero_copy: false,
                    }
                } else {
                    TypeMeta::Dynamic
                };

                #[inline(always)]
                fn size_of(val: &Self::Src) -> WriteResult<usize> {
                    <$target as SchemaWrite<C>>::size_of(&(*val as $target))
                }

                #[inline(always)]
                fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                    <$target as SchemaWrite<C>>::write(writer, &(*src as $target))
                }
            }

            unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for $type {
                type Dst = $type;

                const TYPE_META: TypeMeta = if C::IntEncoding::STATIC {
                    TypeMeta::Static {
                        size: size_of::<$target>(),
                        zero_copy: false,
                    }
                } else {
                    TypeMeta::Dynamic
                };

                #[inline(always)]
                fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                    let target = <$target as SchemaRead<C>>::get(reader)?;
                    let val = target.try_into().map_err(|_| pointer_sized_decode_error())?;
                    dst.write(val);
                    Ok(())
                }
            }
        )*
    };
}

impl_pointer_width!(usize => u64, isize => i64);

macro_rules! impl_byte {
    ($($type:ty),*) => {
        $(
            // SAFETY:
            // - canonical zero-copy type: no endianness, no layout, no validation.
            unsafe impl<C: ConfigCore> ZeroCopy<C> for $type {}

            unsafe impl<C: ConfigCore> SchemaWrite<C> for $type {
                type Src = $type;

                const TYPE_META: TypeMeta = TypeMeta::Static {
                    size: size_of::<$type>(),
                    zero_copy: true,
                };

                #[inline(always)]
                fn size_of(_val: &Self::Src) -> WriteResult<usize> {
                    Ok(size_of::<$type>())
                }

                #[inline(always)]
                fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                    writer.write(&[*src as u8])?;
                    Ok(())
                }
            }

            unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for $type {
                type Dst = $type;

                const TYPE_META: TypeMeta = TypeMeta::Static {
                    size: size_of::<$type>(),
                    zero_copy: true,
                };

                #[inline(always)]
                fn read(
                    reader: &mut impl Reader<'de>,
                    dst: &mut MaybeUninit<Self::Dst>,
                ) -> ReadResult<()> {
                    let byte = *reader.fill_array::<{ 1 }>()?;
                    // SAFETY: `fill_array` guarantees we get one byte.
                    unsafe { reader.consume_unchecked(1) };
                    dst.write(byte[0] as $type);
                    Ok(())
                }
            }
        )*
    };
}

impl_byte!(u8, i8);

unsafe impl<C: ConfigCore> SchemaWrite<C> for bool {
    type Src = bool;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: size_of::<bool>(),
        zero_copy: false,
    };

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(size_of::<u8>())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        unsafe { Ok(writer.write_t(&(*src as u8))?) }
    }
}

unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for bool {
    type Dst = bool;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: size_of::<bool>(),
        zero_copy: false,
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // SAFETY: u8 is plain ol' data.
        let byte = <u8 as SchemaRead<'de, C>>::get(reader)?;
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

unsafe impl<C: ConfigCore> SchemaWrite<C> for char {
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

unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for char {
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

unsafe impl<T, C: ConfigCore> SchemaWrite<C> for PhantomData<T> {
    type Src = PhantomData<T>;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 0,
        zero_copy: true,
    };

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(0)
    }

    #[inline]
    fn write(_writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
        Ok(())
    }
}

unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for PhantomData<T> {
    type Dst = PhantomData<T>;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 0,
        zero_copy: true,
    };

    #[inline]
    fn read(_reader: &mut impl Reader<'de>, _dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        Ok(())
    }
}

unsafe impl<C: ConfigCore> SchemaWrite<C> for () {
    type Src = ();

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 0,
        zero_copy: true,
    };

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(0)
    }

    #[inline]
    fn write(_writer: &mut impl Writer, _src: &Self::Src) -> WriteResult<()> {
        Ok(())
    }
}

unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for () {
    type Dst = ();

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 0,
        zero_copy: true,
    };

    #[inline]
    fn read(_reader: &mut impl Reader<'de>, _dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        Ok(())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T, C: Config> SchemaWrite<C> for Vec<T>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = Vec<T::Src>;

    #[inline]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        <containers::Vec<T, C::LengthEncoding>>::size_of(value)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Vec<T, C::LengthEncoding>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for Vec<T>
where
    T: SchemaRead<'de, C>,
{
    type Dst = Vec<T::Dst>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Vec<T, C::LengthEncoding>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T, C: Config> SchemaWrite<C> for VecDeque<T>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = VecDeque<T::Src>;

    #[inline]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        <containers::VecDeque<T, C::LengthEncoding>>::size_of(value)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::VecDeque<T, C::LengthEncoding>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for VecDeque<T>
where
    T: SchemaRead<'de, C>,
{
    type Dst = VecDeque<T::Dst>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::VecDeque<T, C::LengthEncoding>>::read(reader, dst)
    }
}

unsafe impl<T, C: Config> SchemaWrite<C> for [T]
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = [T::Src];

    #[inline]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, C::LengthEncoding, C>(value)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        write_elem_slice::<T, C::LengthEncoding, C>(writer, value)
    }
}

// SAFETY:
// - [T; N] where T: ZeroCopy is trivially zero-copy. The length is constant,
//   so there is no length encoding.
unsafe impl<const N: usize, C: ConfigCore, T> ZeroCopy<C> for [T; N] where T: ZeroCopy<C> {}

unsafe impl<'de, T, const N: usize, C: ConfigCore> SchemaRead<'de, C> for [T; N]
where
    T: SchemaRead<'de, C>,
{
    type Dst = [T::Dst; N];

    const TYPE_META: TypeMeta = const {
        match T::TYPE_META {
            TypeMeta::Static { size, zero_copy } => TypeMeta::Static {
                size: N * size,
                zero_copy,
            },
            TypeMeta::Dynamic => TypeMeta::Dynamic,
        }
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        if let TypeMeta::Static {
            zero_copy: true, ..
        } = T::TYPE_META
        {
            // SAFETY: `T::Dst` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
            unsafe { reader.copy_into_t(dst)? };
            return Ok(());
        }

        // SAFETY: MaybeUninit<[T::Dst; N]> trivially converts to [MaybeUninit<T::Dst>; N].
        let dst =
            unsafe { transmute::<&mut MaybeUninit<Self::Dst>, &mut [MaybeUninit<T::Dst>; N]>(dst) };
        let base = dst.as_mut_ptr();
        let mut guard = SliceDropGuard::<T::Dst>::new(base);
        if let TypeMeta::Static { size, .. } = Self::TYPE_META {
            // SAFETY: `Self::TYPE_META` specifies a static size, which is `N * static_size_of(T)`.
            // `N` reads of `T` will consume `size` bytes, fully consuming the trusted window.
            let reader = &mut unsafe { reader.as_trusted_for(size) }?;
            for i in 0..N {
                let slot = unsafe { &mut *base.add(i) };
                T::read(reader, slot)?;
                guard.inc_len();
            }
        } else {
            for i in 0..N {
                let slot = unsafe { &mut *base.add(i) };
                T::read(reader, slot)?;
                guard.inc_len();
            }
        }
        mem::forget(guard);
        Ok(())
    }
}

unsafe impl<T, const N: usize, C: ConfigCore> SchemaWrite<C> for [T; N]
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = [T::Src; N];

    const TYPE_META: TypeMeta = const {
        match T::TYPE_META {
            TypeMeta::Static { size, zero_copy } => TypeMeta::Static {
                size: N * size,
                zero_copy,
            },
            TypeMeta::Dynamic => TypeMeta::Dynamic,
        }
    };

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        if let TypeMeta::Static { size, .. } = Self::TYPE_META {
            return Ok(size);
        }
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        value
            .iter()
            .map(T::size_of)
            .try_fold(0usize, |acc, x| x.map(|x| acc + x))
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        match Self::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => {
                // SAFETY: `T::Src` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                unsafe { writer.write_slice_t(value)? };
            }
            TypeMeta::Static {
                size,
                zero_copy: false,
            } => {
                // SAFETY: `Self::TYPE_META` specifies a static size, which is `N * static_size_of(T)`.
                // `N` writes of `T` will write `size` bytes, fully initializing the trusted window.
                let writer = &mut unsafe { writer.as_trusted_for(size) }?;
                for item in value {
                    T::write(writer, item)?;
                }
                writer.finish()?;
            }
            TypeMeta::Dynamic => {
                for item in value {
                    T::write(writer, item)?;
                }
            }
        }

        Ok(())
    }
}

unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for Option<T>
where
    T: SchemaRead<'de, C>,
{
    type Dst = Option<T::Dst>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let variant = <u8 as SchemaRead<'de, C>>::get(reader)?;
        match variant {
            0 => dst.write(Option::None),
            1 => dst.write(Option::Some(T::get(reader)?)),
            _ => return Err(invalid_tag_encoding(variant as usize)),
        };

        Ok(())
    }
}

unsafe impl<T, C: ConfigCore> SchemaWrite<C> for Option<T>
where
    T: SchemaWrite<C>,
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
                <u8 as SchemaWrite<C>>::write(writer, &1)?;
                T::write(writer, value)
            }
            Option::None => <u8 as SchemaWrite<C>>::write(writer, &0),
        }
    }
}

unsafe impl<'de, T, E, C: Config> SchemaRead<'de, C> for Result<T, E>
where
    T: SchemaRead<'de, C>,
    E: SchemaRead<'de, C>,
{
    type Dst = Result<T::Dst, E::Dst>;

    const TYPE_META: TypeMeta = match (
        T::TYPE_META,
        E::TYPE_META,
        <C::TagEncoding as SchemaWrite<C>>::TYPE_META,
    ) {
        (
            TypeMeta::Static { size: t_size, .. },
            TypeMeta::Static { size: e_size, .. },
            TypeMeta::Static {
                size: disc_size, ..
            },
        ) if t_size == e_size => TypeMeta::Static {
            size: disc_size + t_size,
            zero_copy: false,
        },
        _ => TypeMeta::Dynamic,
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let disc = C::TagEncoding::try_into_u32(C::TagEncoding::get(reader)?)?;
        match disc {
            0 => dst.write(Result::Ok(T::get(reader)?)),
            1 => dst.write(Result::Err(E::get(reader)?)),
            _ => return Err(invalid_tag_encoding(disc as usize)),
        };

        Ok(())
    }
}

unsafe impl<T, E, C: Config> SchemaWrite<C> for Result<T, E>
where
    T: SchemaWrite<C>,
    E: SchemaWrite<C>,
    T::Src: Sized,
    E::Src: Sized,
{
    type Src = Result<T::Src, E::Src>;

    const TYPE_META: TypeMeta = match (
        T::TYPE_META,
        E::TYPE_META,
        <C::TagEncoding as SchemaWrite<C>>::TYPE_META,
    ) {
        (
            TypeMeta::Static { size: t_size, .. },
            TypeMeta::Static { size: e_size, .. },
            TypeMeta::Static {
                size: disc_size, ..
            },
        ) if t_size == e_size => TypeMeta::Static {
            size: disc_size + t_size,
            zero_copy: false,
        },
        _ => TypeMeta::Dynamic,
    };

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        match src {
            // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
            Result::Ok(value) => Ok(C::TagEncoding::size_of_from_u32(0)? + T::size_of(value)?),
            Result::Err(error) => Ok(C::TagEncoding::size_of_from_u32(1)? + E::size_of(error)?),
        }
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        match value {
            Result::Ok(value) => {
                C::TagEncoding::write_from_u32(writer, 0)?;
                T::write(writer, value)
            }
            Result::Err(error) => {
                C::TagEncoding::write_from_u32(writer, 1)?;
                E::write(writer, error)
            }
        }
    }
}

unsafe impl<'a, T, C: ConfigCore> SchemaWrite<C> for &'a T
where
    T: SchemaWrite<C>,
    T: ?Sized,
{
    type Src = &'a T::Src;

    const TYPE_META: TypeMeta = T::TYPE_META;

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
        unsafe impl<T, C: ConfigCore> SchemaWrite<C> for $container<T>
        where
            T: SchemaWrite<C>,
        {
            type Src = $container<T::Src>;

            const TYPE_META: TypeMeta = const {
                match T::TYPE_META {
                    TypeMeta::Static { size, .. } => TypeMeta::Static {
                        size,
                        zero_copy: false,
                    },
                    TypeMeta::Dynamic => TypeMeta::Dynamic,
                }
            };

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
        unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for $container<T>
        where
            T: SchemaRead<'de, C>,
        {
            type Dst = $container<T::Dst>;

            const TYPE_META: TypeMeta = const {
                match T::TYPE_META {
                    TypeMeta::Static { size, .. } => TypeMeta::Static {
                        size,
                        zero_copy: false,
                    },
                    TypeMeta::Dynamic => TypeMeta::Dynamic,
                }
            };

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
unsafe impl<T, C: Config> SchemaWrite<C> for Box<[T]>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = Box<[T::Src]>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::Box<[T], C::LengthEncoding>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Box<[T], C::LengthEncoding>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T, C: Config> SchemaWrite<C> for Rc<[T]>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = Rc<[T::Src]>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::Rc<[T], C::LengthEncoding>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Rc<[T], C::LengthEncoding>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T, C: Config> SchemaWrite<C> for Arc<[T]>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = Arc<[T::Src]>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::Arc<[T], C::LengthEncoding>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        <containers::Arc<[T], C::LengthEncoding>>::write(writer, value)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for Box<[T]>
where
    T: SchemaRead<'de, C>,
{
    type Dst = Box<[T::Dst]>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Box<[T], C::LengthEncoding>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for Rc<[T]>
where
    T: SchemaRead<'de, C>,
{
    type Dst = Rc<[T::Dst]>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Rc<[T], C::LengthEncoding>>::read(reader, dst)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for Arc<[T]>
where
    T: SchemaRead<'de, C>,
{
    type Dst = Arc<[T::Dst]>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::Arc<[T], C::LengthEncoding>>::read(reader, dst)
    }
}

unsafe impl<C: Config> SchemaWrite<C> for str {
    type Src = str;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        Ok(C::LengthEncoding::write_bytes_needed(src.len())? + src.len())
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        C::LengthEncoding::write(writer, src.len())?;
        writer.write(src.as_bytes())?;
        Ok(())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<C: Config> SchemaWrite<C> for String {
    type Src = String;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <str as SchemaWrite<C>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        C::LengthEncoding::prealloc_check::<u8>(src.len())?;
        <str as SchemaWrite<C>>::write(writer, src)
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for &'de str {
    type Dst = &'de str;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = C::LengthEncoding::read(reader)?;
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
unsafe impl<'de, C: Config> SchemaRead<'de, C> for String {
    type Dst = String;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = C::LengthEncoding::read_prealloc_check::<u8>(reader)?;
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
    ($feature: literal, $target: ident<$key: ident : $($constraint:path)|*, $value: ident>, $with_capacity: expr) => {
        #[cfg(feature = $feature)]
        unsafe impl<C: Config, $key, $value> SchemaWrite<C> for $target<$key, $value>
        where
            $key: SchemaWrite<C>,
            $key::Src: Sized,
            $value: SchemaWrite<C>,
            $value::Src: Sized,
        {
            type Src = $target<$key::Src, $value::Src>;

            #[inline]
            #[allow(clippy::arithmetic_side_effects)]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                if let (TypeMeta::Static { size: key_size, .. }, TypeMeta::Static { size: value_size, .. }) = ($key::TYPE_META, $value::TYPE_META) {
                    return Ok(C::LengthEncoding::write_bytes_needed(src.len())? + (key_size + value_size) * src.len());
                }
                Ok(C::LengthEncoding::write_bytes_needed(src.len())? +
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
                if let (TypeMeta::Static { size: key_size, .. }, TypeMeta::Static { size: value_size, .. }) = ($key::TYPE_META, $value::TYPE_META) {
                    let len = src.len();
                    #[allow(clippy::arithmetic_side_effects)]
                    let needed = C::LengthEncoding::write_bytes_needed_prealloc_check::<($key, $value)>(len)? + (key_size + value_size) * len;
                    // SAFETY: `$key::TYPE_META` and `$value::TYPE_META` specify static sizes, so `len` writes of `($key::Src, $value::Src)`
                    // and `<BincodeLen>::write` will write `needed` bytes, fully initializing the trusted window.
                    let writer = &mut unsafe { writer.as_trusted_for(needed) }?;
                    C::LengthEncoding::write(writer, len)?;
                    for (k, v) in src.iter() {
                        $key::write(writer, k)?;
                        $value::write(writer, v)?;
                    }
                    writer.finish()?;
                    return Ok(());
                }
                C::LengthEncoding::write(writer, src.len())?;
                for (k, v) in src.iter() {
                    $key::write(writer, k)?;
                    $value::write(writer, v)?;
                }
                Ok(())
            }
        }

        #[cfg(feature = $feature)]
        unsafe impl<'de, C: Config, $key, $value> SchemaRead<'de, C> for $target<$key, $value>
        where
            $key: SchemaRead<'de, C>,
            $value: SchemaRead<'de, C>
            $(,$key::Dst: $constraint+)*,
        {
            type Dst = $target<$key::Dst, $value::Dst>;

            #[inline]
            fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let len = C::LengthEncoding::read_prealloc_check::<($key::Dst, $value::Dst)>(reader)?;

                let map = if let (TypeMeta::Static { size: key_size, .. }, TypeMeta::Static { size: value_size, .. }) = ($key::TYPE_META, $value::TYPE_META) {
                    #[allow(clippy::arithmetic_side_effects)]
                    // SAFETY: `$key::TYPE_META` and `$value::TYPE_META` specify static sizes, so `len` reads of `($key::Dst, $value::Dst)`
                    // will consume `(key_size + value_size) * len` bytes, fully consuming the trusted window.
                    let reader = &mut unsafe { reader.as_trusted_for((key_size + value_size) * len) }?;
                    let mut map = $with_capacity(len);
                    for _ in 0..len {
                        let k = $key::get(reader)?;
                        let v = $value::get(reader)?;
                        map.insert(k, v);
                    }
                    map
                } else {
                    let mut map = $with_capacity(len);
                    for _ in 0..len {
                        let k = $key::get(reader)?;
                        let v = $value::get(reader)?;
                        map.insert(k, v);
                    }
                    map
                };

                dst.write(map);
                Ok(())
            }
        }
    };

    ($feature: literal, $target: ident <$key: ident : $($constraint:path)|*>, $with_capacity: expr, $insert: ident) => {
        #[cfg(feature = $feature)]
        unsafe impl<C: Config, $key: SchemaWrite<C>> SchemaWrite<C> for $target<$key>
        where
            $key::Src: Sized,
        {
            type Src = $target<$key::Src>;

            #[inline]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                size_of_elem_iter::<$key, C::LengthEncoding, C>(src.iter())
            }

            #[inline]
            fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
                write_elem_iter_prealloc_check::<$key, C::LengthEncoding, C>(writer, src.iter())
            }
        }

        #[cfg(feature = $feature)]
        unsafe impl<'de, C: Config, $key> SchemaRead<'de, C> for $target<$key>
        where
            $key: SchemaRead<'de, C>
            $(,$key::Dst: $constraint+)*,
        {
            type Dst = $target<$key::Dst>;

            #[inline]
            fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let len = C::LengthEncoding::read_prealloc_check::<$key::Dst>(reader)?;

                let map = match $key::TYPE_META {
                    TypeMeta::Static { size, .. } => {
                        #[allow(clippy::arithmetic_side_effects)]
                        // SAFETY: `$key::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
                        // will consume `size * len` bytes, fully consuming the trusted window.
                        let reader = &mut unsafe { reader.as_trusted_for(size * len) }?;
                        let mut set = $with_capacity(len);
                        for _ in 0..len {
                            set.$insert($key::get(reader)?);
                        }
                        set
                    }
                    TypeMeta::Dynamic => {
                        let mut set = $with_capacity(len);
                        for _ in 0..len {
                            set.$insert($key::get(reader)?);
                        }
                        set
                    }
                };

                dst.write(map);
                Ok(())
            }
        }
    };
}

impl_seq! { "alloc", BTreeMap<K: Ord, V>, |_| BTreeMap::new() }
impl_seq! { "std", HashMap<K: Hash | Eq, V>, HashMap::with_capacity }
impl_seq! { "alloc", BTreeSet<K: Ord>, |_| BTreeSet::new(), insert }
impl_seq! { "std", HashSet<K: Hash | Eq>, HashSet::with_capacity, insert }
impl_seq! { "alloc", LinkedList<K:>, |_| LinkedList::new(), push_back }

#[cfg(feature = "alloc")]
unsafe impl<T, C: Config> SchemaWrite<C> for BinaryHeap<T>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = BinaryHeap<T::Src>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <containers::BinaryHeap<T, C::LengthEncoding>>::size_of(src)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        <containers::BinaryHeap<T, C::LengthEncoding>>::write(writer, src)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for BinaryHeap<T>
where
    T: SchemaRead<'de, C>,
    T::Dst: Ord,
{
    type Dst = BinaryHeap<T::Dst>;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        <containers::BinaryHeap<T, C::LengthEncoding>>::read(reader, dst)
    }
}

mod zero_copy {
    use {
        super::*,
        core::slice::{from_raw_parts, from_raw_parts_mut},
    };

    /// Ensure proper alignment for forming a reference of type `U` from a
    /// pointer of type `T`.
    ///
    /// This should trivially hold for all types supported by the crate,
    /// as we only mark zero-copy on `u8`, `i8`, and `[u/i8; N]` types.
    /// Additionally, all derived zero-copy types must be comprised entirely
    /// of aforementioned align-1 types.
    ///
    /// Note we include the `align_of > 1` check because it can be DCEd out
    /// for types we support (all align `1`).
    #[inline(always)]
    fn cast_ensure_aligned<C: ConfigCore, T, U>(ptr: *const T) -> ReadResult<*const U> {
        let ptr = ptr.cast::<U>();

        if !C::ZERO_COPY_ALIGN_CHECK {
            return Ok(ptr);
        }

        if align_of::<U>() > 1 && !ptr.is_aligned() {
            return Err(unaligned_pointer_read());
        }
        Ok(ptr)
    }

    /// Ensure proper alignment for forming a mutable reference of type `U` from a
    /// pointer of type `T`.
    ///
    /// See [`cast_ensure_aligned`] for more details.
    #[inline(always)]
    fn cast_ensure_aligned_mut<C: ConfigCore, T, U>(ptr: *mut T) -> ReadResult<*mut U> {
        let ptr = ptr.cast::<U>();

        if !C::ZERO_COPY_ALIGN_CHECK {
            return Ok(ptr);
        }

        if align_of::<U>() > 1 && !ptr.is_aligned() {
            return Err(unaligned_pointer_read());
        }
        Ok(ptr)
    }

    /// Cast a `&[u8]` to a `&T` of a zero-copy type `T`.
    ///
    /// Errors if the pointer is not properly aligned for reads of `T`.
    ///
    /// Note we abstract this into a function because it ensures the lifetime of the
    /// returned reference is the same as the input. Otherwise the compiler would
    /// accept any lifetime as `'de`. We want to preclude usage of something like
    /// `reader.fill_exact`, as its lifetime does not extend past the reader.
    ///
    /// # Safety
    /// - `T` must be a zero-copy type (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
    /// - `bytes.len()` must be equal to `size_of::<T>()`.
    #[inline(always)]
    pub(super) unsafe fn cast_slice_to_t<C: ConfigCore, T>(bytes: &[u8]) -> ReadResult<&T> {
        debug_assert_eq!(bytes.len(), size_of::<T>());
        let ptr = cast_ensure_aligned::<C, u8, T>(bytes.as_ptr())?;
        // SAFETY:
        // - The pointer is non-null, properly aligned for `&T`, and the length is valid.
        // - T is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        let val = unsafe { &*ptr };
        Ok(val)
    }

    /// Cast a `&mut [u8]` to a `&mut T` of a zero-copy type `T`.
    ///
    /// Like [`cast_slice_to_t`], but for mutable slices.
    #[inline(always)]
    pub(super) unsafe fn cast_slice_to_t_mut<C: ConfigCore, T>(
        bytes: &mut [u8],
    ) -> ReadResult<&mut T> {
        debug_assert_eq!(bytes.len(), size_of::<T>());
        let ptr = cast_ensure_aligned_mut::<C, u8, T>(bytes.as_mut_ptr())?;
        // SAFETY:
        // - The pointer is non-null, properly aligned for `&T`, and the length is valid.
        // - T is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        let val = unsafe { &mut *ptr };
        Ok(val)
    }

    /// Cast a `&[u8]` to a `&[T]` of a zero-copy type `T`.
    ///
    /// Errors if the pointer is not properly aligned for reads of `T`.
    ///
    /// Note we abstract this into a function because it ensures the lifetime of the
    /// returned reference is the same as the input. Otherwise the compiler would
    /// accept any lifetime as `'de`. We want to preclude usage of something like
    /// `reader.fill_exact`, as its lifetime does not extend past the reader.
    ///
    /// # Safety
    /// - `T` must be a zero-copy type (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
    /// - `bytes.len()` must be equal to `len * size_of::<T>()`.
    #[inline(always)]
    pub(super) unsafe fn cast_slice_to_slice_t<C: ConfigCore, T>(
        bytes: &[u8],
        len: usize,
    ) -> ReadResult<&[T]> {
        debug_assert_eq!(Some(bytes.len()), len.checked_mul(size_of::<T>()));
        let ptr = cast_ensure_aligned::<C, u8, T>(bytes.as_ptr())?;
        // SAFETY:
        // - The pointer is non-null, properly aligned for `&[T]`, and the length is valid.
        // - T is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        let slice = unsafe { from_raw_parts(ptr, len) };
        Ok(slice)
    }

    /// Cast a `&mut [u8]` to a `&mut [T]` of a zero-copy type `T`.
    ///
    /// Like [`cast_slice_to_slice_t`], but for mutable slices.
    #[inline(always)]
    pub(super) unsafe fn cast_slice_to_slice_t_mut<C: ConfigCore, T>(
        bytes: &mut [u8],
        len: usize,
    ) -> ReadResult<&mut [T]> {
        debug_assert_eq!(Some(bytes.len()), len.checked_mul(size_of::<T>()));
        let ptr = cast_ensure_aligned_mut::<C, u8, T>(bytes.as_mut_ptr())?;
        // SAFETY:
        // - The pointer is non-null, properly aligned for `&[T]`, and the length is valid.
        // - T is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        let slice = unsafe { from_raw_parts_mut(ptr, len) };
        Ok(slice)
    }

    /// [`TypeMeta`] for `&'de T` where `T` is zero-copy.
    pub(super) const fn type_meta_t<'de, T, C: ConfigCore>() -> TypeMeta
    where
        T: SchemaRead<'de, C> + ZeroCopy<C>,
    {
        match T::TYPE_META {
            TypeMeta::Static {
                size,
                zero_copy: true,
            } => TypeMeta::Static {
                size,
                // Note: `&'de T` is NOT zero‑copy in the "raw-bytes representable" sense.
                // In this crate, `zero_copy: true` means:
                // - The type's in‑memory representation is exactly its serialized bytes.
                // - It can be safely initialized by memcpy (no validation, no endianness/layout work).
                // - Containers may bulk-copy elements (e.g., Vec/BoxedSlice memcpy fast path for Pod).
                // - It can be deserialized by reference to some underlying source bytes.
                //
                // A _reference_ to a zero-copy type does not meet that contract:
                // - `&'de T` is a pointer with provenance/lifetime, not bytes you can memcpy into place.
                // - You cannot "initialize a reference" by copying bytes; you must point it at already
                //   valid storage of `T`.
                // - Advertising `zero_copy: true` here could incorrectly enable memcpy of reference
                //   elements (e.g., Vec<&T>), which would be unsound.
                //
                // We borrow the underlying `T` here, knowing it is zero-copy, but the reference itself
                // is never considered zero-copy.
                zero_copy: false,
            },
            // Should be impossible to reach.
            _ => panic!("Type is not zero-copy"),
        }
    }

    /// [`TypeMeta`] for &[T] where `T` is zero-copy.
    ///
    /// Slices are never zero-copy due to length encoding and
    /// references by their nature (as mentioned in [`type_meta_t`])
    /// are not zero-copy.
    pub(super) const fn type_meta_slice<'de, T, C: ConfigCore>() -> TypeMeta
    where
        T: SchemaRead<'de, C> + ZeroCopy<C>,
    {
        match T::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => TypeMeta::Dynamic,
            _ => panic!("Type is not zero-copy"),
        }
    }

    /// Read the length of the slice from the [`Reader`] and return it
    /// with the total size in bytes of the subsequent serialized data.
    ///
    /// Total size of the serialized data is the length of the slice
    /// multiplied by the size of the element type.
    #[inline(always)]
    pub(super) fn read_slice_len_checked<'de, C: Config>(
        reader: &mut impl Reader<'de>,
        size: usize,
    ) -> ReadResult<(usize, usize)> {
        let len = C::LengthEncoding::read(reader)?;
        let Some(total_size) = len.checked_mul(size) else {
            return Err(read_length_encoding_overflow("usize::MAX"));
        };
        Ok((len, total_size))
    }
}

unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for &'de T
where
    T: SchemaRead<'de, C> + ZeroCopy<C>,
{
    type Dst = &'de T::Dst;

    const TYPE_META: TypeMeta = zero_copy::type_meta_t::<T, C>();

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let size = T::TYPE_META.size_assert_zero_copy();
        let bytes = reader.borrow_exact(size)?;
        // SAFETY:
        // - T::Dst is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        // - `bytes.len() == size_of::<T::Dst>()`. `borrow_exact` ensures we read exactly `size` bytes.
        let val = unsafe { zero_copy::cast_slice_to_t::<C, T::Dst>(bytes)? };
        dst.write(val);
        Ok(())
    }
}

unsafe impl<'de, T, C: ConfigCore> SchemaRead<'de, C> for &'de mut T
where
    T: SchemaRead<'de, C> + ZeroCopy<C>,
{
    type Dst = &'de mut T::Dst;

    const TYPE_META: TypeMeta = zero_copy::type_meta_t::<T, C>();

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let size = T::TYPE_META.size_assert_zero_copy();
        let bytes = reader.borrow_exact_mut(size)?;
        // SAFETY:
        // - T::Dst is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        // - `bytes.len() == size_of::<T::Dst>()`. `borrow_exact_mut` ensures we read exactly `size` bytes.
        let val = unsafe { zero_copy::cast_slice_to_t_mut::<C, T::Dst>(bytes)? };
        dst.write(val);
        Ok(())
    }
}

unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for &'de [T]
where
    T: SchemaRead<'de, C> + ZeroCopy<C>,
{
    type Dst = &'de [T::Dst];

    const TYPE_META: TypeMeta = zero_copy::type_meta_slice::<T, C>();

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let size = T::TYPE_META.size_assert_zero_copy();
        let (len, total_size) = zero_copy::read_slice_len_checked::<C>(reader, size)?;
        let bytes = reader.borrow_exact(total_size)?;
        // SAFETY:
        // - T::Dst is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        // - `bytes.len() == len * size_of::<T::Dst>()`.`borrow_exact` ensures we read exactly `len * size` bytes.
        let slice = unsafe { zero_copy::cast_slice_to_slice_t::<C, T::Dst>(bytes, len)? };
        dst.write(slice);
        Ok(())
    }
}

unsafe impl<'de, T, C: Config> SchemaRead<'de, C> for &'de mut [T]
where
    T: SchemaRead<'de, C> + ZeroCopy<C>,
{
    type Dst = &'de mut [T::Dst];

    const TYPE_META: TypeMeta = zero_copy::type_meta_slice::<T, C>();

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let size = T::TYPE_META.size_assert_zero_copy();
        let (len, total_size) = zero_copy::read_slice_len_checked::<C>(reader, size)?;
        let bytes = reader.borrow_exact_mut(total_size)?;
        // SAFETY:
        // - T::Dst is zero-copy (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
        // - `bytes.len() == len * size_of::<T::Dst>()`.`borrow_exact_mut` ensures we read exactly `len * size` bytes.
        let slice = unsafe { zero_copy::cast_slice_to_slice_t_mut::<C, T::Dst>(bytes, len)? };
        dst.write(slice);
        Ok(())
    }
}

unsafe impl<C: ConfigCore> SchemaWrite<C> for Duration {
    type Src = Duration;

    const TYPE_META: TypeMeta = match (
        <u64 as SchemaWrite<C>>::TYPE_META,
        <u32 as SchemaWrite<C>>::TYPE_META,
    ) {
        // both static
        (TypeMeta::Static { size: u64_size, .. }, TypeMeta::Static { size: u32_size, .. }) => {
            TypeMeta::Static {
                size: u64_size + u32_size,
                zero_copy: false,
            }
        }
        _ => TypeMeta::Dynamic,
    };

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        match <Self as SchemaWrite<C>>::TYPE_META {
            TypeMeta::Static { size, .. } => Ok(size),
            TypeMeta::Dynamic => {
                let secs = <u64 as SchemaWrite<C>>::size_of(&src.as_secs())?;
                let nanos = <u32 as SchemaWrite<C>>::size_of(&src.subsec_nanos())?;
                Ok(secs + nanos)
            }
        }
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        <u64 as SchemaWrite<C>>::write(writer, &src.as_secs())?;
        <u32 as SchemaWrite<C>>::write(writer, &src.subsec_nanos())?;
        Ok(())
    }
}

unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for Duration {
    type Dst = Duration;

    const TYPE_META: TypeMeta = <Duration as SchemaWrite<C>>::TYPE_META;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let secs = <u64 as SchemaRead<'de, C>>::get(reader)?;
        let nanos = <u32 as SchemaRead<'de, C>>::get(reader)?;
        if secs.checked_add(u64::from(nanos) / 1_000_000_000).is_none() {
            return Err(invalid_value("Duration overflow"));
        }
        dst.write(Duration::new(secs, nanos));
        Ok(())
    }
}

#[cfg(feature = "std")]
unsafe impl<C: ConfigCore> SchemaWrite<C> for SystemTime {
    type Src = SystemTime;

    const TYPE_META: TypeMeta = <Duration as SchemaWrite<C>>::TYPE_META;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        match <Self as SchemaWrite<C>>::TYPE_META {
            TypeMeta::Static { size, .. } => Ok(size),
            TypeMeta::Dynamic => {
                let duration = src.duration_since(UNIX_EPOCH).map_err(|_| {
                    crate::error::WriteError::Custom("SystemTime before UNIX_EPOCH")
                })?;
                <Duration as SchemaWrite<C>>::size_of(&duration)
            }
        }
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        let duration = src
            .duration_since(UNIX_EPOCH)
            .map_err(|_| crate::error::WriteError::Custom("SystemTime before UNIX_EPOCH"))?;
        <Duration as SchemaWrite<C>>::write(writer, &duration)?;
        Ok(())
    }
}

#[cfg(feature = "std")]
unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for SystemTime {
    type Dst = SystemTime;

    const TYPE_META: TypeMeta = <Duration as SchemaRead<'de, C>>::TYPE_META;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let duration = <Duration as SchemaRead<'de, C>>::get(reader)?;
        let system_time = UNIX_EPOCH
            .checked_add(duration)
            .ok_or_else(|| invalid_value("SystemTime overflow"))?;
        dst.write(system_time);
        Ok(())
    }
}

unsafe impl<C: ConfigCore> SchemaWrite<C> for Ipv4Addr {
    type Src = Ipv4Addr;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 4,
        zero_copy: false,
    };

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(4)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        writer.write(&src.octets())?;
        Ok(())
    }
}

unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for Ipv4Addr {
    type Dst = Ipv4Addr;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 4,
        zero_copy: false,
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let bytes = *reader.fill_array::<4>()?;
        // SAFETY: `fill_array` guarantees 4 bytes are available
        unsafe { reader.consume_unchecked(4) };
        dst.write(Ipv4Addr::from(bytes));
        Ok(())
    }
}

unsafe impl<C: ConfigCore> SchemaWrite<C> for Ipv6Addr {
    type Src = Ipv6Addr;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 16,
        zero_copy: false,
    };

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        Ok(16)
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        writer.write(&src.octets())?;
        Ok(())
    }
}

unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for Ipv6Addr {
    type Dst = Ipv6Addr;

    const TYPE_META: TypeMeta = TypeMeta::Static {
        size: 16,
        zero_copy: false,
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let bytes = *reader.fill_array::<16>()?;
        // SAFETY: `fill_array` guarantees 16 bytes are available
        unsafe { reader.consume_unchecked(16) };
        dst.write(Ipv6Addr::from(bytes));
        Ok(())
    }
}

unsafe impl<C: Config> SchemaWrite<C> for IpAddr {
    type Src = IpAddr;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        Ok(match src {
            IpAddr::V4(_) => C::TagEncoding::size_of_from_u32(0)? + 4,
            IpAddr::V6(_) => C::TagEncoding::size_of_from_u32(1)? + 16,
        })
    }

    #[inline]
    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        match src {
            IpAddr::V4(addr) => {
                C::TagEncoding::write_from_u32(writer, 0)?;
                <Ipv4Addr as SchemaWrite<C>>::write(writer, addr)
            }
            IpAddr::V6(addr) => {
                C::TagEncoding::write_from_u32(writer, 1)?;
                <Ipv6Addr as SchemaWrite<C>>::write(writer, addr)
            }
        }
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for IpAddr {
    type Dst = IpAddr;

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let tag = C::TagEncoding::try_into_u32(C::TagEncoding::get(reader)?)?;
        match tag {
            0 => {
                let addr = <Ipv4Addr as SchemaRead<'de, C>>::get(reader)?;
                dst.write(IpAddr::V4(addr));
                Ok(())
            }
            1 => {
                let addr = <Ipv6Addr as SchemaRead<'de, C>>::get(reader)?;
                dst.write(IpAddr::V6(addr));
                Ok(())
            }
            _ => Err(invalid_tag_encoding(tag as usize)),
        }
    }
}
