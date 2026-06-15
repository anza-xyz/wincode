use {
    crate::{
        ReadResult, SchemaRead, SchemaReadContext, SchemaWrite, TypeMeta, WriteResult,
        config::{Config, ConfigCore},
        containers::decode_into_slice_t,
        error::invalid_utf8_encoding,
        io::{Reader, Writer},
        len::SeqLen,
        schema::{size_of_elem_slice, write_elem_slice_prealloc_check},
    },
    alloc::alloc::Layout,
    bumpalo::{
        Bump,
        boxed::Box,
        collections::{String, Vec},
    },
    core::{mem::MaybeUninit, slice::from_raw_parts_mut},
};

unsafe impl<'de, 'bump, C: Config, T> SchemaReadContext<'de, C, &'bump Bump> for Vec<'bump, T>
where
    T: SchemaRead<'de, C>,
    T::Dst: 'bump,
{
    type Dst = Vec<'bump, T::Dst>;

    #[inline]
    fn read_with_context(
        ctx: &'bump Bump,
        mut reader: impl Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> ReadResult<()> {
        let len = C::LengthEncoding::read_prealloc_check::<T::Dst>(reader.by_ref())?;
        let mut vec: Vec<'bump, T::Dst> = Vec::with_capacity_in(len, ctx);
        // SAFETY: `Vec::with_capacity_in(len, ctx)` allocated storage for at
        // least `len` elements, and `as_mut_ptr` points to that uninitialized
        // storage while `vec` is alive and not reallocated.
        let slice = unsafe { from_raw_parts_mut(vec.as_mut_ptr().cast::<MaybeUninit<_>>(), len) };
        decode_into_slice_t::<T, C>(reader, slice)?;
        // SAFETY: `decode_into_slice_t` initializes all `len` elements on success.
        unsafe { vec.set_len(len) };

        dst.write(vec);
        Ok(())
    }
}

unsafe impl<'bump, C: Config, T> SchemaWrite<C> for Vec<'bump, T>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = Vec<'bump, T::Src>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, C::LengthEncoding, C>(src)
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_slice_prealloc_check::<T, C::LengthEncoding, C>(writer, src)
    }
}

unsafe impl<'de, 'bump, C: Config> SchemaReadContext<'de, C, &'bump Bump> for String<'bump> {
    type Dst = String<'bump>;

    #[inline]
    fn read_with_context(
        ctx: &'bump Bump,
        reader: impl Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> ReadResult<()> {
        let bytes = <Vec<u8> as SchemaReadContext<C, _>>::get_with_context(ctx, reader)?;
        match String::from_utf8(bytes) {
            Ok(s) => {
                dst.write(s);
                Ok(())
            }
            Err(e) => Err(invalid_utf8_encoding(e.utf8_error())),
        }
    }
}

unsafe impl<'bump, C: Config> SchemaWrite<C> for String<'bump> {
    type Src = String<'bump>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <str as SchemaWrite<C>>::size_of(src)
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        C::LengthEncoding::prealloc_check::<u8>(src.len())?;
        <str as SchemaWrite<C>>::write(writer, src)
    }
}

unsafe impl<'de, 'bump, C: ConfigCore, T> SchemaReadContext<'de, C, &'bump Bump> for Box<'bump, T>
where
    T: SchemaRead<'de, C>,
    T::Dst: 'bump,
{
    type Dst = Box<'bump, T::Dst>;

    const TYPE_META: TypeMeta = T::TYPE_META.keep_zero_copy(false);

    #[inline]
    fn read_with_context(
        ctx: &'bump Bump,
        reader: impl Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> ReadResult<()> {
        let ptr = ctx.alloc_layout(Layout::new::<T::Dst>()).as_ptr();

        // SAFETY: `ptr` was allocated with `Layout::new::<T::Dst>()`, so it is
        // non-null, properly aligned, and valid for one `MaybeUninit<T::Dst>`.
        T::read(reader, unsafe { &mut *ptr.cast::<MaybeUninit<T::Dst>>() })?;
        // SAFETY: `T::read` initialized the allocation on success, and
        // `Box::from_raw` accepts pointers allocated by this `Bump`.
        let boxed = unsafe { Box::from_raw(ptr.cast::<T::Dst>()) };
        dst.write(boxed);

        Ok(())
    }
}

unsafe impl<'bump, C: ConfigCore, T> SchemaWrite<C> for Box<'bump, T>
where
    T: SchemaWrite<C>,
{
    type Src = Box<'bump, T::Src>;

    const TYPE_META: TypeMeta = T::TYPE_META.keep_zero_copy(false);

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <T as SchemaWrite<C>>::size_of(src)
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        <T as SchemaWrite<C>>::write(writer, src)
    }
}

/// Borrowed elements in bumpalo containers must not outlive the input bytes they reference.
///
/// ```compile_fail
/// use bumpalo::{Bump, collections::Vec};
/// use wincode::{deserialize_with_context, serialize};
///
/// let bump = Bump::new();
/// let deserialized: Vec<&[u8]>;
///
/// {
///     let src = [b"borrowed".as_slice()];
///     let serialized = serialize(&src[..]).unwrap();
///     deserialized = deserialize_with_context(&bump, &serialized).unwrap();
/// }
///
/// assert_eq!(deserialized[0], b"borrowed");
/// ```
#[expect(dead_code)]
fn bumpalo_vec_of_borrowed_slices_cannot_outlive_input() {}

/// References to elements stored in bumpalo containers must not outlive the container.
///
/// ```compile_fail
/// use bumpalo::{Bump, collections::Vec};
/// use wincode::{deserialize_with_context, serialize};
///
/// let serialized = serialize(&[b"borrowed".as_slice()][..]).unwrap();
/// let slot_ref: &&[u8];
///
/// {
///     let bump = Bump::new();
///     let vec: Vec<&[u8]> = deserialize_with_context(&bump, &serialized).unwrap();
///     slot_ref = &vec[0];
/// }
///
/// assert_eq!(*slot_ref, b"borrowed");
/// ```
#[expect(dead_code)]
fn bumpalo_vec_element_references_cannot_outlive_container() {}

/// Owned bumpalo values must not outlive the `Bump` allocator that stores their contents.
///
/// ```compile_fail
/// use bumpalo::{Bump, collections::String};
/// use wincode::{deserialize_with_context, serialize};
///
/// let deserialized: String;
///
/// {
///     let bump = Bump::new();
///     let serialized = serialize("owned in bump").unwrap();
///     deserialized = deserialize_with_context(&bump, &serialized).unwrap();
/// }
///
/// assert_eq!(deserialized.as_str(), "owned in bump");
/// ```
#[expect(dead_code)]
fn bumpalo_owned_values_cannot_outlive_arena() {}

/// Borrowed values from bumpalo-backed input bytes must not outlive the input buffer.
///
/// ```compile_fail
/// use bumpalo::{Bump, collections::Vec};
/// use wincode::{deserialize, serialize};
///
/// let deserialized: &[u8];
///
/// {
///     let bump = Bump::new();
///     let serialized = serialize(b"borrowed".as_slice()).unwrap();
///     let bytes = Vec::from_iter_in(serialized, &bump);
///     deserialized = deserialize(&bytes).unwrap();
/// }
///
/// assert_eq!(deserialized, b"borrowed");
/// ```
#[expect(dead_code)]
fn borrowed_values_from_bumpalo_input_cannot_outlive_input_buffer() {}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{deserialize_with_context, proptest_config::proptest_cfg, serialize},
        proptest::prelude::*,
    };

    #[test]
    fn vec_round_trip() {
        proptest!(proptest_cfg(), |(val: alloc::vec::Vec<u64>)| {
            let bump = Bump::new();
            let val = Vec::from_iter_in(val, &bump);

            let serialized = serialize(&val).unwrap();

            let deserialized: Vec<u64> = deserialize_with_context(&bump, &serialized).unwrap();
            prop_assert_eq!(deserialized, val);
        });
    }

    #[test]
    fn string_round_trip() {
        proptest!(proptest_cfg(), |(val: alloc::string::String)| {
            let bump = Bump::new();
            let val = String::from_str_in(&val, &bump);

            let serialized = serialize(&val).unwrap();

            let deserialized: String = deserialize_with_context(&bump, &serialized).unwrap();
            prop_assert_eq!(deserialized, val);
        });
    }

    #[test]
    fn box_round_trip() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq, proptest_derive::Arbitrary)]
        #[wincode(internal)]
        struct Test {
            foo: u64,
            bar: alloc::string::String,
            baz: bool,
        }

        proptest!(proptest_cfg(), |(val: Test)| {
            let bump = Bump::new();
            let val = Box::new_in(val, &bump);

            let serialized = serialize(&val).unwrap();

            let deserialized: Box<Test> = deserialize_with_context(&bump, &serialized).unwrap();
            prop_assert_eq!(deserialized, val);
        });
    }

    /// Owned bumpalo values can outlive the input bytes because their contents live in the `Bump`.
    #[test]
    fn owned_string_can_outlive_input_bytes() {
        let bump = Bump::new();
        let deserialized: String;

        {
            // bumpalo::String owns its contents, so `deserialized` should outlive the block,
            // even though input bytes are temporary.
            let serialized = serialize("owned in bump").unwrap();
            deserialized = deserialize_with_context(&bump, &serialized).unwrap();
        }

        assert_eq!(deserialized.as_str(), "owned in bump");
    }

    /// Copied element references can outlive the bumpalo container they were stored in.
    #[test]
    fn copied_input_borrow_can_outlive_bumpalo_container() {
        let serialized = serialize(&[b"borrowed".as_slice()][..]).unwrap();
        let bytes_ref: &[u8];

        {
            let bump = Bump::new();
            let vec: Vec<&[u8]> = deserialize_with_context(&bump, &serialized).unwrap();
            bytes_ref = vec[0];
        }

        assert_eq!(bytes_ref, b"borrowed");
    }
}
