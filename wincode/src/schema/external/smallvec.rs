use {
    crate::{
        ReadResult, SchemaRead, SchemaWrite, WriteResult,
        config::Config,
        containers::decode_into_slice_t,
        io::{Reader, Writer},
        len::SeqLen,
        schema::{size_of_elem_slice, write_elem_slice_prealloc_check},
    },
    core::{mem::MaybeUninit, slice::from_raw_parts_mut},
    smallvec::SmallVec,
};

unsafe impl<T, const N: usize, C: Config> SchemaWrite<C> for SmallVec<[T; N]>
where
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = SmallVec<[T::Src; N]>;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_slice::<T, C::LengthEncoding, C>(src)
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_slice_prealloc_check::<T, C::LengthEncoding, C>(writer, src)
    }
}

unsafe impl<'de, T, const N: usize, C: Config> SchemaRead<'de, C> for SmallVec<[T; N]>
where
    T: SchemaRead<'de, C>,
{
    type Dst = SmallVec<[T::Dst; N]>;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = C::LengthEncoding::read_prealloc_check::<T::Dst>(reader.by_ref())?;

        // Reserve capacity through `dst` in place. Moving a `SmallVec::with_capacity(len)`
        // local into `dst` would memcpy its whole `[T::Dst; N]` inline region;
        // building empty in `dst` and growing in place leaves that region uninit.
        let values = dst.write(SmallVec::new());
        values.reserve_exact(len);

        // `dst` now owns a reserved (possibly heap) allocation, but the caller
        // still treats it as uninitialized and will not drop it. Free it on any
        // early exit -- an `Err` return *or* a panic while decoding -- so the
        // allocation cannot leak. The guard is disarmed only once `dst` holds the
        // fully initialized value.
        struct Guard<'a, U>(&'a mut MaybeUninit<U>);
        impl<U> Drop for Guard<'_, U> {
            fn drop(&mut self) {
                // SAFETY: the guard is only live while `dst` holds an empty
                // `SmallVec` (length 0 until the guard is disarmed), so this drops
                // just the reserved allocation, never any element.
                unsafe { self.0.assume_init_drop() };
            }
        }
        let guard = Guard(dst);

        // SAFETY: `dst` was initialized with the empty `SmallVec` above.
        let ptr: *mut T::Dst = unsafe { guard.0.assume_init_mut() }.as_mut_ptr();
        // SAFETY: the buffer has capacity for `len` elements. On error (or panic)
        // `decode_into_slice_t` drops any elements it initialized; on success it
        // initializes all `len` of them.
        let slice = unsafe { from_raw_parts_mut(ptr.cast::<MaybeUninit<T::Dst>>(), len) };
        decode_into_slice_t::<T, C>(reader, slice)?;

        // SAFETY: `decode_into_slice_t` initialized all `len` elements on success.
        unsafe { guard.0.assume_init_mut().set_len(len) };
        // `dst` now fully owns the value; keep it rather than dropping via `guard`.
        core::mem::forget(guard);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        crate::{deserialize, proptest_config::proptest_cfg, serialize},
        proptest::prelude::*,
        smallvec::{SmallVec, smallvec},
    };

    type SmallVec4<T> = SmallVec<[T; 4]>;

    #[test]
    fn test_smallvec_inline_roundtrip() {
        let value: SmallVec4<u8> = smallvec![1u8, 2, 3];
        let serialized = serialize(&value).unwrap();
        let deserialized: SmallVec4<u8> = deserialize(&serialized).unwrap();
        assert_eq!(deserialized, value);
    }

    #[test]
    fn test_smallvec_spilled_roundtrip() {
        let value: SmallVec4<u8> = smallvec![1u8, 2, 3, 4, 5];
        let serialized = serialize(&value).unwrap();
        let deserialized: SmallVec4<u8> = deserialize(&serialized).unwrap();
        assert_eq!(deserialized, value);
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_smallvec_static(value in proptest::collection::vec(any::<u64>(), 0..=100).prop_map(SmallVec4::from_vec)) {
            let bincode_serialized = bincode::serialize(&value).unwrap();
            let schema_serialized = serialize(&value).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: SmallVec4<u64> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: SmallVec4<u64> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&value, &bincode_deserialized);
            prop_assert_eq!(value, schema_deserialized);
        }

        #[test]
        fn test_smallvec_non_static(value in proptest::collection::vec(any::<String>(), 0..=16).prop_map(SmallVec4::from_vec)) {
            let bincode_serialized = bincode::serialize(&value).unwrap();
            let schema_serialized = serialize(&value).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: SmallVec4<String> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: SmallVec4<String> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&value, &bincode_deserialized);
            prop_assert_eq!(value, schema_deserialized);
        }
    }
}
