use {
    crate::{
        config::Config,
        error::{ReadResult, WriteResult, WriteError},
        io::{Reader, Writer},
        len::SeqLen,
        schema::{TypeMeta, SchemaRead, SchemaWrite, size_of_elem_iter, write_elem_iter_prealloc_check},
    },
    core::{hash::Hash, mem::MaybeUninit},
    indexmap::{IndexMap, IndexSet}
};

#[cfg(feature = "indexmap")]
unsafe impl<C: Config, K, V> SchemaWrite<C> for IndexMap<K, V>
where
    K: SchemaWrite<C>,
    K::Src: Sized,
    V: SchemaWrite<C>,
    V::Src: Sized,
{
    type Src = IndexMap<K::Src, V::Src>;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        if let (
            TypeMeta::Static { size: key_size, .. },
            TypeMeta::Static { size: value_size, .. },
        ) = (K::TYPE_META, V::TYPE_META)
        {
            return Ok(
                C::LengthEncoding::write_bytes_needed(src.len())?
                + (key_size + value_size) * src.len()
            );
        }
        Ok(
            C::LengthEncoding::write_bytes_needed(src.len())?
            + src.iter().try_fold(0usize, |acc, (k, v)|
                Ok::<_, WriteError>(acc + K::size_of(k)? + V::size_of(v)?)
            )?
        )
    }

    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        if let (
            TypeMeta::Static { size: key_size, .. },
            TypeMeta::Static { size: value_size, .. },
        ) = (K::TYPE_META, V::TYPE_META)
        {
            let len = src.len();
            let needed =
                C::LengthEncoding::write_bytes_needed_prealloc_check::<(K, V)>(len)?
                + (key_size + value_size) * len;
            // SAFETY: `K::TYPE_META` and `V::TYPE_META` specify static sizes, so `len` writes of `(K::Src, V::Src)`
            // and `<BincodeLen>::write` will write `needed` bytes, fully initializing the trusted window.
            let writer = &mut unsafe { writer.as_trusted_for(needed) }?;
            C::LengthEncoding::write(writer, len)?;

            for (k, v) in src {
                K::write(writer, k)?;
                V::write(writer, v)?;
            }

            writer.finish()?;
            Ok(())
        } else {
            C::LengthEncoding::write(writer, src.len())?;
            for (k, v) in src {
                K::write(writer, k)?;
                V::write(writer, v)?;
            }
            Ok(())
        }
    }
}

#[cfg(feature = "indexmap")]
unsafe impl<'de, C: Config, K, V> SchemaRead<'de, C> for IndexMap<K, V>
where
    K: SchemaRead<'de, C>,
    V: SchemaRead<'de, C>,
    K::Dst: Hash + Eq,
{
    type Dst = IndexMap<K::Dst, V::Dst>;

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len =
            C::LengthEncoding::read_prealloc_check::<(K::Dst, V::Dst)>(reader)?;

        let mut map = IndexMap::with_capacity(len);

        if let (
            TypeMeta::Static { size: key_size, .. },
            TypeMeta::Static { size: value_size, .. },
        ) = (K::TYPE_META, V::TYPE_META)
        {
            let reader =
                &mut unsafe { reader.as_trusted_for((key_size + value_size) * len) }?;
            for _ in 0..len {
                map.insert(K::get(reader)?, V::get(reader)?);
            }
        } else {
            for _ in 0..len {
                map.insert(K::get(reader)?, V::get(reader)?);
            }
        }

        dst.write(map);
        Ok(())
    }
}

#[cfg(feature = "indexmap")]
unsafe impl<C: Config, K> SchemaWrite<C> for IndexSet<K>
where
    K: SchemaWrite<C>,
    K::Src: Sized,
{
    type Src = IndexSet<K::Src>;

    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        size_of_elem_iter::<K, C::LengthEncoding, C>(src.iter())
    }

    fn write(writer: &mut impl Writer, src: &Self::Src) -> WriteResult<()> {
        write_elem_iter_prealloc_check::<K, C::LengthEncoding, C>(writer, src.iter())
    }
}

#[cfg(feature = "indexmap")]
unsafe impl<'de, C: Config, K> SchemaRead<'de, C> for IndexSet<K>
where
    K: SchemaRead<'de, C>,
    K::Dst: Hash + Eq,
{
    type Dst = IndexSet<K::Dst>;

    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len =
            C::LengthEncoding::read_prealloc_check::<K::Dst>(reader)?;

        let mut set = IndexSet::with_capacity(len);

        match K::TYPE_META {
            TypeMeta::Static { size, .. } => {
                #[allow(clippy::arithmetic_side_effects)]
                // SAFETY: `K::TYPE_META` specifies a static size, so `len` reads of `T::Dst`
                // will consume `size * len` bytes, fully consuming the trusted window.
                let reader =
                    &mut unsafe { reader.as_trusted_for(size * len) }?;
                for _ in 0..len {
                    set.insert(K::get(reader)?);
                }
            }
            TypeMeta::Dynamic => {
                for _ in 0..len {
                    set.insert(K::get(reader)?);
                }
            }
        }

        dst.write(set);
        Ok(())
    }
}


#[cfg(all(test, feature = "std", feature = "derive"))]
mod tests {
    #![allow(clippy::arithmetic_side_effects, deprecated)]
    
    use {
        crate::{
            serialize, deserialize,
            proptest_config::proptest_cfg,
        },
        wincode_derive::{SchemaRead, SchemaWrite},
        proptest::prelude::*,
        indexmap::{IndexMap, IndexSet}
    };
    #[cfg(target_endian = "little")]
    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
        Clone,
        Copy,
    )]
    #[wincode(internal)]
    #[repr(C)]
    struct StructZeroCopy {
        a: u128,
        b: i128,
        c: u64,
        d: i64,
        e: u32,
        f: i32,
        ar1: [u8; 8],
        g: u16,
        h: i16,
        ar2: [u8; 12],
        i: u8,
        j: i8,
        ar3: [u8; 14],
    }

    #[cfg(not(target_endian = "little"))]
    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
        Clone,
        Copy,
    )]
    #[wincode(internal)]
    #[repr(C)]
    struct StructZeroCopy {
        byte: u8,
        ar: [u8; 32],
    }

    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
    )]
    #[wincode(internal)]
    struct StructStatic {
        a: u64,
        b: bool,
        e: [u8; 32],
    }

    #[derive(
        serde::Serialize,
        serde::Deserialize,
        Debug,
        PartialEq,
        Eq,
        Ord,
        PartialOrd,
        SchemaWrite,
        SchemaRead,
        proptest_derive::Arbitrary,
        Hash,
    )]
    #[wincode(internal)]
    struct StructNonStatic {
        a: u64,
        b: bool,
        e: String,
    }
    // We create Helper functions to create strategies for both IndexMap and IndexSet,
    //since they both implement Arbitrary from the arbitrary crate directly but not from 
    // proptest::Arbitrary 
    fn index_map_strategy<K, V>(
        key_strategy: impl Strategy<Value = K>,
        value_strategy: impl Strategy<Value = V>,
        size: impl Into<proptest::collection::SizeRange>,
    ) -> impl Strategy<Value = IndexMap<K, V>>
    where
        K: std::fmt::Debug + std::hash::Hash + Eq,
        V: std::fmt::Debug,
    {
        proptest::collection::vec((key_strategy, value_strategy), size)
            .prop_map(|vec| vec.into_iter().collect())
    }

    fn index_set_strategy<T>(
        element_strategy: impl Strategy<Value = T>,
        size: impl Into<proptest::collection::SizeRange>,
    ) -> impl Strategy<Value = IndexSet<T>>
    where
        T: std::fmt::Debug + std::hash::Hash + Eq,
    {
        proptest::collection::vec(element_strategy, size)
            .prop_map(|vec| vec.into_iter().collect())
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_index_map_zero_copy(
            map in index_map_strategy(any::<u8>(), any::<StructZeroCopy>(), 0..20)
        ) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            
            let bincode_deserialized: IndexMap<u8, StructZeroCopy> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: IndexMap<u8, StructZeroCopy> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }
        
        #[test]
        fn test_index_map_static(
            map in index_map_strategy(any::<u64>(), any::<StructStatic>(), 0..20)
        ) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            
            let bincode_deserialized: IndexMap<u64, StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: IndexMap<u64, StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }
        
        #[test]
        fn test_index_map_non_static(
            map in index_map_strategy(any::<u64>(), any::<StructNonStatic>(), 0..20)
        ) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            
            let bincode_deserialized: IndexMap<u64, StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: IndexMap<u64, StructNonStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }
        
        #[test]
        fn test_index_set_zero_copy(
            set in index_set_strategy(any::<StructZeroCopy>(), 0..20)
        ) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            
            let bincode_deserialized: IndexSet<StructZeroCopy> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: IndexSet<StructZeroCopy> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }
        
        #[test]
        fn test_index_set_static(
            set in index_set_strategy(any::<StructStatic>(), 0..20)
        ) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            
            let bincode_deserialized: IndexSet<StructStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: IndexSet<StructStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }
        
        #[test]
        fn test_index_set_non_static(
            set in index_set_strategy(any::<StructNonStatic>(), 0..20)
        ) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);
            
            let bincode_deserialized: IndexSet<StructNonStatic> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: IndexSet<StructNonStatic> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }
    }
}
