use {
    crate::{
        io::{Reader, Writer},
        len::SeqLen,
        schema::impls::{impl_seq_kv, impl_seq_v},
    },
    core::hash::{BuildHasher, Hash},
    indexmap::{IndexMap, IndexSet},
};

impl_seq_kv! { "indexmap", IndexMap<K: Hash | Eq, V, S: BuildHasher | Default>, IndexMap::with_capacity_and_hasher }
impl_seq_v! { "indexmap", IndexSet<K: Hash | Eq, S: BuildHasher | Default>, IndexSet::with_capacity_and_hasher, insert }

#[cfg(test)]
mod tests {
    use {
        crate::{deserialize, proptest_config::proptest_cfg, serialize},
        indexmap::{IndexMap, IndexSet},
        proptest::prelude::*,
        std::collections::hash_map::RandomState,
    };

    type TestIndexMap<K, V> = IndexMap<K, V, RandomState>;
    type TestIndexSet<T> = IndexSet<T, RandomState>;

    #[test]
    fn test_index_map_insertion_order_roundtrip() {
        let map: TestIndexMap<u8, u8> = IndexMap::from_iter([(3u8, 30u8), (1, 10), (2, 20)]);
        let serialized = serialize(&map).unwrap();
        let deserialized: TestIndexMap<u8, u8> = deserialize(&serialized).unwrap();
        assert_eq!(
            deserialized.keys().copied().collect::<Vec<_>>(),
            vec![3, 1, 2]
        );
        assert_eq!(deserialized, map);
    }

    #[test]
    fn test_index_set_insertion_order_roundtrip() {
        let set: TestIndexSet<u8> = IndexSet::from_iter([3u8, 1, 2]);
        let serialized = serialize(&set).unwrap();
        let deserialized: TestIndexSet<u8> = deserialize(&serialized).unwrap();
        assert_eq!(
            deserialized.iter().copied().collect::<Vec<_>>(),
            vec![3, 1, 2]
        );
        assert_eq!(deserialized, set);
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_index_map_static(map in proptest::collection::vec((any::<u64>(), any::<u64>()), 0..=100).prop_map(|entries| entries.into_iter().collect::<TestIndexMap<_, _>>())) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: TestIndexMap<u64, u64> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: TestIndexMap<u64, u64> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_index_map_non_static(map in proptest::collection::vec((any::<u64>(), any::<String>()), 0..=16).prop_map(|entries| entries.into_iter().collect::<TestIndexMap<_, _>>())) {
            let bincode_serialized = bincode::serialize(&map).unwrap();
            let schema_serialized = serialize(&map).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: TestIndexMap<u64, String> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: TestIndexMap<u64, String> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&map, &bincode_deserialized);
            prop_assert_eq!(map, schema_deserialized);
        }

        #[test]
        fn test_index_set_static(set in proptest::collection::vec(any::<u64>(), 0..=100).prop_map(|entries| entries.into_iter().collect::<TestIndexSet<_>>())) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: TestIndexSet<u64> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: TestIndexSet<u64> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }

        #[test]
        fn test_index_set_non_static(set in proptest::collection::vec(any::<String>(), 0..=16).prop_map(|entries| entries.into_iter().collect::<TestIndexSet<_>>())) {
            let bincode_serialized = bincode::serialize(&set).unwrap();
            let schema_serialized = serialize(&set).unwrap();
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: TestIndexSet<String> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: TestIndexSet<String> = deserialize(&schema_serialized).unwrap();
            prop_assert_eq!(&set, &bincode_deserialized);
            prop_assert_eq!(set, schema_deserialized);
        }
    }
}
