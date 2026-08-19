#[cfg(feature = "std")]
use std::collections::hash_map::RandomState;
use {
    crate::containers::{map_container, set_container},
    core::hash::{BuildHasher, Hash},
    indexmap::{IndexMap as ExtIndexMap, IndexSet as ExtIndexSet},
};

map_container! {
    /// Like [`HashMap`](crate::containers::HashMap), for [`IndexMap`](indexmap::IndexMap).
    IndexMap => ExtIndexMap<K: Hash | Eq, V, S: BuildHasher | Default = RandomState>,
    ExtIndexMap::with_capacity_and_hasher,
    cap_unique_keys
}

set_container! {
    /// Like [`HashSet`](crate::containers::HashSet), for [`IndexSet`](indexmap::IndexSet).
    IndexSet => ExtIndexSet<K: Hash | Eq, S: BuildHasher | Default = RandomState>,
    ExtIndexSet::with_capacity_and_hasher,
    cap_unique_keys
}

#[cfg(test)]
mod tests {
    use {
        crate::{
            Deserialize, ReadError, Serialize, containers, containers::CheckUniqueKeys,
            deserialize, len::BincodeLen, proptest_config::proptest_cfg, serialize,
        },
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

    #[test]
    fn test_index_containers_check_uniqueness_and_preserve_order() {
        let dup_map = serialize(&vec![(1u32, 10u64), (1, 20)]).unwrap();
        assert!(matches!(
            <containers::IndexMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&dup_map),
            Err(ReadError::Custom(_)),
        ));

        let dup_set = serialize(&vec![7u32, 7]).unwrap();
        assert!(matches!(
            <containers::IndexSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(&dup_set),
            Err(ReadError::Custom(_)),
        ));

        let map: TestIndexMap<u32, u64> = IndexMap::from_iter([(3u32, 30u64), (1, 10), (2, 20)]);
        let bytes = <containers::IndexMap<u32, u64, BincodeLen>>::serialize(&map).unwrap();
        let decoded =
            <containers::IndexMap<u32, u64, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes)
                .unwrap();
        assert_eq!(decoded.keys().copied().collect::<Vec<_>>(), vec![3, 1, 2]);

        let set: TestIndexSet<u32> = IndexSet::from_iter([3u32, 1, 2]);
        let bytes = <containers::IndexSet<u32, BincodeLen>>::serialize(&set).unwrap();
        let decoded =
            <containers::IndexSet<u32, BincodeLen, CheckUniqueKeys>>::deserialize(&bytes).unwrap();
        assert_eq!(decoded.iter().copied().collect::<Vec<_>>(), vec![3, 1, 2]);
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
