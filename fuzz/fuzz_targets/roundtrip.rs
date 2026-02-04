#![no_main]

use {
    libfuzzer_sys::fuzz_target,
    std::{
        collections::{BTreeMap, BTreeSet, HashMap, HashSet, LinkedList, VecDeque},
        net::{IpAddr, Ipv4Addr, Ipv6Addr},
        time::{Duration, SystemTime},
    },
    uuid::Uuid,
    wincode::config::{Configuration, DEFAULT_PREALLOCATION_SIZE_LIMIT},
    wincode_derive::{SchemaRead, SchemaWrite},
};

trait NanAwareEq {
    fn nan_aware_eq(&self, other: &Self) -> bool;
}

impl NanAwareEq for f32 {
    fn nan_aware_eq(&self, other: &Self) -> bool {
        if self.is_nan() && other.is_nan() {
            true
        } else {
            self == other
        }
    }
}

impl NanAwareEq for f64 {
    fn nan_aware_eq(&self, other: &Self) -> bool {
        if self.is_nan() && other.is_nan() {
            true
        } else {
            self == other
        }
    }
}
include!("../types.rs");

impl NanAwareEq for FloatTypes {
    fn nan_aware_eq(&self, other: &Self) -> bool {
        self.f32_val.nan_aware_eq(&other.f32_val)
            && self.f64_val.nan_aware_eq(&other.f64_val)
            && self.vec_f32.len() == other.vec_f32.len()
            && self
                .vec_f32
                .iter()
                .zip(&other.vec_f32)
                .all(|(a, b)| a.nan_aware_eq(b))
            && self.vec_f64.len() == other.vec_f64.len()
            && self
                .vec_f64
                .iter()
                .zip(&other.vec_f64)
                .all(|(a, b)| a.nan_aware_eq(b))
    }
}

fn is_preallocation_error<T>(result: &Result<T, wincode::error::ReadError>) -> bool {
    matches!(
        result,
        Err(wincode::error::ReadError::PreallocationSizeLimit { .. })
    )
}

macro_rules! assert_config_roundtrip {
    (@cmp eq, $a:expr, $b:expr, $label:expr) => {
        assert_eq!($a, $b, "Deserialization mismatch for {}", $label);
    };
    (@cmp nan, $a:expr, $b:expr, $label:expr) => {
        assert!($a.nan_aware_eq(&$b), "Deserialization mismatch for {}", $label);
    };
    ($cmp:ident, $label:expr, $wincode_result:expr, $bincode_result:expr, $reser_w:expr, $reser_b:expr) => {
        match ($wincode_result, $bincode_result) {
            (Ok(wv), Ok(bv)) => {
                assert_config_roundtrip!(@cmp $cmp, wv, bv, $label);
                let ws = ($reser_w)(&wv);
                let bs = ($reser_b)(&bv);
                assert!(
                    ws.len() <= DEFAULT_PREALLOCATION_SIZE_LIMIT,
                    "Serialized size {} exceeds DEFAULT_PREALLOCATION_SIZE_LIMIT ({}) for {}",
                    ws.len(),
                    DEFAULT_PREALLOCATION_SIZE_LIMIT,
                    $label
                );
                assert_eq!(ws, bs, "Re-serialization mismatch for {}", $label);
            }
            (Err(_), Err(_)) => {}
            (Ok(_), Err(e)) => {
                panic!("wincode accepted but bincode rejected for {}: {e:?}", $label);
            }
            (Err(e), Ok(_)) => {
                panic!("bincode accepted but wincode rejected for {}: {e}", $label);
            }
        }
    };
    (unordered, $label:expr, $wincode_result:expr, $bincode_result:expr, $reser_w:expr) => {
        match ($wincode_result, $bincode_result) {
            (Ok(wv), Ok(bv)) => {
                assert_eq!(wv, bv, "Deserialization mismatch for {}", $label);
                let ws = ($reser_w)(&wv);
                // Unordered collections may serialize to different byte sequences
                assert!(
                    ws.len() <= DEFAULT_PREALLOCATION_SIZE_LIMIT,
                    "Serialized size {} exceeds DEFAULT_PREALLOCATION_SIZE_LIMIT ({}) for {}",
                    ws.len(),
                    DEFAULT_PREALLOCATION_SIZE_LIMIT,
                    $label
                );
            }
            (Err(_), Err(_)) => {}
            (Ok(_), Err(e)) => {
                panic!("wincode accepted but bincode rejected for {}: {e:?}", $label);
            }
            (Err(e), Ok(_)) => {
                panic!("bincode accepted but wincode rejected for {}: {e}", $label);
            }
        }
    };
}

macro_rules! test_config {
    ($bytes:expr, $type:ty, unordered, $wc:expr, v1($opts:expr)) => {{
        use bincode_1::Options;
        let config = $wc;
        let opts = $opts;
        let wr: Result<$type, _> = wincode::config::deserialize($bytes, config);
        if is_preallocation_error(&wr) {
            let limited = opts.with_limit(DEFAULT_PREALLOCATION_SIZE_LIMIT as u64);
            let br: Result<$type, _> = limited.deserialize_from($bytes);
            assert!(br.is_err(),
                "bincode v1 accepted but wincode rejected due to preallocation limit for {}",
                stringify!($type));
        } else {
            let br: Result<$type, _> = opts.deserialize($bytes);
            assert_config_roundtrip!(unordered, stringify!($type), wr, br,
                |v: &$type| wincode::config::serialize(v, config).unwrap()
            );
        }
    }};
    ($bytes:expr, $type:ty, unordered, $wc:expr, v2($bc2:expr)) => {{
        let config = $wc;
        let bc2 = $bc2;
        let wr: Result<$type, _> = wincode::config::deserialize($bytes, config);
        if is_preallocation_error(&wr) {
            let limited = bc2.with_limit::<{ DEFAULT_PREALLOCATION_SIZE_LIMIT }>();
            let br: Result<$type, _> =
                bincode_2::serde::borrow_decode_from_slice($bytes, limited).map(|(v, _)| v);
            assert!(br.is_err(),
                "bincode v2 accepted but wincode rejected due to preallocation limit for {}",
                stringify!($type));
        } else {
            let br: Result<$type, _> =
                bincode_2::serde::borrow_decode_from_slice($bytes, bc2).map(|(v, _)| v);
            assert_config_roundtrip!(unordered, stringify!($type), wr, br,
                |v: &$type| wincode::config::serialize(v, config).unwrap()
            );
        }
    }};
    ($bytes:expr, $type:ty, $cmp:ident, $wc:expr, v1($opts:expr)) => {{
        use bincode_1::Options;
        let config = $wc;
        let opts = $opts;
        let wr: Result<$type, _> = wincode::config::deserialize($bytes, config);
        if is_preallocation_error(&wr) {
            let limited = opts.with_limit(DEFAULT_PREALLOCATION_SIZE_LIMIT as u64);
            // Important: use deserialize_from to enforce limits (https://github.com/bincode-org/bincode/issues/299)
            let br: Result<$type, _> = limited.deserialize_from($bytes);
            assert!(br.is_err(),
                "bincode v1 accepted but wincode rejected due to preallocation limit for {}",
                stringify!($type));
        } else {
            let br: Result<$type, _> = opts.deserialize($bytes);
            assert_config_roundtrip!($cmp, stringify!($type), wr, br,
                |v: &$type| wincode::config::serialize(v, config).unwrap(),
                |v: &$type| opts.serialize(v).unwrap()
            );
        }
    }};
    ($bytes:expr, $type:ty, $cmp:ident, $wc:expr, v2($bc2:expr)) => {{
        let config = $wc;
        let bc2 = $bc2;
        let wr: Result<$type, _> = wincode::config::deserialize($bytes, config);
        if is_preallocation_error(&wr) {
            let limited = bc2.with_limit::<{ DEFAULT_PREALLOCATION_SIZE_LIMIT }>();
            let br: Result<$type, _> =
                bincode_2::serde::borrow_decode_from_slice($bytes, limited).map(|(v, _)| v);
            assert!(br.is_err(),
                "bincode v2 accepted but wincode rejected due to preallocation limit for {}",
                stringify!($type));
        } else {
            let br: Result<$type, _> =
                bincode_2::serde::borrow_decode_from_slice($bytes, bc2).map(|(v, _)| v);
            assert_config_roundtrip!($cmp, stringify!($type), wr, br,
                |v: &$type| wincode::config::serialize(v, config).unwrap(),
                |v: &$type| bincode_2::serde::encode_to_vec(v, bc2).unwrap()
            );
        }
    }};
}

macro_rules! test_all_configs {
    ($data:expr, $type:ty) => {
        test_config!(
            $data,
            $type,
            eq,
            Configuration::default()
                .with_little_endian()
                .with_fixint_encoding(),
            v1(bincode_1::DefaultOptions::new()
                .with_little_endian()
                .with_fixint_encoding()
                .allow_trailing_bytes())
        );
        test_config!(
            $data,
            $type,
            eq,
            Configuration::default()
                .with_big_endian()
                .with_fixint_encoding(),
            v1(bincode_1::DefaultOptions::new()
                .with_big_endian()
                .with_fixint_encoding()
                .allow_trailing_bytes())
        );
        test_config!(
            $data,
            $type,
            eq,
            Configuration::default()
                .with_little_endian()
                .with_varint_encoding(),
            v2(bincode_2::config::standard()
                .with_little_endian()
                .with_variable_int_encoding())
        );
        test_config!(
            $data,
            $type,
            eq,
            Configuration::default()
                .with_big_endian()
                .with_varint_encoding(),
            v2(bincode_2::config::standard()
                .with_big_endian()
                .with_variable_int_encoding())
        );
    };
}

macro_rules! test_all_configs_float {
    ($data:expr, $type:ty) => {
        test_config!(
            $data,
            $type,
            nan,
            Configuration::default()
                .with_little_endian()
                .with_fixint_encoding(),
            v1(bincode_1::DefaultOptions::new()
                .with_little_endian()
                .with_fixint_encoding()
                .allow_trailing_bytes())
        );
        test_config!(
            $data,
            $type,
            nan,
            Configuration::default()
                .with_big_endian()
                .with_fixint_encoding(),
            v1(bincode_1::DefaultOptions::new()
                .with_big_endian()
                .with_fixint_encoding()
                .allow_trailing_bytes())
        );
        test_config!(
            $data,
            $type,
            nan,
            Configuration::default()
                .with_little_endian()
                .with_varint_encoding(),
            v2(bincode_2::config::standard()
                .with_little_endian()
                .with_variable_int_encoding())
        );
        test_config!(
            $data,
            $type,
            nan,
            Configuration::default()
                .with_big_endian()
                .with_varint_encoding(),
            v2(bincode_2::config::standard()
                .with_big_endian()
                .with_variable_int_encoding())
        );
    };
}

macro_rules! test_all_configs_unordered {
    ($data:expr, $type:ty) => {
        test_config!(
            $data,
            $type,
            unordered,
            Configuration::default()
                .with_little_endian()
                .with_fixint_encoding(),
            v1(bincode_1::DefaultOptions::new()
                .with_little_endian()
                .with_fixint_encoding()
                .allow_trailing_bytes())
        );
        test_config!(
            $data,
            $type,
            unordered,
            Configuration::default()
                .with_big_endian()
                .with_fixint_encoding(),
            v1(bincode_1::DefaultOptions::new()
                .with_big_endian()
                .with_fixint_encoding()
                .allow_trailing_bytes())
        );
        test_config!(
            $data,
            $type,
            unordered,
            Configuration::default()
                .with_little_endian()
                .with_varint_encoding(),
            v2(bincode_2::config::standard()
                .with_little_endian()
                .with_variable_int_encoding())
        );
        test_config!(
            $data,
            $type,
            unordered,
            Configuration::default()
                .with_big_endian()
                .with_varint_encoding(),
            v2(bincode_2::config::standard()
                .with_big_endian()
                .with_variable_int_encoding())
        );
    };
}

// Varint encoding differs between bincode 1.x and bincode 2.x, and wincode targets compatibility with bincode 2.x.
// Wincode does not support `reject_trailing_bytes` configurations, so we allow trailing bytes in every configuration.
fuzz_target!(|data: &[u8]| {
    test_all_configs!(data, bool);
    test_all_configs!(data, u8);
    test_all_configs!(data, u16);
    test_all_configs!(data, u32);
    test_all_configs!(data, u64);
    test_all_configs!(data, u128);
    test_all_configs!(data, i8);
    test_all_configs!(data, i16);
    test_all_configs!(data, i32);
    test_all_configs!(data, i64);
    test_all_configs!(data, i128);
    test_all_configs_float!(data, f32);
    test_all_configs_float!(data, f64);

    test_all_configs!(data, Vec<u8>);
    test_all_configs!(data, String);
    test_all_configs!(data, Vec<u32>);
    test_all_configs!(data, Vec<String>);
    test_all_configs!(data, Option<u64>);
    test_all_configs!(data, Option<String>);
    test_all_configs!(data, [u8; 4]);
    test_all_configs!(data, [u32; 8]);
    test_all_configs!(data, (u64, bool));
    test_all_configs!(data, (u32, String, bool));
    test_all_configs!(data, Ipv4Addr);
    test_all_configs!(data, Ipv6Addr);
    test_all_configs!(data, IpAddr);
    test_all_configs!(data, Duration);
    test_all_configs!(data, SystemTime);
    test_all_configs!(data, Uuid);
    test_all_configs!(data, char);
    test_all_configs!(data, Box<u32>);
    test_all_configs!(data, Box<[u8]>);
    test_all_configs!(data, VecDeque<u32>);
    test_all_configs!(data, LinkedList<u32>);
    test_all_configs!(data, BTreeSet<u32>);
    test_all_configs!(data, BTreeMap<u32, u32>);
    test_all_configs!(data, Result<u32, String>);
    test_all_configs_unordered!(data, HashMap<u32, u32>);
    test_all_configs_unordered!(data, HashSet<u32>);

    test_all_configs!(data, BasicTypes);
    test_all_configs!(data, VecTypes);
    test_all_configs!(data, StringTypes);
    test_all_configs!(data, OptionTypes);
    test_all_configs!(data, ArrayTypes);
    test_all_configs_float!(data, FloatTypes);
    test_all_configs!(data, TupleStruct);
    test_all_configs!(data, SimpleEnum);
    test_all_configs!(data, NestedStruct);
    test_all_configs!(data, ComplexStruct);

    test_all_configs!(data, ZeroCopySimple);
    test_all_configs!(data, ZeroCopyOrdered);
    test_all_configs!(data, ZeroCopyPrimitives);
    test_all_configs!(data, ZeroCopyArrays);
    test_all_configs!(data, ZeroCopyNested);
    test_all_configs!(data, ZeroCopySignature);
});
