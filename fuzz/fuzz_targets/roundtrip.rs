#![no_main]

use {
    libfuzzer_sys::fuzz_target,
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
#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct BasicTypes {
    b: bool,
    u8_val: u8,
    u16_val: u16,
    u32_val: u32,
    u64_val: u64,
    u128_val: u128,
    i8_val: i8,
    i16_val: i16,
    i32_val: i32,
    i64_val: i64,
    i128_val: i128,
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct VecTypes {
    vec_u8: Vec<u8>,
    vec_u32: Vec<u32>,
    vec_u64: Vec<u64>,
    vec_bool: Vec<bool>,
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct StringTypes {
    s: String,
    vec_strings: Vec<String>,
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct OptionTypes {
    opt_u64: Option<u64>,
    opt_string: Option<String>,
    opt_vec: Option<Vec<u32>>,
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct NestedStruct {
    inner: BasicTypes,
    data: Vec<u64>,
    flag: bool,
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct TupleStruct(u64, String, bool);

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
enum SimpleEnum {
    Variant1,
    Variant2(u64),
    Variant3 { x: u32, y: bool },
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct ArrayTypes {
    arr_u8: [u8; 4],
    arr_u32: [u32; 3],
    arr_bool: [bool; 2],
}

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct FloatTypes {
    f32_val: f32,
    f64_val: f64,
    vec_f32: Vec<f32>,
    vec_f64: Vec<f64>,
}

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

#[derive(
    Debug, Clone, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
struct ComplexStruct {
    basic: BasicTypes,
    vecs: VecTypes,
    strings: StringTypes,
    options: OptionTypes,
    nested: NestedStruct,
    tuple: TupleStruct,
    enums: SimpleEnum,
    arrays: ArrayTypes,
}

#[repr(C)]
#[derive(
    Debug, Clone, Copy, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
#[wincode(assert_zero_copy)]
struct ZeroCopySimple {
    a: u32,
    b: u16,
    c: u8,
    d: u8,
}

#[repr(transparent)]
#[derive(
    Debug, Clone, Copy, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
#[wincode(assert_zero_copy)]
struct ZeroCopySignature([u8; 32]);

#[repr(C)]
#[derive(
    Debug, Clone, Copy, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
#[wincode(assert_zero_copy)]
struct ZeroCopyArrays {
    id: u64,
    hash: [u8; 32],
    flags: [u8; 4],
    _pad: [u8; 4],
}

#[repr(C)]
#[derive(
    Debug, Clone, Copy, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
#[wincode(assert_zero_copy)]
struct ZeroCopyOrdered {
    u64_val: u64,
    u32_val: u32,
    u16_val: u16,
    u8_val1: u8,
    u8_val2: u8,
}

#[repr(C)]
#[derive(
    Debug, Clone, Copy, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
#[wincode(assert_zero_copy)]
struct ZeroCopyNested {
    inner: ZeroCopySimple,
    timestamp: u64,
}

#[repr(C)]
#[derive(
    Debug, Clone, Copy, PartialEq, SchemaWrite, SchemaRead, serde::Serialize, serde::Deserialize,
)]
#[wincode(assert_zero_copy)]
struct ZeroCopyPrimitives {
    i64_val: i64,
    i32_val: i32,
    i16_val: i16,
    i8_val: i8,
    _pad: u8,
}

macro_rules! test_roundtrip {
    ($bytes:expr, $type:ty) => {{
        let wincode_result: Result<$type, _> = wincode::deserialize($bytes);
        let bincode_result: Result<$type, _> = bincode::deserialize($bytes);

        match (wincode_result, bincode_result) {
            (Ok(wincode_val), Ok(bincode_val)) => {
                assert_eq!(
                    wincode_val,
                    bincode_val,
                    "Deserialization produced different values for {}",
                    stringify!($type)
                );

                let wincode_reserialized =
                    wincode::serialize(&wincode_val).expect("Re-serialization should succeed");
                let bincode_reserialized =
                    bincode::serialize(&bincode_val).expect("Re-serialization should succeed");

                assert_eq!(
                    wincode_reserialized,
                    bincode_reserialized,
                    "Re-serialization mismatch for {}",
                    stringify!($type)
                );
            }
            (Err(_), Err(_)) => {}
            (Ok(_), Err(_)) => {
                panic!(
                    "wincode accepted but bincode rejected for {}",
                    stringify!($type)
                );
            }
            (Err(_), Ok(_)) => {
                panic!(
                    "bincode accepted but wincode rejected for {}",
                    stringify!($type)
                );
            }
        }
    }};
}

macro_rules! test_roundtrip_float {
    ($bytes:expr, $type:ty) => {{
        let wincode_result: Result<$type, _> = wincode::deserialize($bytes);
        let bincode_result: Result<$type, _> = bincode::deserialize($bytes);

        match (wincode_result, bincode_result) {
            (Ok(wincode_val), Ok(bincode_val)) => {
                assert!(
                    wincode_val.nan_aware_eq(&bincode_val),
                    "Deserialization produced different values for {}",
                    stringify!($type)
                );

                let wincode_reserialized =
                    wincode::serialize(&wincode_val).expect("Re-serialization should succeed");
                let bincode_reserialized =
                    bincode::serialize(&bincode_val).expect("Re-serialization should succeed");

                assert_eq!(
                    wincode_reserialized,
                    bincode_reserialized,
                    "Re-serialization mismatch for {}",
                    stringify!($type)
                );
            }
            (Err(_), Err(_)) => {}
            (Ok(_), Err(_)) => {
                panic!(
                    "wincode accepted but bincode rejected for {}",
                    stringify!($type)
                );
            }
            (Err(_), Ok(_)) => {
                panic!(
                    "bincode accepted but wincode rejected for {}",
                    stringify!($type)
                );
            }
        }
    }};
}

fuzz_target!(|data: &[u8]| {
    test_roundtrip!(data, bool);
    test_roundtrip!(data, u8);
    test_roundtrip!(data, u16);
    test_roundtrip!(data, u32);
    test_roundtrip!(data, u64);
    test_roundtrip!(data, u128);
    test_roundtrip!(data, i8);
    test_roundtrip!(data, i16);
    test_roundtrip!(data, i32);
    test_roundtrip!(data, i64);
    test_roundtrip!(data, i128);
    test_roundtrip_float!(data, f32);
    test_roundtrip_float!(data, f64);

    test_roundtrip!(data, String);
    test_roundtrip!(data, Vec<u8>);
    test_roundtrip!(data, Vec<u32>);
    test_roundtrip!(data, Vec<String>);
    test_roundtrip!(data, Option<u64>);
    test_roundtrip!(data, Option<String>);
    test_roundtrip!(data, [u8; 4]);
    test_roundtrip!(data, [u32; 8]);
    test_roundtrip!(data, (u64, bool));
    test_roundtrip!(data, (u32, String, bool));

    test_roundtrip!(data, BasicTypes);
    test_roundtrip!(data, VecTypes);
    test_roundtrip!(data, StringTypes);
    test_roundtrip!(data, OptionTypes);
    test_roundtrip!(data, ArrayTypes);
    test_roundtrip_float!(data, FloatTypes);
    test_roundtrip!(data, TupleStruct);
    test_roundtrip!(data, SimpleEnum);
    test_roundtrip!(data, NestedStruct);
    test_roundtrip!(data, ComplexStruct);

    test_roundtrip!(data, ZeroCopySimple);
    test_roundtrip!(data, ZeroCopyOrdered);
    test_roundtrip!(data, ZeroCopyPrimitives);
    test_roundtrip!(data, ZeroCopyArrays);
    test_roundtrip!(data, ZeroCopyNested);
    test_roundtrip!(data, ZeroCopySignature);
});
