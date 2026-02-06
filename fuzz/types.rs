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
