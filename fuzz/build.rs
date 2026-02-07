use {
    std::{
        collections::{BTreeMap, BTreeSet, HashMap, HashSet, LinkedList, VecDeque},
        fs,
        net::{IpAddr, Ipv4Addr, Ipv6Addr},
        path::Path,
        time::{Duration, UNIX_EPOCH},
    },
    uuid::Uuid,
    wincode::config::{Configuration, DEFAULT_PREALLOCATION_SIZE_LIMIT},
    wincode_derive::{SchemaRead, SchemaWrite},
};

include!("types.rs");

fn write_seed(corpus_dir: &Path, name: &str, data: &[u8]) {
    let path = corpus_dir.join(name);
    fs::write(&path, data).unwrap_or_else(|e| panic!("failed to write seed {name}: {e}"));
}

macro_rules! seed {
    ($corpus_dir:expr, $name:expr, $value:expr) => {
        let bytes = wincode::serialize(&$value)
            .expect(concat!("failed to serialize seed: ", stringify!($name)));
        write_seed($corpus_dir, $name, &bytes);
    };
}

fn main() {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let corpus_dir = Path::new(&manifest_dir).join("corpus").join("roundtrip");
    fs::create_dir_all(&corpus_dir).expect("failed to create corpus directory");

    {
        let prealloc_limit_vec: Vec<u8> = vec![0u8; DEFAULT_PREALLOCATION_SIZE_LIMIT + 1];
        let config = Configuration::default().disable_preallocation_size_limit();
        let bytes = wincode::config::serialize(&prealloc_limit_vec, config)
            .expect("failed to serialize seed: seed-vec_u8-prealloc_limit");
        write_seed(&corpus_dir, "seed-vec_u8-prealloc_limit", &bytes);
    }

    seed!(&corpus_dir, "seed-bool-false", false);
    seed!(&corpus_dir, "seed-bool-true", true);

    seed!(&corpus_dir, "seed-u8-zero", 0u8);
    seed!(&corpus_dir, "seed-u8-max", u8::MAX);

    seed!(&corpus_dir, "seed-u16-zero", 0u16);
    seed!(&corpus_dir, "seed-u16-max", u16::MAX);

    seed!(&corpus_dir, "seed-u32-zero", 0u32);
    seed!(&corpus_dir, "seed-u32-max", u32::MAX);

    seed!(&corpus_dir, "seed-u64-zero", 0u64);
    seed!(&corpus_dir, "seed-u64-max", u64::MAX);

    seed!(&corpus_dir, "seed-u128-zero", 0u128);
    seed!(&corpus_dir, "seed-u128-max", u128::MAX);

    seed!(&corpus_dir, "seed-i8-zero", 0i8);
    seed!(&corpus_dir, "seed-i8-min", i8::MIN);
    seed!(&corpus_dir, "seed-i8-max", i8::MAX);

    seed!(&corpus_dir, "seed-i16-zero", 0i16);
    seed!(&corpus_dir, "seed-i16-min", i16::MIN);
    seed!(&corpus_dir, "seed-i16-max", i16::MAX);

    seed!(&corpus_dir, "seed-i32-zero", 0i32);
    seed!(&corpus_dir, "seed-i32-min", i32::MIN);
    seed!(&corpus_dir, "seed-i32-max", i32::MAX);

    seed!(&corpus_dir, "seed-i64-zero", 0i64);
    seed!(&corpus_dir, "seed-i64-min", i64::MIN);
    seed!(&corpus_dir, "seed-i64-max", i64::MAX);

    seed!(&corpus_dir, "seed-i128-zero", 0i128);
    seed!(&corpus_dir, "seed-i128-min", i128::MIN);
    seed!(&corpus_dir, "seed-i128-max", i128::MAX);

    seed!(&corpus_dir, "seed-f32-zero", 0.0f32);
    seed!(&corpus_dir, "seed-f32-one", 1.0f32);
    seed!(&corpus_dir, "seed-f32-neg-one", -1.0f32);
    seed!(&corpus_dir, "seed-f32-nan", f32::NAN);
    seed!(&corpus_dir, "seed-f32-inf", f32::INFINITY);
    seed!(&corpus_dir, "seed-f32-neg-inf", f32::NEG_INFINITY);
    seed!(&corpus_dir, "seed-f32-min", f32::MIN);
    seed!(&corpus_dir, "seed-f32-max", f32::MAX);

    seed!(&corpus_dir, "seed-f64-zero", 0.0f64);
    seed!(&corpus_dir, "seed-f64-one", 1.0f64);
    seed!(&corpus_dir, "seed-f64-neg-one", -1.0f64);
    seed!(&corpus_dir, "seed-f64-nan", f64::NAN);
    seed!(&corpus_dir, "seed-f64-inf", f64::INFINITY);
    seed!(&corpus_dir, "seed-f64-neg-inf", f64::NEG_INFINITY);
    seed!(&corpus_dir, "seed-f64-min", f64::MIN);
    seed!(&corpus_dir, "seed-f64-max", f64::MAX);

    seed!(&corpus_dir, "seed-string-empty", String::new());
    seed!(&corpus_dir, "seed-string-hello", String::from("hello"));
    seed!(
        &corpus_dir,
        "seed-string-utf8",
        String::from("\u{1F600}\u{00E9}\u{4E16}\u{754C}")
    );

    seed!(&corpus_dir, "seed-ipv4-localhost", Ipv4Addr::LOCALHOST);
    seed!(&corpus_dir, "seed-ipv4-broadcast", Ipv4Addr::BROADCAST);
    seed!(&corpus_dir, "seed-ipv6-localhost", Ipv6Addr::LOCALHOST);
    seed!(&corpus_dir, "seed-ipv6-unspecified", Ipv6Addr::UNSPECIFIED);
    seed!(
        &corpus_dir,
        "seed-ipaddr-v4",
        IpAddr::V4(Ipv4Addr::LOCALHOST)
    );
    seed!(
        &corpus_dir,
        "seed-ipaddr-v6",
        IpAddr::V6(Ipv6Addr::LOCALHOST)
    );
    seed!(&corpus_dir, "seed-duration-zero", Duration::ZERO);
    seed!(&corpus_dir, "seed-duration-max", Duration::MAX);
    seed!(&corpus_dir, "seed-duration-1s", Duration::from_secs(1));
    seed!(&corpus_dir, "seed-systemtime-epoch", UNIX_EPOCH);
    seed!(
        &corpus_dir,
        "seed-systemtime-now",
        UNIX_EPOCH + Duration::from_secs(1_700_000_000)
    );

    seed!(&corpus_dir, "seed-uuid-nil", Uuid::nil());
    seed!(&corpus_dir, "seed-uuid-max", Uuid::max());
    seed!(
        &corpus_dir,
        "seed-uuid-v4",
        Uuid::from_bytes([
            0x55, 0x0e, 0x84, 0x00, 0xe2, 0x9b, 0x41, 0xd4, 0xa7, 0x16, 0x44, 0x66, 0x55, 0x44,
            0x00, 0x00,
        ])
    );

    seed!(&corpus_dir, "seed-char-ascii", 'A');
    seed!(&corpus_dir, "seed-char-emoji", '\u{1F600}');
    seed!(&corpus_dir, "seed-char-null", '\0');

    seed!(&corpus_dir, "seed-box_u32", Box::new(42u32));
    seed!(
        &corpus_dir,
        "seed-box_slice_u8",
        vec![1u8, 2, 3].into_boxed_slice()
    );

    seed!(
        &corpus_dir,
        "seed-vecdeque_u32-empty",
        VecDeque::<u32>::new()
    );
    seed!(
        &corpus_dir,
        "seed-vecdeque_u32-small",
        VecDeque::from([1u32, 2, 3])
    );

    seed!(
        &corpus_dir,
        "seed-linkedlist_u32-empty",
        LinkedList::<u32>::new()
    );
    seed!(
        &corpus_dir,
        "seed-linkedlist_u32-small",
        LinkedList::from([1u32, 2, 3])
    );

    seed!(
        &corpus_dir,
        "seed-btreeset_u32-empty",
        BTreeSet::<u32>::new()
    );
    seed!(
        &corpus_dir,
        "seed-btreeset_u32-small",
        BTreeSet::from([1u32, 2, 3])
    );

    seed!(
        &corpus_dir,
        "seed-btreemap_u32-empty",
        BTreeMap::<u32, u32>::new()
    );
    seed!(
        &corpus_dir,
        "seed-btreemap_u32-small",
        BTreeMap::from([(1u32, 10u32), (2, 20)])
    );

    seed!(&corpus_dir, "seed-result_ok", Ok::<u32, String>(42));
    seed!(
        &corpus_dir,
        "seed-result_err",
        Err::<u32, String>(String::from("error"))
    );

    seed!(
        &corpus_dir,
        "seed-hashmap_u32-empty",
        HashMap::<u32, u32>::new()
    );
    seed!(
        &corpus_dir,
        "seed-hashmap_u32-small",
        HashMap::from([(1u32, 10u32), (2, 20)])
    );

    seed!(&corpus_dir, "seed-hashset_u32-empty", HashSet::<u32>::new());
    seed!(
        &corpus_dir,
        "seed-hashset_u32-small",
        HashSet::from([1u32, 2, 3])
    );

    seed!(&corpus_dir, "seed-vec_u8-empty", Vec::<u8>::new());
    seed!(&corpus_dir, "seed-vec_u8-small", vec![1u8, 2, 3, 4]);

    seed!(&corpus_dir, "seed-vec_u32-empty", Vec::<u32>::new());
    seed!(&corpus_dir, "seed-vec_u32-small", vec![1u32, 2, 3]);

    seed!(&corpus_dir, "seed-vec_string-empty", Vec::<String>::new());
    seed!(
        &corpus_dir,
        "seed-vec_string-multi",
        vec![String::from("a"), String::from("bc"), String::from("def")]
    );

    seed!(&corpus_dir, "seed-option_u64-none", Option::<u64>::None);
    seed!(&corpus_dir, "seed-option_u64-some", Some(42u64));

    seed!(
        &corpus_dir,
        "seed-option_string-none",
        Option::<String>::None
    );
    seed!(
        &corpus_dir,
        "seed-option_string-some",
        Some(String::from("hello"))
    );

    seed!(&corpus_dir, "seed-arr_u8_4-zeros", [0u8; 4]);
    seed!(&corpus_dir, "seed-arr_u8_4-values", [1u8, 2, 3, 4]);

    seed!(&corpus_dir, "seed-arr_u32_8-zeros", [0u32; 8]);
    seed!(
        &corpus_dir,
        "seed-arr_u32_8-values",
        [1u32, 2, 3, 4, 5, 6, 7, 8]
    );

    seed!(&corpus_dir, "seed-tuple_u64_bool", (42u64, true));

    seed!(
        &corpus_dir,
        "seed-tuple_u32_string_bool",
        (99u32, String::from("test"), false)
    );

    seed!(
        &corpus_dir,
        "seed-basic_types-zeros",
        BasicTypes {
            b: false,
            u8_val: 0,
            u16_val: 0,
            u32_val: 0,
            u64_val: 0,
            u128_val: 0,
            i8_val: 0,
            i16_val: 0,
            i32_val: 0,
            i64_val: 0,
            i128_val: 0,
        }
    );
    seed!(
        &corpus_dir,
        "seed-basic_types-maxmin",
        BasicTypes {
            b: true,
            u8_val: u8::MAX,
            u16_val: u16::MAX,
            u32_val: u32::MAX,
            u64_val: u64::MAX,
            u128_val: u128::MAX,
            i8_val: i8::MIN,
            i16_val: i16::MIN,
            i32_val: i32::MIN,
            i64_val: i64::MIN,
            i128_val: i128::MIN,
        }
    );

    seed!(
        &corpus_dir,
        "seed-vec_types-empty",
        VecTypes {
            vec_u8: vec![],
            vec_u32: vec![],
            vec_u64: vec![],
            vec_bool: vec![],
        }
    );
    seed!(
        &corpus_dir,
        "seed-vec_types-populated",
        VecTypes {
            vec_u8: vec![1, 2, 3],
            vec_u32: vec![100, 200],
            vec_u64: vec![u64::MAX],
            vec_bool: vec![true, false, true],
        }
    );

    seed!(
        &corpus_dir,
        "seed-string_types-empty",
        StringTypes {
            s: String::new(),
            vec_strings: vec![],
        }
    );
    seed!(
        &corpus_dir,
        "seed-string_types-utf8",
        StringTypes {
            s: String::from("\u{1F600}\u{00E9}"),
            vec_strings: vec![String::from("hello"), String::from("\u{4E16}\u{754C}")],
        }
    );

    seed!(
        &corpus_dir,
        "seed-option_types-none",
        OptionTypes {
            opt_u64: None,
            opt_string: None,
            opt_vec: None,
        }
    );
    seed!(
        &corpus_dir,
        "seed-option_types-some",
        OptionTypes {
            opt_u64: Some(42),
            opt_string: Some(String::from("hello")),
            opt_vec: Some(vec![1, 2, 3]),
        }
    );

    seed!(
        &corpus_dir,
        "seed-array_types",
        ArrayTypes {
            arr_u8: [1, 2, 3, 4],
            arr_u32: [100, 200, 300],
            arr_bool: [true, false],
        }
    );

    seed!(
        &corpus_dir,
        "seed-float_types-normal",
        FloatTypes {
            f32_val: 1.5,
            f64_val: -2.5,
            vec_f32: vec![0.0, 1.0],
            vec_f64: vec![f64::MAX],
        }
    );
    seed!(
        &corpus_dir,
        "seed-float_types-special",
        FloatTypes {
            f32_val: f32::NAN,
            f64_val: f64::INFINITY,
            vec_f32: vec![f32::NEG_INFINITY, f32::NAN],
            vec_f64: vec![f64::NEG_INFINITY, f64::NAN],
        }
    );

    seed!(
        &corpus_dir,
        "seed-tuple_struct",
        TupleStruct(42, String::from("hello"), true)
    );

    seed!(
        &corpus_dir,
        "seed-simple_enum-variant1",
        SimpleEnum::Variant1
    );
    seed!(
        &corpus_dir,
        "seed-simple_enum-variant2",
        SimpleEnum::Variant2(99)
    );
    seed!(
        &corpus_dir,
        "seed-simple_enum-variant3",
        SimpleEnum::Variant3 { x: 42, y: true }
    );

    let basic_zeros = BasicTypes {
        b: false,
        u8_val: 0,
        u16_val: 0,
        u32_val: 0,
        u64_val: 0,
        u128_val: 0,
        i8_val: 0,
        i16_val: 0,
        i32_val: 0,
        i64_val: 0,
        i128_val: 0,
    };
    seed!(
        &corpus_dir,
        "seed-nested_struct",
        NestedStruct {
            inner: BasicTypes {
                b: true,
                u8_val: 1,
                u16_val: 2,
                u32_val: 3,
                u64_val: 4,
                u128_val: 5,
                i8_val: -1,
                i16_val: -2,
                i32_val: -3,
                i64_val: -4,
                i128_val: -5,
            },
            data: vec![10, 20, 30],
            flag: true,
        }
    );

    seed!(
        &corpus_dir,
        "seed-complex_struct",
        ComplexStruct {
            basic: basic_zeros,
            vecs: VecTypes {
                vec_u8: vec![1],
                vec_u32: vec![2],
                vec_u64: vec![3],
                vec_bool: vec![true],
            },
            strings: StringTypes {
                s: String::from("test"),
                vec_strings: vec![String::from("a")],
            },
            options: OptionTypes {
                opt_u64: Some(1),
                opt_string: None,
                opt_vec: Some(vec![1]),
            },
            nested: NestedStruct {
                inner: BasicTypes {
                    b: true,
                    u8_val: 1,
                    u16_val: 1,
                    u32_val: 1,
                    u64_val: 1,
                    u128_val: 1,
                    i8_val: 1,
                    i16_val: 1,
                    i32_val: 1,
                    i64_val: 1,
                    i128_val: 1,
                },
                data: vec![],
                flag: false,
            },
            tuple: TupleStruct(0, String::new(), false),
            enums: SimpleEnum::Variant1,
            arrays: ArrayTypes {
                arr_u8: [0; 4],
                arr_u32: [0; 3],
                arr_bool: [false; 2],
            },
        }
    );

    seed!(
        &corpus_dir,
        "seed-zero_copy_simple",
        ZeroCopySimple {
            a: 0x12345678,
            b: 0xABCD,
            c: 0xEF,
            d: 0x01,
        }
    );

    seed!(
        &corpus_dir,
        "seed-zero_copy_ordered",
        ZeroCopyOrdered {
            u64_val: u64::MAX,
            u32_val: u32::MAX,
            u16_val: u16::MAX,
            u8_val1: u8::MAX,
            u8_val2: 0,
        }
    );

    seed!(
        &corpus_dir,
        "seed-zero_copy_primitives",
        ZeroCopyPrimitives {
            i64_val: i64::MIN,
            i32_val: i32::MIN,
            i16_val: i16::MIN,
            i8_val: i8::MIN,
            _pad: 0,
        }
    );

    seed!(
        &corpus_dir,
        "seed-zero_copy_arrays",
        ZeroCopyArrays {
            id: 42,
            hash: [0xAB; 32],
            flags: [1, 2, 3, 4],
            _pad: [0; 4],
        }
    );

    seed!(
        &corpus_dir,
        "seed-zero_copy_nested",
        ZeroCopyNested {
            inner: ZeroCopySimple {
                a: 1,
                b: 2,
                c: 3,
                d: 4,
            },
            timestamp: 1_000_000,
        }
    );

    seed!(
        &corpus_dir,
        "seed-zero_copy_signature",
        ZeroCopySignature([0xFF; 32])
    );
}
