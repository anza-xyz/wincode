use {
    criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput},
    serde::{Deserialize, Serialize},
    std::{collections::HashMap, hint::black_box},
    wincode::{
        config::DefaultConfig, deserialize, serialize, serialize_into, serialized_size, SchemaRead,
        SchemaWrite,
    },
};

#[derive(Serialize, Deserialize, SchemaWrite, SchemaRead, Clone)]
struct SimpleStruct {
    id: u64,
    value: u64,
    flag: bool,
}

#[repr(C)]
#[derive(Clone, Copy, SchemaWrite, SchemaRead, Serialize, Deserialize)]
struct PodStruct {
    a: [u8; 32],
    b: [u8; 16],
    c: [u8; 8],
}

/// verification helper: ensures wincode output matches bincode
fn verify_serialize_into<T>(data: &T) -> Vec<u8>
where
    T: SchemaWrite<DefaultConfig, Src = T> + Serialize + ?Sized,
{
    let serialized = bincode::serialize(data).unwrap();
    assert_eq!(serialize(data).unwrap(), serialized);

    let size = serialized_size(data).unwrap() as usize;
    let mut buffer = vec![0u8; size];
    serialize_into(&mut buffer.as_mut_slice(), data).unwrap();

    assert_eq!(&buffer[..], &serialized[..]);

    serialized
}

/// this allocation happens outside the benchmark loop to measure only
fn create_bench_buffer<T>(data: &T) -> Vec<u8>
where
    T: SchemaWrite<DefaultConfig, Src = T> + ?Sized,
{
    let size = serialized_size(data).unwrap() as usize;
    vec![0u8; size]
}

fn bench_primitives_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Primitives");
    group.throughput(Throughput::Elements(1));

    let data = 0xDEADBEEFCAFEBABEu64;
    let serialized = verify_serialize_into(&data);

    // In-place serialization (measures pure serialization, no allocation)
    group.bench_function("u64/wincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data)).unwrap());
    });

    group.bench_function("u64/bincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| {
            bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data))
                .unwrap()
        });
    });

    group.bench_function("u64/wincode/serialize", |b| {
        b.iter(|| serialize(black_box(&data)).unwrap());
    });

    group.bench_function("u64/bincode/serialize", |b| {
        b.iter(|| bincode::serialize(black_box(&data)).unwrap());
    });

    group.bench_function("u64/wincode/serialized_size", |b| {
        b.iter(|| serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("u64/bincode/serialized_size", |b| {
        b.iter(|| bincode::serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("u64/wincode/deserialize", |b| {
        b.iter(|| deserialize::<u64>(black_box(&serialized)).unwrap());
    });

    group.bench_function("u64/bincode/deserialize", |b| {
        b.iter(|| bincode::deserialize::<u64>(black_box(&serialized)).unwrap());
    });

    group.finish();
}

fn bench_vec_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<u64>");

    for size in [100, 1_000, 10_000] {
        let data: Vec<u64> = (0..size).map(|i| i as u64).collect();
        let data_size = serialized_size(&data).unwrap();
        group.throughput(Throughput::Bytes(data_size));

        let serialized = verify_serialize_into(&data);

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d))
                        .unwrap()
                })
            },
        );

        // Allocating serialization
        group.bench_with_input(
            BenchmarkId::new("wincode/serialize", size),
            &data,
            |b, d| b.iter(|| serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| bincode::serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| deserialize::<Vec<u64>>(black_box(s)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| bincode::deserialize::<Vec<u64>>(black_box(s)).unwrap()),
        );
    }

    group.finish();
}

fn bench_struct_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("SimpleStruct");
    group.throughput(Throughput::Elements(1));

    let data = SimpleStruct {
        id: 12345,
        value: 0xDEADBEEF,
        flag: true,
    };
    let serialized = verify_serialize_into(&data);

    group.bench_function("wincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| {
            bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data))
                .unwrap()
        });
    });

    group.bench_function("wincode/serialize", |b| {
        b.iter(|| serialize(black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialize", |b| {
        b.iter(|| bincode::serialize(black_box(&data)).unwrap());
    });

    group.bench_function("wincode/serialized_size", |b| {
        b.iter(|| serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialized_size", |b| {
        b.iter(|| bincode::serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("wincode/deserialize", |b| {
        b.iter(|| deserialize::<SimpleStruct>(black_box(&serialized)).unwrap());
    });

    group.bench_function("bincode/deserialize", |b| {
        b.iter(|| bincode::deserialize::<SimpleStruct>(black_box(&serialized)).unwrap());
    });

    group.finish();
}

fn bench_pod_struct_single_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("PodStruct");
    group.throughput(Throughput::Elements(1));

    let data = PodStruct {
        a: [42u8; 32],
        b: [17u8; 16],
        c: [99u8; 8],
    };
    let serialized = verify_serialize_into(&data);

    group.bench_function("wincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| {
            bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data))
                .unwrap()
        });
    });

    group.bench_function("wincode/serialize", |b| {
        b.iter(|| serialize(black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialize", |b| {
        b.iter(|| bincode::serialize(black_box(&data)).unwrap());
    });

    group.bench_function("wincode/serialized_size", |b| {
        b.iter(|| serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialized_size", |b| {
        b.iter(|| bincode::serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("wincode/deserialize", |b| {
        b.iter(|| deserialize::<PodStruct>(black_box(&serialized)).unwrap());
    });

    group.bench_function("bincode/deserialize", |b| {
        b.iter(|| bincode::deserialize::<PodStruct>(black_box(&serialized)).unwrap());
    });

    group.finish();
}

fn bench_hashmap_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap<u64, u64>");

    for size in [100, 1_000] {
        let data: HashMap<u64, u64> = (0..size).map(|i: u64| (i, i.wrapping_mul(2))).collect();
        group.throughput(Throughput::Elements(size));

        let serialized = verify_serialize_into(&data);

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d))
                        .unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize", size),
            &data,
            |b, d| b.iter(|| serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| bincode::serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| deserialize::<HashMap<u64, u64>>(black_box(s)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| bincode::deserialize::<HashMap<u64, u64>>(black_box(s)).unwrap()),
        );
    }

    group.finish();
}

fn bench_hashmap_pod_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap<[u8; 16], PodStruct>");

    for size in [100, 1_000] {
        let data: HashMap<[u8; 16], PodStruct> = (0..size)
            .map(|i| {
                let mut key = [0u8; 16];
                key[0] = i as u8;
                key[1] = (i >> 8) as u8;
                (
                    key,
                    PodStruct {
                        a: [i as u8; 32],
                        b: [i as u8; 16],
                        c: [i as u8; 8],
                    },
                )
            })
            .collect();
        group.throughput(Throughput::Elements(size));

        let serialized = verify_serialize_into(&data);

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d))
                        .unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize", size),
            &data,
            |b, d| b.iter(|| serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| bincode::serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| deserialize::<HashMap<[u8; 16], PodStruct>>(black_box(s)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/deserialize", size),
            &serialized,
            |b, s| {
                b.iter(|| {
                    bincode::deserialize::<HashMap<[u8; 16], PodStruct>>(black_box(s)).unwrap()
                })
            },
        );
    }

    group.finish();
}

fn bench_pod_struct_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<PodStruct>");

    for size in [1_000, 10_000] {
        let data: Vec<PodStruct> = (0..size)
            .map(|i| PodStruct {
                a: [i as u8; 32],
                b: [i as u8; 16],
                c: [i as u8; 8],
            })
            .collect();
        let data_size = serialized_size(&data).unwrap();
        group.throughput(Throughput::Bytes(data_size));

        let serialized = verify_serialize_into(&data);

        // In-place serialization
        group.bench_with_input(
            BenchmarkId::new("wincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| {
                    bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d))
                        .unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize", size),
            &data,
            |b, d| b.iter(|| serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| bincode::serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| deserialize::<Vec<PodStruct>>(black_box(s)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/deserialize", size),
            &serialized,
            |b, s| b.iter(|| bincode::deserialize::<Vec<PodStruct>>(black_box(s)).unwrap()),
        );
    }

    group.finish();
}

// Unit enum - only discriminant serialized, size known at compile time.
#[derive(Serialize, Deserialize, SchemaWrite, SchemaRead, Clone, Copy, PartialEq)]
enum UnitEnum {
    A,
    B,
    C,
    D,
}

// All variants same size (2x u64) - enables static size optimization.
#[derive(Serialize, Deserialize, SchemaWrite, SchemaRead, Clone, PartialEq)]
enum SameSizedEnum {
    Transfer { amount: u64, fee: u64 },
    Stake { lamports: u64, rent: u64 },
    Withdraw { amount: u64, timestamp: u64 },
    Close { refund: u64, slot: u64 },
}

// Different sized variants - baseline for comparison.
#[derive(Serialize, Deserialize, SchemaWrite, SchemaRead, Clone, PartialEq)]
enum MixedSizedEnum {
    Small { flag: u8 },
    Medium { value: u64 },
    Large { x: u64, y: u64, z: u64 },
}

// Macro to reduce duplication across enum benchmarks.
macro_rules! bench_enum {
    ($fn_name:ident, $group_name:literal, $type:ty, $data:expr) => {
        fn $fn_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group_name);
            let data: $type = $data;
            let data_size = serialized_size(&data).unwrap();
            group.throughput(Throughput::Bytes(data_size));

            let serialized = verify_serialize_into(&data);

            group.bench_function("wincode/serialize_into", |b| {
                let mut buffer = create_bench_buffer(&data);
                b.iter(|| {
                    serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data)).unwrap()
                });
            });

            group.bench_function("bincode/serialize_into", |b| {
                let mut buffer = create_bench_buffer(&data);
                b.iter(|| {
                    bincode::serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data))
                        .unwrap()
                });
            });

            group.bench_function("wincode/serialize", |b| {
                b.iter(|| serialize(black_box(&data)).unwrap());
            });

            group.bench_function("bincode/serialize", |b| {
                b.iter(|| bincode::serialize(black_box(&data)).unwrap());
            });

            group.bench_function("wincode/serialized_size", |b| {
                b.iter(|| serialized_size(black_box(&data)).unwrap());
            });

            group.bench_function("bincode/serialized_size", |b| {
                b.iter(|| bincode::serialized_size(black_box(&data)).unwrap());
            });

            group.bench_function("wincode/deserialize", |b| {
                b.iter(|| deserialize::<$type>(black_box(&serialized)).unwrap());
            });

            group.bench_function("bincode/deserialize", |b| {
                b.iter(|| bincode::deserialize::<$type>(black_box(&serialized)).unwrap());
            });

            group.finish();
        }
    };
}

// Macro to reduce duplication across Vec enum benchmarks.
macro_rules! bench_vec_enum {
    ($fn_name:ident, $group_name:literal, $type:ty, $data_gen:expr) => {
        fn $fn_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group_name);

            for size in [100, 1_000, 10_000] {
                let data: Vec<$type> = $data_gen(size);
                let data_size = serialized_size(&data).unwrap();

                group
                    .bench_with_input(
                        BenchmarkId::new("wincode/serialize_into", size),
                        &data,
                        |b, d| {
                            let mut buffer = create_bench_buffer(d);
                            b.iter(|| {
                                serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d))
                                    .unwrap()
                            })
                        },
                    )
                    .throughput(Throughput::Bytes(data_size));

                group
                    .bench_with_input(
                        BenchmarkId::new("bincode/serialize_into", size),
                        &data,
                        |b, d| {
                            let mut buffer = create_bench_buffer(d);
                            b.iter(|| {
                                bincode::serialize_into(
                                    black_box(&mut buffer.as_mut_slice()),
                                    black_box(d),
                                )
                                .unwrap()
                            })
                        },
                    )
                    .throughput(Throughput::Bytes(data_size));

                group
                    .bench_with_input(
                        BenchmarkId::new("wincode/serialize", size),
                        &data,
                        |b, d| b.iter(|| serialize(black_box(d)).unwrap()),
                    )
                    .throughput(Throughput::Bytes(data_size));

                group
                    .bench_with_input(
                        BenchmarkId::new("bincode/serialize", size),
                        &data,
                        |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
                    )
                    .throughput(Throughput::Bytes(data_size));

                group
                    .bench_with_input(
                        BenchmarkId::new("wincode/serialized_size", size),
                        &data,
                        |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
                    )
                    .throughput(Throughput::Bytes(data_size));

                group
                    .bench_with_input(
                        BenchmarkId::new("bincode/serialized_size", size),
                        &data,
                        |b, d| b.iter(|| bincode::serialized_size(black_box(d)).unwrap()),
                    )
                    .throughput(Throughput::Bytes(data_size));

                let serialized = verify_serialize_into(&data);

                group
                    .bench_with_input(
                        BenchmarkId::new("wincode/deserialize", size),
                        &serialized,
                        |b, s| b.iter(|| deserialize::<Vec<$type>>(black_box(s)).unwrap()),
                    )
                    .throughput(Throughput::Bytes(data_size));

                group
                    .bench_with_input(
                        BenchmarkId::new("bincode/deserialize", size),
                        &serialized,
                        |b, s| b.iter(|| bincode::deserialize::<Vec<$type>>(black_box(s)).unwrap()),
                    )
                    .throughput(Throughput::Bytes(data_size));
            }

            group.finish();
        }
    };
}

bench_enum!(
    bench_unit_enum_comparison,
    "UnitEnum",
    UnitEnum,
    UnitEnum::C
);

bench_enum!(
    bench_same_sized_enum_comparison,
    "SameSizedEnum",
    SameSizedEnum,
    SameSizedEnum::Transfer {
        amount: 1_000_000,
        fee: 5000
    }
);

bench_enum!(
    bench_mixed_sized_enum_comparison,
    "MixedSizedEnum",
    MixedSizedEnum,
    MixedSizedEnum::Large {
        x: 111,
        y: 222,
        z: 333
    }
);

bench_vec_enum!(
    bench_vec_unit_enum_comparison,
    "Vec<UnitEnum>",
    UnitEnum,
    |size| {
        (0..size)
            .map(|i| match i % 4 {
                0 => UnitEnum::A,
                1 => UnitEnum::B,
                2 => UnitEnum::C,
                _ => UnitEnum::D,
            })
            .collect()
    }
);

bench_vec_enum!(
    bench_vec_same_sized_enum_comparison,
    "Vec<SameSizedEnum>",
    SameSizedEnum,
    |size| {
        (0..size)
            .map(|i| match i % 4 {
                0 => SameSizedEnum::Transfer {
                    amount: i as u64,
                    fee: 5000,
                },
                1 => SameSizedEnum::Stake {
                    lamports: i as u64,
                    rent: 1000,
                },
                2 => SameSizedEnum::Withdraw {
                    amount: i as u64,
                    timestamp: i as u64,
                },
                _ => SameSizedEnum::Close {
                    refund: i as u64,
                    slot: i as u64,
                },
            })
            .collect()
    }
);

bench_vec_enum!(
    bench_vec_mixed_sized_enum_comparison,
    "Vec<MixedSizedEnum>",
    MixedSizedEnum,
    |size| {
        (0..size)
            .map(|i| match i % 3 {
                0 => MixedSizedEnum::Small { flag: i as u8 },
                1 => MixedSizedEnum::Medium { value: i as u64 },
                _ => MixedSizedEnum::Large {
                    x: i as u64,
                    y: i as u64,
                    z: i as u64,
                },
            })
            .collect()
    }
);

#[cfg(feature = "solana-short-vec")]
fn bench_short_u16_comparison(c: &mut Criterion) {
    use {
        solana_short_vec::ShortU16,
        wincode::{len::short_vec::decode_short_u16, serialize_into},
    };
    let mut group = c.benchmark_group("ShortU16");

    let cases = [
        (0x7f_u16, &[0x7f][..]),
        (0x3fff_u16, &[0xff, 0x7f][..]),
        (0xffff_u16, &[0xff, 0xff, 0x03][..]),
    ];

    let mut ser_buffer = [0u8; 3];
    for (val, bytes) in cases {
        group.throughput(Throughput::Bytes(bytes.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("wincode:decode_short_u16", val),
            &bytes,
            |b, bytes| b.iter(|| decode_short_u16(black_box(bytes)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("solana_short_vec:decode_shortu16_len", val),
            &bytes,
            |b, bytes| b.iter(|| solana_short_vec::decode_shortu16_len(black_box(bytes)).unwrap()),
        );

        let short_u16 = ShortU16(val);
        let serialized = bincode::serialize(&short_u16).unwrap();
        assert_eq!(serialize(&short_u16).unwrap(), serialized);
        assert_eq!(
            deserialize::<ShortU16>(&serialized).unwrap().0,
            bincode::deserialize::<ShortU16>(&serialized).unwrap().0
        );

        group.bench_with_input(
            BenchmarkId::new("wincode:serialize", val),
            &short_u16,
            |b, s| {
                b.iter(|| {
                    serialize_into(black_box(&mut ser_buffer.as_mut_slice()), black_box(s)).unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bincode:serialize", val),
            &short_u16,
            |b, s| {
                b.iter(|| {
                    bincode::serialize_into(black_box(&mut ser_buffer.as_mut_slice()), black_box(s))
                        .unwrap()
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode:deserialize", val),
            &serialized,
            |b, s| b.iter(|| deserialize::<ShortU16>(black_box(s)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode:deserialize", val),
            &serialized,
            |b, s| b.iter(|| bincode::deserialize::<ShortU16>(black_box(s)).unwrap()),
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_primitives_comparison,
    bench_vec_comparison,
    bench_struct_comparison,
    bench_pod_struct_single_comparison,
    bench_hashmap_comparison,
    bench_hashmap_pod_comparison,
    bench_pod_struct_comparison,
    bench_unit_enum_comparison,
    bench_same_sized_enum_comparison,
    bench_mixed_sized_enum_comparison,
    bench_vec_unit_enum_comparison,
    bench_vec_same_sized_enum_comparison,
    bench_vec_mixed_sized_enum_comparison,
    bench_short_u16_comparison,
);

criterion_main!(benches);
