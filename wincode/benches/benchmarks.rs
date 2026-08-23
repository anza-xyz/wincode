//! # Running these benchmarks
//!
//! You can run the full suite with `cargo bench`. It needs no special flags and gives the
//! general view: how wincode compares against bincode across the type and collection
//! shapes below.
//!
//! In order to do a targeted comparison of a specific code change, run a side-by-side
//! baseline comparison on a single benchmark instead. A criterion timing depends on the
//! layout of the whole binary, so an unrelated edit elsewhere can move a number further
//! than the change under test does. Build against both revisions with 64-byte function
//! alignment, and measure one benchmark per process, pinned to a core:
//!
//! ```text
//! # build only: RUSTFLAGS applies at build time, and the measured run must not be cargo's
//! RUSTFLAGS="-Cllvm-args=-align-all-functions=6" cargo bench --bench benchmarks --no-run
//!
//! # copy the binary name printed above, and record a baseline from one benchmark
//! taskset -c 4 target/release/deps/benchmarks-<hash> --bench \
//!     --exact "BTreeMap<u64, u64>/wincode/deserialize/1000" --save-baseline before
//!
//! # rebuild on the other revision, then compare its binary against that baseline
//! taskset -c 4 target/release/deps/benchmarks-<other-hash> --bench \
//!     --exact "BTreeMap<u64, u64>/wincode/deserialize/1000" --baseline before
//! ```
//!
//! `--list` prints the available ids. Each bench fn is `#[inline(never)]`, so those
//! binaries also carry one symbol per benchmark, and `objdump -d` on it shows what a
//! change did to the emitted instructions.

use {
    criterion::{
        Bencher, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
        measurement::WallTime,
    },
    rand::{Rng as _, SeedableRng},
    serde::{Deserialize, Serialize},
    std::{
        collections::{BTreeMap, BTreeSet, HashMap, LinkedList, VecDeque},
        hint::black_box,
    },
    wincode::{
        SchemaRead, SchemaWrite, config::DefaultConfig, deserialize, serialize, serialize_into,
        serialized_size,
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
    serialize_into(buffer.as_mut_slice(), data).unwrap();

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

/// Build a benchmark's data when criterion runs this, then time `body` against it.
///
/// Keep `new_data` behind this helper: criterion filters inside `bench_function`, so
/// setup left in the enclosing bench fn runs even for benchmarks a `--bench` filter
/// excluded, and every measurement then depends on what the other groups allocated.
fn run_with_t<T, R>(
    new_data: impl Fn() -> T,
    body: impl Fn(&T) -> R,
) -> impl FnMut(&mut Bencher<'_, WallTime>) {
    move |b| {
        let data = new_data();
        b.iter(|| body(black_box(&data)));
    }
}

/// [`run_with_t`] plus a buffer sized for the encoding, for the in-place writes.
///
/// The buffer arrives without `black_box`, unlike the data: whether the writer is the
/// slice or a reference to it changes what is measured, so that choice stays with the
/// body, and so does the `black_box` that pins it.
fn run_with_buf<T, R>(
    new_data: impl Fn() -> T,
    body: impl Fn(&mut [u8], &T) -> R,
) -> impl FnMut(&mut Bencher<'_, WallTime>)
where
    T: SchemaWrite<DefaultConfig, Src = T>,
{
    move |b| {
        let data = new_data();
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| body(buffer.as_mut_slice(), black_box(&data)));
    }
}

/// [`run_with_t`] for the deserialization benchmarks, which measure against encoded bytes.
fn run_with_bytes<T, R>(
    new_data: impl Fn() -> T,
    body: impl Fn(&[u8]) -> R,
) -> impl FnMut(&mut Bencher<'_, WallTime>)
where
    T: SchemaWrite<DefaultConfig, Src = T> + Serialize,
{
    move |b| {
        let bytes = verify_serialize_into(&new_data());
        b.iter(|| body(black_box(&bytes)));
    }
}

#[inline(never)]
fn bench_primitives_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Primitives");
    group.throughput(Throughput::Elements(1));

    let new_data = || 0xDEADBEEFCAFEBABEu64;

    // In-place serialization (measures pure serialization, no allocation)
    group.bench_function(
        "u64/wincode/serialize_into",
        run_with_buf(new_data, |buffer, d| {
            serialize_into(black_box(buffer), d).unwrap()
        }),
    );

    group.bench_function(
        "u64/bincode/serialize_into",
        run_with_buf(new_data, |buffer, d| {
            bincode::serialize_into(black_box(buffer), d).unwrap()
        }),
    );

    group.bench_function(
        "u64/wincode/serialize",
        run_with_t(new_data, |d| serialize(d).unwrap()),
    );

    group.bench_function(
        "u64/bincode/serialize",
        run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
    );

    group.bench_function(
        "u64/wincode/serialized_size",
        run_with_t(new_data, |d| serialized_size(d).unwrap()),
    );

    group.bench_function(
        "u64/bincode/serialized_size",
        run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
    );

    group.bench_function(
        "u64/wincode/deserialize",
        run_with_bytes(new_data, |s| deserialize::<u64>(s).unwrap()),
    );

    group.bench_function(
        "u64/bincode/deserialize",
        run_with_bytes(new_data, |s| bincode::deserialize::<u64>(s).unwrap()),
    );

    group.finish();
}

#[inline(never)]
fn bench_char_deserialization(c: &mut Criterion) {
    c.bench_function("char/wincode/deserialize", |b| {
        let str: String = rand::prelude::SmallRng::seed_from_u64(0x42)
            .sample_iter::<char, _>(rand::distr::StandardUniform)
            .take(10_000)
            .collect();

        b.iter(|| {
            let mut bytes = black_box(str.as_bytes());
            let mut sum: u32 = 0;
            while !bytes.is_empty() {
                let ch: char = wincode::deserialize_from(&mut bytes).unwrap();
                sum = sum.wrapping_add(ch as u32);
            }
            black_box(sum);
        });
    });
}

#[inline(never)]
fn bench_vec_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<u64>");

    for size in [100, 1_000, 10_000] {
        let new_data = || -> Vec<u64> { (0..size).collect() };
        group.throughput(Throughput::Elements(size));

        group.bench_function(
            BenchmarkId::new("wincode/serialize_into", size),
            run_with_buf(new_data, |buffer, d| {
                serialize_into(black_box(buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize_into", size),
            run_with_buf(new_data, |buffer, d| {
                bincode::serialize_into(black_box(buffer), d).unwrap()
            }),
        );

        // Allocating serialization
        group.bench_function(
            BenchmarkId::new("wincode/serialize", size),
            run_with_t(new_data, |d| serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize", size),
            run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialized_size", size),
            run_with_t(new_data, |d| serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialized_size", size),
            run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/deserialize", size),
            run_with_bytes(new_data, |s| deserialize::<Vec<u64>>(s).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/deserialize", size),
            run_with_bytes(new_data, |s| bincode::deserialize::<Vec<u64>>(s).unwrap()),
        );
    }

    group.finish();
}

#[inline(never)]
fn bench_struct_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("SimpleStruct");
    group.throughput(Throughput::Elements(1));

    let new_data = || SimpleStruct {
        id: 12345,
        value: 0xDEADBEEF,
        flag: true,
    };

    group.bench_function(
        "wincode/serialize_into",
        run_with_buf(new_data, |buffer, d| {
            serialize_into(black_box(buffer), d).unwrap()
        }),
    );

    group.bench_function(
        "bincode/serialize_into",
        run_with_buf(new_data, |buffer, d| {
            bincode::serialize_into(black_box(buffer), d).unwrap()
        }),
    );

    group.bench_function(
        "wincode/serialize",
        run_with_t(new_data, |d| serialize(d).unwrap()),
    );

    group.bench_function(
        "bincode/serialize",
        run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
    );

    group.bench_function(
        "wincode/serialized_size",
        run_with_t(new_data, |d| serialized_size(d).unwrap()),
    );

    group.bench_function(
        "bincode/serialized_size",
        run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
    );

    group.bench_function(
        "wincode/deserialize",
        run_with_bytes(new_data, |s| deserialize::<SimpleStruct>(s).unwrap()),
    );

    group.bench_function(
        "bincode/deserialize",
        run_with_bytes(new_data, |s| {
            bincode::deserialize::<SimpleStruct>(s).unwrap()
        }),
    );

    group.finish();
}

#[inline(never)]
fn bench_pod_struct_single_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("PodStruct");
    group.throughput(Throughput::Elements(1));

    let new_data = || PodStruct {
        a: [42u8; 32],
        b: [17u8; 16],
        c: [99u8; 8],
    };

    group.bench_function(
        "wincode/serialize_into",
        run_with_buf(new_data, |buffer, d| {
            serialize_into(black_box(buffer), d).unwrap()
        }),
    );

    group.bench_function(
        "bincode/serialize_into",
        run_with_buf(new_data, |buffer, d| {
            bincode::serialize_into(black_box(buffer), d).unwrap()
        }),
    );

    group.bench_function(
        "wincode/serialize",
        run_with_t(new_data, |d| serialize(d).unwrap()),
    );

    group.bench_function(
        "bincode/serialize",
        run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
    );

    group.bench_function(
        "wincode/serialized_size",
        run_with_t(new_data, |d| serialized_size(d).unwrap()),
    );

    group.bench_function(
        "bincode/serialized_size",
        run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
    );

    group.bench_function(
        "wincode/deserialize",
        run_with_bytes(new_data, |s| deserialize::<PodStruct>(s).unwrap()),
    );

    group.bench_function(
        "bincode/deserialize",
        run_with_bytes(new_data, |s| bincode::deserialize::<PodStruct>(s).unwrap()),
    );

    group.finish();
}

#[inline(never)]
fn bench_hashmap_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap<u64, u64>");

    for size in [100, 1_000] {
        let new_data =
            || -> HashMap<u64, u64> { (0..size).map(|i: u64| (i, i.wrapping_mul(2))).collect() };
        group.throughput(Throughput::Elements(size));

        group.bench_function(
            BenchmarkId::new("wincode/serialize_into", size),
            run_with_buf(new_data, |buffer, d| {
                serialize_into(black_box(buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize_into", size),
            run_with_buf(new_data, |buffer, d| {
                bincode::serialize_into(black_box(buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialize", size),
            run_with_t(new_data, |d| serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize", size),
            run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialized_size", size),
            run_with_t(new_data, |d| serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialized_size", size),
            run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/deserialize", size),
            run_with_bytes(new_data, |s| deserialize::<HashMap<u64, u64>>(s).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/deserialize", size),
            run_with_bytes(new_data, |s| {
                bincode::deserialize::<HashMap<u64, u64>>(s).unwrap()
            }),
        );
    }

    group.finish();
}

#[inline(never)]
fn bench_hashmap_pod_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap<[u8; 16], PodStruct>");

    for size in [100, 1_000] {
        let new_data = || -> HashMap<[u8; 16], PodStruct> {
            (0..size)
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
                .collect()
        };
        group.throughput(Throughput::Elements(size));

        group.bench_function(
            BenchmarkId::new("wincode/serialize_into", size),
            run_with_buf(new_data, |buffer, d| {
                serialize_into(black_box(buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize_into", size),
            run_with_buf(new_data, |buffer, d| {
                bincode::serialize_into(black_box(buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialize", size),
            run_with_t(new_data, |d| serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize", size),
            run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialized_size", size),
            run_with_t(new_data, |d| serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialized_size", size),
            run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/deserialize", size),
            run_with_bytes(new_data, |s| {
                deserialize::<HashMap<[u8; 16], PodStruct>>(s).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("bincode/deserialize", size),
            run_with_bytes(new_data, |s| {
                bincode::deserialize::<HashMap<[u8; 16], PodStruct>>(s).unwrap()
            }),
        );
    }

    group.finish();
}

#[inline(never)]
fn bench_pod_struct_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<PodStruct>");

    for size in [1_000, 10_000] {
        let new_data = || -> Vec<PodStruct> {
            (0..size)
                .map(|i| PodStruct {
                    a: [i as u8; 32],
                    b: [i as u8; 16],
                    c: [i as u8; 8],
                })
                .collect()
        };
        group.throughput(Throughput::Elements(size));

        // In-place serialization
        group.bench_function(
            BenchmarkId::new("wincode/serialize_into", size),
            run_with_buf(new_data, |mut buffer, d| {
                serialize_into(black_box(&mut buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize_into", size),
            run_with_buf(new_data, |mut buffer, d| {
                bincode::serialize_into(black_box(&mut buffer), d).unwrap()
            }),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialize", size),
            run_with_t(new_data, |d| serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialize", size),
            run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/serialized_size", size),
            run_with_t(new_data, |d| serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/serialized_size", size),
            run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("wincode/deserialize", size),
            run_with_bytes(new_data, |s| deserialize::<Vec<PodStruct>>(s).unwrap()),
        );

        group.bench_function(
            BenchmarkId::new("bincode/deserialize", size),
            run_with_bytes(new_data, |s| {
                bincode::deserialize::<Vec<PodStruct>>(s).unwrap()
            }),
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
        #[inline(never)]
        fn $fn_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group_name);
            let new_data = || -> $type { $data };
            group.throughput(Throughput::Elements(1));

            group.bench_function(
                "wincode/serialize_into",
                run_with_buf(new_data, |mut buffer, d| {
                    serialize_into(black_box(&mut buffer), d).unwrap()
                }),
            );

            group.bench_function(
                "bincode/serialize_into",
                run_with_buf(new_data, |mut buffer, d| {
                    bincode::serialize_into(black_box(&mut buffer), d).unwrap()
                }),
            );

            group.bench_function(
                "wincode/serialize",
                run_with_t(new_data, |d| serialize(d).unwrap()),
            );

            group.bench_function(
                "bincode/serialize",
                run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
            );

            group.bench_function(
                "wincode/serialized_size",
                run_with_t(new_data, |d| serialized_size(d).unwrap()),
            );

            group.bench_function(
                "bincode/serialized_size",
                run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
            );

            group.bench_function(
                "wincode/deserialize",
                run_with_bytes(new_data, |s| deserialize::<$type>(s).unwrap()),
            );

            group.bench_function(
                "bincode/deserialize",
                run_with_bytes(new_data, |s| bincode::deserialize::<$type>(s).unwrap()),
            );

            group.finish();
        }
    };
}

// Macro to reduce duplication across Vec enum benchmarks.
macro_rules! bench_vec_enum {
    ($fn_name:ident, $group_name:literal, $type:ty, $data_gen:expr) => {
        #[inline(never)]
        fn $fn_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group_name);

            for size in [100, 1_000, 10_000] {
                let new_data = || -> Vec<$type> { $data_gen(size) };
                group.throughput(Throughput::Elements(size));

                group.bench_function(
                    BenchmarkId::new("wincode/serialize_into", size),
                    run_with_buf(new_data, |mut buffer, d| {
                        serialize_into(black_box(&mut buffer), d).unwrap()
                    }),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/serialize_into", size),
                    run_with_buf(new_data, |mut buffer, d| {
                        bincode::serialize_into(black_box(&mut buffer), d).unwrap()
                    }),
                );

                group.bench_function(
                    BenchmarkId::new("wincode/serialize", size),
                    run_with_t(new_data, |d| serialize(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/serialize", size),
                    run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("wincode/serialized_size", size),
                    run_with_t(new_data, |d| serialized_size(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/serialized_size", size),
                    run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("wincode/deserialize", size),
                    run_with_bytes(new_data, |s| deserialize::<Vec<$type>>(s).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/deserialize", size),
                    run_with_bytes(new_data, |s| bincode::deserialize::<Vec<$type>>(s).unwrap()),
                );
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
                    amount: i,
                    fee: 5000,
                },
                1 => SameSizedEnum::Stake {
                    lamports: i,
                    rent: 1000,
                },
                2 => SameSizedEnum::Withdraw {
                    amount: i,
                    timestamp: i,
                },
                _ => SameSizedEnum::Close { refund: i, slot: i },
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
                1 => MixedSizedEnum::Medium { value: i },
                _ => MixedSizedEnum::Large { x: i, y: i, z: i },
            })
            .collect()
    }
);

macro_rules! bench_collection {
    ($fn_name:ident, $group_name:literal, $type:ty, $data_gen:expr) => {
        #[inline(never)]
        fn $fn_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group_name);

            for size in [100, 1_000] {
                let new_data = || -> $type { $data_gen(size) };
                group.throughput(Throughput::Elements(size));

                group.bench_function(
                    BenchmarkId::new("wincode/serialize_into", size),
                    run_with_buf(new_data, |mut buffer, d| {
                        serialize_into(black_box(&mut buffer), d).unwrap()
                    }),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/serialize_into", size),
                    run_with_buf(new_data, |mut buffer, d| {
                        bincode::serialize_into(black_box(&mut buffer), d).unwrap()
                    }),
                );

                group.bench_function(
                    BenchmarkId::new("wincode/serialize", size),
                    run_with_t(new_data, |d| serialize(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/serialize", size),
                    run_with_t(new_data, |d| bincode::serialize(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("wincode/serialized_size", size),
                    run_with_t(new_data, |d| serialized_size(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/serialized_size", size),
                    run_with_t(new_data, |d| bincode::serialized_size(d).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("wincode/deserialize", size),
                    run_with_bytes(new_data, |s| deserialize::<$type>(s).unwrap()),
                );

                group.bench_function(
                    BenchmarkId::new("bincode/deserialize", size),
                    run_with_bytes(new_data, |s| bincode::deserialize::<$type>(s).unwrap()),
                );
            }

            group.finish();
        }
    };
}

bench_collection!(
    bench_btreemap_comparison,
    "BTreeMap<u64, u64>",
    BTreeMap<u64, u64>,
    |size| (0..size).map(|i: u64| (i, i)).collect()
);

bench_collection!(
    bench_btreeset_comparison,
    "BTreeSet<u64>",
    BTreeSet<u64>,
    |size| (0..size).collect()
);

bench_collection!(
    bench_linkedlist_comparison,
    "LinkedList<u64>",
    LinkedList<u64>,
    |size| (0..size).collect()
);

bench_collection!(
    bench_vecdeque_comparison,
    "VecDeque<u64>",
    VecDeque<u64>,
    |size| (0..size).collect()
);

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
    bench_btreemap_comparison,
    bench_btreeset_comparison,
    bench_linkedlist_comparison,
    bench_vecdeque_comparison,
    bench_char_deserialization,
);

criterion_main!(benches);
