use {
    criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput},
    serde::{Deserialize, Serialize},
    std::collections::HashMap,
    // `serialize` is only used in `verify_serialize_into` for verification purposes, not in benchmarks
    wincode::{deserialize, serialize, serialize_into, serialized_size, SchemaRead, SchemaWrite},
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


/// this function is used for verification only and is not part of the benchmarked code.
fn verify_serialize_into<T>(data: &T) -> Vec<u8>
where
    T: SchemaWrite<Src = T> + Serialize + ?Sized,
{
    let serialized = bincode::serialize(data).unwrap();
    assert_eq!(serialize(data).unwrap(), serialized);
    
    let size = serialized_size(data).unwrap() as usize;
    let mut buffer = vec![0u8; size];
    serialize_into(&mut buffer.as_mut_slice(), data).unwrap();
    assert_eq!(&buffer[..], &serialized[..]);
    
    serialized
}

fn create_bench_buffer<T>(data: &T) -> Vec<u8>
where
    T: SchemaWrite<Src = T> + ?Sized,
{
    let size = serialized_size(data).unwrap() as usize;
    vec![0u8; size]
}

fn bench_primitives_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Primitives");
    group.throughput(Throughput::Elements(1));

    let data = 0xDEADBEEFCAFEBABEu64;
    let serialized = verify_serialize_into(&data);

    group.bench_function("u64/wincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data)).unwrap());
    });

    group.bench_function("u64/wincode/serialized_size", |b| {
        b.iter(|| serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("u64/bincode/serialize", |b| {
        b.iter(|| bincode::serialize(black_box(&data)).unwrap());
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
                b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap())
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
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

    // Serialize benchmarks
    group.bench_function("wincode/serialize_into", |b| {
        let mut buffer = create_bench_buffer(&data);
        b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(&data)).unwrap());
    });

    group.bench_function("wincode/serialized_size", |b| {
        b.iter(|| serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialize", |b| {
        b.iter(|| bincode::serialize(black_box(&data)).unwrap());
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

    group.bench_function("wincode/serialized_size", |b| {
        b.iter(|| serialized_size(black_box(&data)).unwrap());
    });

    group.bench_function("bincode/serialize", |b| {
        b.iter(|| bincode::serialize(black_box(&data)).unwrap());
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
                b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap())
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
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
                b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap())
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
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

        group.bench_with_input(
            BenchmarkId::new("wincode/serialize_into", size),
            &data,
            |b, d| {
                let mut buffer = create_bench_buffer(d);
                b.iter(|| serialize_into(black_box(&mut buffer.as_mut_slice()), black_box(d)).unwrap())
            },
        );

        group.bench_with_input(
            BenchmarkId::new("wincode/serialized_size", size),
            &data,
            |b, d| b.iter(|| serialized_size(black_box(d)).unwrap()),
        );

        group.bench_with_input(
            BenchmarkId::new("bincode/serialize", size),
            &data,
            |b, d| b.iter(|| bincode::serialize(black_box(d)).unwrap()),
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

criterion_group!(
    benches,
    bench_primitives_comparison,
    bench_vec_comparison,
    bench_struct_comparison,
    bench_pod_struct_single_comparison,
    bench_hashmap_comparison,
    bench_hashmap_pod_comparison,
    bench_pod_struct_comparison,
);

criterion_main!(benches);
