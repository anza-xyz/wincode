use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use serde::{Deserialize, Serialize};
use wincode::{containers::Pod, deserialize, serialize, SchemaRead, SchemaWrite};
use std::collections::HashMap;

#[derive(Serialize, Deserialize, SchemaWrite, SchemaRead, Clone)]
struct SimpleStruct {
    id: u64,
    value: u64,
    flag: bool,
}

#[repr(transparent)]
#[derive(Clone, Copy, SchemaWrite, SchemaRead, Serialize, Deserialize)]
struct PodStruct([u8; 32]);

// ============================================================================
// COMPARISON BENCHMARKS (wincode vs bincode)
// ============================================================================

fn bench_primitives_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Primitives");
    group.throughput(Throughput::Elements(1));
    
    let data = 0xDEADBEEFCAFEBABEu64;
    let serialized = bincode::serialize(&data).unwrap();
    assert_eq!(wincode::serialize(&data).unwrap(), serialized);
    
    group.bench_function("u64/wincode", |b| {
        b.iter(|| wincode::deserialize::<u64>(black_box(&serialized)).unwrap());
    });
    
    group.bench_function("u64/bincode", |b| {
        b.iter(|| bincode::deserialize::<u64>(black_box(&serialized)).unwrap());
    });
    
    group.finish();
}

fn bench_vec_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<u64>");
    
    for size in [100, 1_000, 10_000] {
        let data: Vec<u64> = (0..size).map(|i| i as u64).collect();
        group.throughput(Throughput::Bytes((size * 8) as u64));
        
        let serialized = bincode::serialize(&data).unwrap();
        assert_eq!(wincode::serialize(&data).unwrap(), serialized);
        
        group.bench_with_input(
            BenchmarkId::new("wincode", size),
            &serialized,
            |b, s| b.iter(|| wincode::deserialize::<Vec<u64>>(black_box(s)).unwrap()),
        );
        
        group.bench_with_input(
            BenchmarkId::new("bincode", size),
            &serialized,
            |b, s| b.iter(|| bincode::deserialize::<Vec<u64>>(black_box(s)).unwrap()),
        );
    }
    
    group.finish();
}

fn bench_struct_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("SimpleStruct");
    group.throughput(Throughput::Elements(1));
    
    let data = SimpleStruct { id: 12345, value: 0xDEADBEEF, flag: true };
    let serialized = bincode::serialize(&data).unwrap();
    assert_eq!(wincode::serialize(&data).unwrap(), serialized);
    
    group.bench_function("wincode", |b| {
        b.iter(|| wincode::deserialize::<SimpleStruct>(black_box(&serialized)).unwrap());
    });
    
    group.bench_function("bincode", |b| {
        b.iter(|| bincode::deserialize::<SimpleStruct>(black_box(&serialized)).unwrap());
    });
    
    group.finish();
}

fn bench_hashmap_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap<u64, u64>");
    
    for size in [100, 1_000] {
        let data: HashMap<u64, u64> = (0..size).map(|i| (i as u64, i * 2)).collect();
        group.throughput(Throughput::Elements(size as u64));
        
        let serialized = bincode::serialize(&data).unwrap();
        assert_eq!(wincode::serialize(&data).unwrap(), serialized);
        
        group.bench_with_input(
            BenchmarkId::new("wincode", size),
            &serialized,
            |b, s| b.iter(|| wincode::deserialize::<HashMap<u64, u64>>(black_box(s)).unwrap()),
        );
        
        group.bench_with_input(
            BenchmarkId::new("bincode", size),
            &serialized,
            |b, s| b.iter(|| bincode::deserialize::<HashMap<u64, u64>>(black_box(s)).unwrap()),
        );
    }
    
    group.finish();
}

// ============================================================================
// POD OPTIMIZATION BENCHMARKS
// ============================================================================

fn bench_pod_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("Pod Optimization");
    
    for size in [1_000, 10_000] {
        let data: Vec<PodStruct> = (0..size).map(|i| PodStruct([i as u8; 32])).collect();
        let bytes = (size * 32) as u64;
        group.throughput(Throughput::Bytes(bytes));
        
        // Regular Vec<PodStruct>
        let serialized_regular = serialize(&data).unwrap();
        group.bench_with_input(
            BenchmarkId::new("regular", size),
            &serialized_regular,
            |b, s| b.iter(|| deserialize::<Vec<PodStruct>>(black_box(s)).unwrap()),
        );
        
        // Vec<Pod<PodStruct>> - optimized
        #[derive(SchemaWrite, SchemaRead)]
        struct WithPod {
            #[wincode(with = "wincode::containers::Vec<Pod<_>>")]
            data: Vec<PodStruct>,
        }
        
        let with_pod = WithPod { data: data.clone() };
        let serialized_pod = serialize(&with_pod).unwrap();
        group.bench_with_input(
            BenchmarkId::new("Pod optimized", size),
            &serialized_pod,
            |b, s| b.iter(|| deserialize::<WithPod>(black_box(s)).unwrap()),
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_primitives_comparison,
    bench_vec_comparison,
    bench_struct_comparison,
    bench_hashmap_comparison,
    bench_pod_optimization,
);

criterion_main!(benches);
