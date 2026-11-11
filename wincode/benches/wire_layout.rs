//! Encoding and decoding cost of where a struct's dynamic fields sit.
//!
//! Every arm in a group encodes the same number of wire bytes, the size in the group's name, so
//! the arms differ only in field order. Field order decides which static fields share a trusted
//! window and keep fixed offsets, and so how many bounds checks the backend can drop.
//!
//! For numbers worth quoting, use the protocol from `benchmarks.rs`: 64-byte function alignment,
//! one benchmark per process, pinned to a core, with `-Ctarget-cpu=native`.
//!
//! ```text
//! RUSTFLAGS="-Ctarget-cpu=native -Cllvm-args=-align-all-functions=6" \
//!     cargo bench --features derive --bench wire_layout --no-run
//! taskset -c 4 target/release/deps/wire_layout-<hash> \
//!     --bench --exact "Struct32/interleaved/deserialize"
//! ```

use {
    criterion::{
        Bencher, Criterion, Throughput, criterion_group, criterion_main, measurement::WallTime,
    },
    std::hint::black_box,
    wincode::{
        SchemaRead, SchemaWrite, config::DefaultConfig, deserialize, serialize_into,
        serialized_size,
    },
};

/// Each static field sits between dynamic ones, so no window forms.
#[derive(SchemaWrite, SchemaRead)]
struct Alternating {
    h: u64,
    d1: Option<u8>,
    i: u64,
    d2: Option<u8>,
    f: u32,
    d3: Option<u8>,
    e: u16,
    d4: Option<u8>,
    g: u16,
}

impl Alternating {
    fn new() -> Self {
        Self {
            h: 1,
            d1: Some(11),
            i: 2,
            d2: Some(12),
            f: 3,
            d3: Some(13),
            e: 4,
            d4: Some(14),
            g: 5,
        }
    }
}

/// Serialized size shared by all five arms.
const WIRE: usize = 32;

/// No dynamic field, so every offset is fixed.
#[derive(SchemaWrite, SchemaRead)]
struct Header {
    h: u64,
    i: u64,
    f: u32,
    g: u32,
    d: u16,
    e: u16,
    a: u8,
    b: u8,
    c: u8,
    k: u8,
}

impl Header {
    fn new() -> Self {
        Self {
            h: 1,
            i: 2,
            f: 3,
            g: 4,
            d: 5,
            e: 6,
            a: 7,
            b: 8,
            c: 9,
            k: 10,
        }
    }
}

/// Eight static fields worth 30 bytes, then a dynamic one: the first eight offsets are fixed.
#[derive(SchemaWrite, SchemaRead)]
struct Prefixed {
    h: u64,
    i: u64,
    f: u32,
    g: u32,
    d: u16,
    e: u16,
    a: u8,
    b: u8,
    tail: Option<u8>,
}

impl Prefixed {
    fn new() -> Self {
        Self {
            h: 1,
            i: 2,
            f: 3,
            g: 4,
            d: 5,
            e: 6,
            a: 7,
            b: 8,
            tail: Some(11),
        }
    }
}

/// Opens with the dynamic field, so the static fields after it get no window.
#[derive(SchemaWrite, SchemaRead)]
struct Suffixed {
    head: Option<u8>,
    h: u64,
    i: u64,
    f: u32,
    g: u32,
    d: u16,
    e: u16,
    a: u8,
    b: u8,
}

impl Suffixed {
    fn new() -> Self {
        Self {
            head: Some(11),
            h: 1,
            i: 2,
            f: 3,
            g: 4,
            d: 5,
            e: 6,
            a: 7,
            b: 8,
        }
    }
}

/// Alternates static and dynamic fields, so only the first two fields share a window.
#[derive(SchemaWrite, SchemaRead)]
struct Interleaved {
    h: u64,
    d: u16,
    first: Option<u8>,
    i: u64,
    f: u32,
    second: Option<u8>,
    g: u32,
    e: u16,
}

impl Interleaved {
    fn new() -> Self {
        Self {
            h: 1,
            d: 5,
            first: Some(11),
            i: 2,
            f: 3,
            second: Some(12),
            g: 4,
            e: 6,
        }
    }
}

/// Encode once, checking the arm is the size the group claims.
fn encoded<T>(data: &T) -> [u8; WIRE]
where
    T: SchemaWrite<DefaultConfig, Src = T>,
{
    assert_eq!(serialized_size(data).unwrap() as usize, WIRE);
    let mut bytes = [0u8; WIRE];
    serialize_into(bytes.as_mut_slice(), data).unwrap();
    bytes
}

/// Keep setup inside the returned closure: criterion filters inside `bench_function`, so setup in
/// the bench fn would run even for benchmarks a `--bench` filter excludes.
fn run_serialize<T>(new_data: impl Fn() -> T) -> impl FnMut(&mut Bencher<'_, WallTime>)
where
    T: SchemaWrite<DefaultConfig, Src = T>,
{
    move |b| {
        let data = new_data();
        let mut buffer = encoded(&data);
        b.iter(|| serialize_into(black_box(buffer.as_mut_slice()), black_box(&data)).unwrap());
    }
}

/// Like [`run_serialize`], but decodes the encoded bytes.
fn run_deserialize<T, R>(
    new_data: impl Fn() -> T,
    deserialize_fn: impl Fn(&[u8]) -> R,
) -> impl FnMut(&mut Bencher<'_, WallTime>)
where
    T: SchemaWrite<DefaultConfig, Src = T>,
{
    move |b| {
        let bytes = encoded(&new_data());
        b.iter(|| deserialize_fn(black_box(bytes.as_slice())));
    }
}

/// Measures how the position of a struct's dynamic fields affects encoding and decoding.
///
/// The derive opens one trusted window over the leading static fields when there are at least
/// two of them. `header` gets a window over the whole struct, `prefixed` over all but its last
/// field and `interleaved` over its first two fields, while `suffixed` and `alternating` get
/// none.
///
/// The dynamic field is an `Option<u8>`. Its size depends on the variant, but it is owned, tiny
/// and allocation-free, so it adds no other cost.
#[inline(never)]
fn bench_field_runs(c: &mut Criterion) {
    let mut group = c.benchmark_group("Struct32");
    group.throughput(Throughput::Elements(1));

    group.bench_function("header/serialize_into", run_serialize(Header::new));
    group.bench_function(
        "header/deserialize",
        run_deserialize(Header::new, |s| deserialize::<Header>(s).unwrap()),
    );

    group.bench_function("prefixed/serialize_into", run_serialize(Prefixed::new));
    group.bench_function(
        "prefixed/deserialize",
        run_deserialize(Prefixed::new, |s| deserialize::<Prefixed>(s).unwrap()),
    );

    group.bench_function("suffixed/serialize_into", run_serialize(Suffixed::new));
    group.bench_function(
        "suffixed/deserialize",
        run_deserialize(Suffixed::new, |s| deserialize::<Suffixed>(s).unwrap()),
    );

    group.bench_function(
        "alternating/serialize_into",
        run_serialize(Alternating::new),
    );
    group.bench_function(
        "alternating/deserialize",
        run_deserialize(Alternating::new, |s| deserialize::<Alternating>(s).unwrap()),
    );

    group.bench_function(
        "interleaved/serialize_into",
        run_serialize(Interleaved::new),
    );
    group.bench_function(
        "interleaved/deserialize",
        run_deserialize(Interleaved::new, |s| deserialize::<Interleaved>(s).unwrap()),
    );

    group.finish();
}

criterion_group!(benches, bench_field_runs);

criterion_main!(benches);
