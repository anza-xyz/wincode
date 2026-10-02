//! What a struct's field layout costs its encoding and decoding.
//!
//! The derive emits one read or write per field at constant offsets, so how much the backend
//! can merge, and how many bounds checks it can drop, follows from the fields themselves:
//! where they sit, and which of them have a size known ahead of time. Arms in a group encode
//! the same number of wire bytes -- the size the group is named for -- so a gap between two of
//! them reflects whatever that group varies rather than a difference in how much data moved.
//!
//! For a number worth quoting use the protocol in `benchmarks.rs`: 64-byte function alignment,
//! one benchmark per process, pinned to a core, keeping `-Ctarget-cpu=native`.
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

/// Every static field stands alone between dynamic ones, so no run holds more than one field
/// and none is worth a trusted window.
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

/// Dynamic field first, so the static run trails it instead of leading it. No offset is
/// fixed, but the run's total size still is.
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

/// Static and dynamic fields alternating, so the static bytes fall into three runs rather than
/// one. The worst shape for the fields, and the one that gains least from covering only the
/// leading run.
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

/// Setup stays behind the helper: criterion filters inside `bench_function`, so setup left in
/// the bench fn runs even for benchmarks a `--bench` filter excluded.
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

/// [`run_serialize`] for the decode, which measures against the encoded bytes.
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

/// Measures the cost of placing a struct's dynamic fields in various positions.
///
/// Field positions decide how the statically sized fields fall into runs, and a run has to hold
/// at least two of them to be worth a trusted window. `header` has no dynamic field at all, so
/// its statics form one run; `prefixed` and `suffixed` put one at an end, leaving a single run
/// beside it; `interleaved` splits the statics into three short runs; and `alternating` sets
/// every static field apart, so no run is long enough to win a window. Nothing after a dynamic
/// field has a fixed offset either, so the arms differ in how many of their fields keep one.
///
/// The dynamic field is an `Option<u8>`: its size varies with the variant, but it is owned,
/// tiny and allocation-free, so neither side pays for anything else.
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
