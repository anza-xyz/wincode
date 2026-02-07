# wincode

Fast, bincode‑compatible serializer/deserializer focused on in‑place initialization and direct memory writes.

[![Crates.io version](https://img.shields.io/crates/v/wincode.svg?style=flat-square)](https://crates.io/crates/wincode)
[![docs.rs docs](https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square)](https://docs.rs/wincode)

## Quickstart

`wincode` traits are implemented for many built-in types (like `Vec`, integers, etc.).

You'll most likely want to start by using `wincode` on your own struct types, which can be done with the derive macros.

```rust
#[derive(SchemaWrite, SchemaRead)]
struct MyStruct {
    data: Vec<u64>,
    win: bool,
}

let val = MyStruct { data: vec![1,2,3], win: true };
assert_eq!(wincode::serialize(&val).unwrap(), bincode::serialize(&val).unwrap());
```

See the [`docs`](https://docs.rs/wincode) for more details.

## Benchmarks

Run benchmarks comparing `wincode` against `bincode`:

```bash
cargo bench --features derive
```

## Security

Release `v0.1.2` is currently undergoing 3 independent security reviews with the following firms:
- Neodyme
- [OtterSec](audits/wincode_ottersec_audit_0.1.2.pdf)
- Asymmetric Research

Reports will be added to the repo once completed.

### Fuzzing

This crate has been fuzzed using the harness in the `fuzz` folder for roundtrip correctness against bincode.
