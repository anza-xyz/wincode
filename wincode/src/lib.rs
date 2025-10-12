//! wincode is a fast, bincode‑compatible serializer/deserializer focused on in‑place
//! initialization and direct memory writes.
//!
//! In short, `wincode` operates over traits that facilitate direct writes of memory
//! into final destinations (including heap-allocated buffers) without intermediate
//! staging buffers.
//!
//! # Quickstart
//!
//! `wincode` traits are implemented for many built-in types (like `Vec`, integers, etc.).
//!
//! You'll most likely want to start by using `wincode` on your own struct types, which can be
//! done easily with the derive macros.
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use serde::{Serialize, Deserialize};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # #[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
//! #
//! #[derive(SchemaWrite, SchemaRead)]
//! struct MyStruct {
//!     data: Vec<u64>,
//!     win: bool,
//! }
//!
//! let val = MyStruct { data: vec![1,2,3], win: true };
//! assert_eq!(wincode::serialize(&val).unwrap(), bincode::serialize(&val).unwrap());
//! # }
//! ```
//!
//! For POD‑like fields (bytes, arrays of bytes, POD newtypes), use [`containers`]
//! to leverage optimized read/write implementations.
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{containers::{self, Pod}};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # use serde::{Serialize, Deserialize};
//! # #[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
//! #[derive(SchemaWrite, SchemaRead)]
//! struct MyStruct {
//!     #[wincode(with = "containers::Vec<Pod<_>>")]
//!     data: Vec<u8>,
//!     #[wincode(with = "containers::Vec<Pod<_>>")]
//!     addresses: Vec<[u8; 32]>,
//! }
//!
//! let val = MyStruct { data: vec![1,2,3], addresses: vec![[0; 32], [1; 32]] };
//! assert_eq!(wincode::serialize(&val).unwrap(), bincode::serialize(&val).unwrap());
//! # }
//! ```
//!
//! # Motivation
//!
//! Safe Rust offers limited support for placement initialization, especially for heap
//! memory. The effect of this is a lot of unnecessary copying, which is unacceptable in
//! performance‑critical code.
//! `serde` inherits these limitations since it neither attempts to initialize in‑place
//! nor exposes APIs to do so. `wincode` addresses this by providing schemas that support direct,
//! in‑place reads and writes for common patterns like byte buffers and POD types.
//!
//! # Adapting foreign types
//!
//! Another motivating feature of `wincode` is the ability to implement serialization/deserialization
//! on foreign types, where serialization/deserialization schemes on those types are unoptimized (and
//! out of your control as a foreign type). For example, suppose the following struct,
//! defined outside of your crate:
//! ```
//! use serde::{Serialize, Deserialize};
//!
//! #[derive(Serialize, Deserialize)]
//! pub struct A {
//!     pub data: Vec<u8>,
//!     pub address: [u8; 32],
//! }
//! ```
//!
//! `serde`'s default, naive, implementation will perform per-element visitation of all bytes
//! in `Vec<u8>` and `[u8; 32]`. Because these fields are "plain old data", ideally we would
//! avoid per-element visitation entirely and read / write these fields in a single pass.
//! The situation worsens if this struct needs to be written into a heap allocated data structure,
//! like a `Vec<A>` or `Box<[A]>`. Due to lack of placement initialization of heap memory, all
//! those bytes will be put on the stack before being copied into the heap allocation.
//!
//! `wincode` can solve this with the following:
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{Serialize as _, Deserialize as _, containers::{self, Pod}};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # use serde::{Serialize, Deserialize};
//! # #[derive(Debug, PartialEq, Eq)]
//! // Defined in some foreign crate...
//! #[derive(Serialize, Deserialize)]
//! pub struct A {
//!     pub data: Vec<u8>,
//!     pub address: [u8; 32],
//! }
//!
//! #[derive(SchemaWrite, SchemaRead)]
//! #[wincode(from = "A")]
//! pub struct MyA {
//!     data: containers::Vec<Pod<u8>>,
//!     address: Pod<[u8; 32]>,
//! }
//!
//! let val = A {
//!     data: vec![1, 2, 3],
//!     address: [0; 32],
//! };
//! let bincode_serialize = bincode::serialize(&val).unwrap();
//! let wincode_serialize = MyA::serialize(&val).unwrap();
//! assert_eq!(bincode_serialize, wincode_serialize);
//!
//! let bincode_deserialize: A = bincode::deserialize(&bincode_serialize).unwrap();
//! let wincode_deserialize = MyA::deserialize(&bincode_serialize).unwrap();
//! assert_eq!(val, bincode_deserialize);
//! assert_eq!(val, wincode_deserialize);
//! # }
//! ```
//!
//! Now, when deserializing `A`:
//! - All initialization is done in-place, including heap-allocated memory
//!   (true of all supported heap-allocated structures in `wincode`).
//! - Byte fields are written in a single pass by leveraging the
//!   [`Pod`](containers::Pod) in the [`containers`] module.
//! - No intermediate staging buffers: bytes are copied directly into the final
//!   destination allocation during deserialization and written directly into the
//!   output buffer during serialization.
//!
//! # Compatibility
//!
//! - Produces the same bytes as `bincode` for the covered shapes when using bincode's
//!   default configuration, provided your [`SchemaWrite`] and [`SchemaRead`] schemas and
//!   [`containers`] match the layout implied by your `serde` types.
//! - Length encodings are pluggable via [`SeqLen`](len::SeqLen).
//!
//! # Derive attributes
//!
//! ## Top level
//! |Attribute|Type|Default|Description
//! |---|---|---|---|
//! |`from`|`Type`|`None`|Indicates that type is a mapping from another type (example in previous section)|
//! |`no_suppress_unused`|`bool`|`false`|Disable unused field lints suppression. Only usable on structs with `from`.|
//! |`struct_extensions`|`bool`|`false`|Generates placement initialization helpers on `SchemaRead` struct implementations|
//!
//! ### `no_suppress_unused`
//!
//! When creating a mapping type with `#[wincode(from = "AnotherType")]`, fields are typically
//! comprised of [`containers`] (of course not strictly always true). As a result, these structs
//! purely exist for the compiler to generate optimized implementations, and are never actually
//! constructed. As a result, unused field lints will be triggered, which can be annoying.
//! By default, when `from` is used, the derive macro will generate dummy function that references all
//! the struct fields, which suppresses those lints. This function will ultimately be compiled out of your
//! build, but you can disable this by setting `no_suppress_unused` to `true`. You can also avoid
//! these lint errors with visibility modifiers (e.g., `pub`).
//!
//! Note that this only works on structs, as it is not possible to construct an arbitrary enum variant.
//!
//! ### `struct_extensions`
//!
//! You may have some exotic serialization logic that requires you to implement `SchemaRead` manually
//! for a type. In these scenarios, you'll likely want to leverage some additional helper methods
//! to reduce the amount of boilerplate that is typically required when dealing with uninitialized
//! fields.
//!
//! For example:
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{SchemaRead, SchemaWrite, io::Reader, error::ReadResult};
//! # use serde::{Serialize, Deserialize};
//! # use core::mem::MaybeUninit;
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaRead, SchemaWrite)]
//! #[wincode(struct_extensions)]
//! struct Header {
//!     num_required_signatures: u8,
//!     num_signed_accounts: u8,
//!     num_unsigned_accounts: u8,
//! }
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaRead, SchemaWrite)]
//! #[wincode(struct_extensions)]
//! struct Payload {
//!     header: Header,
//!     data: Vec<u8>,
//! }
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaWrite)]
//! struct Message {
//!     payload: Payload,
//! }
//!
//! // Assume for some reason we have to manually implement `SchemaRead` for `Message`.
//! impl SchemaRead<'_> for Message {
//!     type Dst = Message;
//!
//!     fn read(reader: &mut Reader, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
//!         // We have to do a big ugly cast like this to get a mutable MaybeUninit<Payload>.
//!         let mut payload = unsafe {
//!             &mut *(&raw mut (*dst.as_mut_ptr()).payload).cast::<MaybeUninit<Payload>>()
//!         };
//!         // `Payload::uninit_header_mut` is generated by `#[wincode(struct_extensions)]`.
//!         // This avoids having to do a big ugly cast like we had to do for payload above.
//!         //
//!         // Project a mutable `MaybeUninit<Header>` from the `MaybeUninit<Payload>`.
//!         let header = Payload::uninit_header_mut(payload);
//!         // Similarly, `Header::read_num_required_signatures` is generated
//!         // by `#[wincode(struct_extensions)]`.
//!         //
//!         // Read directly into the projected MaybeUninit<Header> slot.
//!         Header::read_num_required_signatures(reader, header)?;
//!         // ...
//!         Header::read_num_signed_accounts(reader, header)?;
//!         Header::read_num_unsigned_accounts(reader, header)?;
//!         // Alternatively, we could have done `Payload::read_header(reader, payload)?;`
//!         // rather than reading all the fields individually.
//!         Payload::read_data(reader, payload)?;
//!         Ok(())
//!     }
//! }
//!
//! let msg = Message {
//!     payload: Payload {
//!         header: Header {
//!             num_required_signatures: 1,
//!             num_signed_accounts: 2,
//!             num_unsigned_accounts: 3
//!         },
//!         data: vec![4, 5, 6, 7, 8, 9]
//!     }
//! };
//! let serialized = wincode::serialize(&msg).unwrap();
//! let deserialized = wincode::deserialize(&serialized).unwrap();
//! assert_eq!(msg, deserialized);
//! # }
//! ```
//!
//! `#[wincode(struct_extensions)]` generates three methods per field:
//! - `uninit_<field_name>_mut`
//!   - Gets a mutable `MaybeUninit` projection to the `<field_name>` slot.
//! - `read_<field_name>`
//!   - Reads into a `MaybeUninit`'s `<field_name>` slot from the given [`Reader`](io::Reader).
//! - `write_uninit_<field_name>`
//!   - Writes a `MaybeUninit`'s `<field_name>` slot with the given value.
//!
//!
//! ## Field level
//! |Attribute|Type|Default|Description
//! |---|---|---|---|
//! |`with`|`Type`|`None`|Overrides the default `SchemaRead` or `SchemaWrite` implementation for the field.|
//!
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(feature = "alloc")]
extern crate alloc;

pub mod error;
pub use error::{Error, ReadError, ReadResult, Result, WriteError, WriteResult};
pub mod io;
pub mod len;
mod schema;
pub use schema::*;
mod serde;
pub use serde::*;
#[cfg(test)]
mod proptest_config;
mod util;
#[cfg(feature = "derive")]
pub use wincode_derive::*;
// Include tuple impls.
include!(concat!(env!("OUT_DIR"), "/tuples.rs"));
