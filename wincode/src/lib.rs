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
//!     data: Vec<u8>,
//!     win: bool,
//! }
//!
//! let val = MyStruct { data: vec![1,2,3], win: true };
//! assert_eq!(wincode::serialize(&val).unwrap(), bincode::serialize(&val).unwrap());
//! # }
//! ```
//!
//! For "plain old data" (see [`Pod`](containers::Pod)) fields (POD newtypes, arrays of POD newtypes, etc),
//! use [`containers`] to leverage optimized read/write implementations.
//!
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{containers::{self, Pod}};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! # use serde::{Serialize, Deserialize};
//! # #[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
//! #[repr(transparent)]
//! #[derive(Clone, Copy)]
//! struct Address([u8; 32]);
//!
//! # #[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
//! #[repr(transparent)]
//! #[derive(Clone, Copy)]
//! struct Hash([u8; 32]);
//!
//! # #[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
//! #[derive(SchemaWrite, SchemaRead)]
//! struct MyStruct {
//!     #[wincode(with = "Pod<_>")]
//!     hash: Hash,
//!     #[wincode(with = "containers::Vec<Pod<_>>")]
//!     addresses: Vec<Address>,
//! }
//!
//! let val = MyStruct {
//!     hash: Hash([0; 32]),
//!     addresses: vec![Address([0; 32]), Address([1; 32])]
//! };
//! assert_eq!(wincode::serialize(&val).unwrap(), bincode::serialize(&val).unwrap());
//! # }
//! ```
//!
//! # Motivation
//!
//! Typical Rust API design employs a *construct-then-move* style of programming.
//! Common APIs like `Vec::push`, iterator adaptors, `Box::new` (and its `Rc`/`Arc`
//! variants), and even returning a fully-initialized struct from a function all
//! follow this pattern. While this style feels intuitive and ergonomic, it
//! inherently entails copying unless the compiler can perform elision -- which,
//! today, it generally cannot. To see why this is a consequence of the design,
//! consider the following code:
//! ```
//! # struct MyStruct;
//! # impl MyStruct {
//! #     fn new() -> Self {
//! #         MyStruct
//! #     }
//! # }
//! Box::new(MyStruct::new());
//! ```
//! `MyStruct` must be constructed *before* it can be moved into `Box`'s allocation.
//! This is a classic code ordering problem: to avoid the copy, `Box::new` needs
//! to execute code before `MyStruct::new()` runs. `Vec::push`, iterator collection,
//! and similar APIs have this same problem.
//! (See these [design meeting notes](https://hackmd.io/XXuVXH46T8StJB_y0urnYg) or
//! or the
//! [`placement-by-return` RFC](https://github.com/PoignardAzur/rust-rfcs/blob/placement-by-return/text/0000-placement-by-return.md)
//! for a more in-depth discussion on this topic.) The result of this is that even
//! performance conscious developers routinely introduce avoidable copying without
//! realizing it. `serde` inherits these issues since it neither attempts to
//! initialize in‑place nor exposes APIs to do so.
//!
//! These patterns are not inherent limitations of Rust, but are consequences of
//! conventions and APIs that do not consider in-place initialization as part of
//! their design. The tools for in-place construction *do* exist (see
//! [`MaybeUninit`](core::mem::MaybeUninit) and raw pointer APIs), but they are
//! rarely surfaced in libraries and can be cumbersome to use (see [`addr_of_mut!`](core::ptr::addr_of_mut)),
//! so programmers are often not even aware of them or avoid them.
//!
//! `wincode` makes in-place initialization a first class design goal, and fundamentally
//! operates on [traits](#traits) that facilitate direct writes of memory.
//!
//! # Adapting foreign types
//!
//! `wincode` can also be used to implement serialization/deserialization
//! on foreign types, where serialization/deserialization schemes on those types are unoptimized (and
//! out of your control as a foreign type). For example, consider the following struct,
//! defined outside of your crate:
//! ```
//! use serde::{Serialize, Deserialize};
//!
//! # #[derive(PartialEq, Eq, Debug)]
//! #[repr(transparent)]
//! #[derive(Clone, Copy, Serialize, Deserialize)]
//! struct Address([u8; 32]);
//!
//! # #[derive(PartialEq, Eq, Debug)]
//! #[repr(transparent)]
//! #[derive(Clone, Copy, Serialize, Deserialize)]
//! struct Hash([u8; 32]);
//!
//! #[derive(Serialize, Deserialize)]
//! pub struct A {
//!     pub addresses: Vec<Address>,
//!     pub hash: Hash,
//! }
//! ```
//!
//! `serde`'s default, naive, implementation will perform per-element visitation of all bytes
//! in `Vec<Address>` and `Hash`. Because these fields are "plain old data", ideally we would
//! avoid per-element visitation entirely and read / write these fields in a single pass.
//! The situation worsens if this struct needs to be written into a heap allocated data structure,
//! like a `Vec<A>` or `Box<[A]>`. As discussed in [motivation](#motivation), all
//! those bytes will be initialized on the stack before being copied into the heap allocation.
//!
//! `wincode` can solve this with the following:
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use wincode::{Serialize as _, Deserialize as _, containers::{self, Pod}};
//! # use wincode_derive::{SchemaWrite, SchemaRead};
//! mod foreign_crate {
//!     // Defined in some foreign crate...
//!     use serde::{Serialize, Deserialize};
//!
//!     # #[derive(PartialEq, Eq, Debug)]
//!     #[repr(transparent)]
//!     #[derive(Clone, Copy, Serialize, Deserialize)]
//!     pub struct Address(pub [u8; 32]);
//!
//!     # #[derive(PartialEq, Eq, Debug)]
//!     #[repr(transparent)]
//!     #[derive(Clone, Copy, Serialize, Deserialize)]
//!     pub struct Hash(pub [u8; 32]);
//!
//!     # #[derive(PartialEq, Eq, Debug)]
//!     #[derive(Serialize, Deserialize)]
//!     pub struct A {
//!         pub addresses: Vec<Address>,
//!         pub hash: Hash,
//!     }
//! }
//!
//! #[derive(SchemaWrite, SchemaRead)]
//! #[wincode(from = "foreign_crate::A")]
//! pub struct MyA {
//!     addresses: Vec<Pod<foreign_crate::Address>>,
//!     hash: Pod<foreign_crate::Hash>,
//! }
//!
//! let val = foreign_crate::A {
//!     addresses: vec![foreign_crate::Address([0; 32]), foreign_crate::Address([1; 32])],
//!     hash: foreign_crate::Hash([0; 32]),
//! };
//! let bincode_serialize = bincode::serialize(&val).unwrap();
//! let wincode_serialize = MyA::serialize(&val).unwrap();
//! assert_eq!(bincode_serialize, wincode_serialize);
//!
//! let bincode_deserialize: foreign_crate::A = bincode::deserialize(&bincode_serialize).unwrap();
//! let wincode_deserialize = MyA::deserialize(&bincode_serialize).unwrap();
//! assert_eq!(val, bincode_deserialize);
//! assert_eq!(val, wincode_deserialize);
//! # }
//! ```
//!
//! Now, when deserializing `A`:
//! - All initialization is done in-place, including heap-allocated memory
//!   (true of all supported contiguous heap-allocated structures in `wincode`).
//! - Byte fields are read and written in a single pass.
//!
//! # Compatibility
//!
//! - Produces the same bytes as `bincode` for the covered shapes when using bincode's
//!   default configuration, provided your [`SchemaWrite`] and [`SchemaRead`] schemas and
//!   [`containers`] match the layout implied by your `serde` types.
//! - Length encodings are pluggable via [`SeqLen`](len::SeqLen).
//!
//! # Zero-copy deserialization
//!
//! `wincode`'s zero-copy deserialization is built on the following primitives:
//! - [`u8`]
//! - [`i8`]
//!
//! Within `wincode`, any type that is composed entirely of these primitives is
//! eligible for zero-copy deserialization.
//!
//! Let `Z` be the set of zero-copy types.
//!
//! The following higher order types are eligible for zero-copy deserialization:
//! - `&[Z]`
//! - `&Z`
//! - `&[Z; N]`
//!
//! Structs deriving [`SchemaWrite`] and [`SchemaRead`] are eligible for zero-copy deserialization
//! as long as they are composed entirely of the above zero-copy types and are annotated with
//! `#[repr(transparent)]` or `#[repr(C)]`.
//! Note that this is **not** true for tuples, as Rust does not currently guarantee tuple layout.
//!
//! ## Examples
//!
//! ### `&[u8]`
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! use wincode::{SchemaWrite, SchemaRead};
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaWrite, SchemaRead)]
//! struct ByteRef<'a> {
//!     bytes: &'a [u8],
//! }
//!
//! let bytes: Vec<u8> = vec![1, 2, 3, 4, 5];
//! let byte_ref = ByteRef { bytes: &bytes };
//! let serialized = wincode::serialize(&byte_ref).unwrap();
//! let deserialized: ByteRef<'_> = wincode::deserialize(&serialized).unwrap();
//! assert_eq!(byte_ref, deserialized);
//! # }  
//! ```
//!
//! ### struct newtype
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! # use rand::random;
//! # use std::array;
//! use wincode::{SchemaWrite, SchemaRead};
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaWrite, SchemaRead)]
//! #[repr(transparent)]
//! struct Signature([u8; 64]);
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaWrite, SchemaRead)]
//! struct Data<'a> {
//!     signature: &'a Signature,
//!     data: &'a [u8],
//! }
//!
//! let signature = Signature(array::from_fn(|_| random()));
//! let data = Data {
//!     signature: &signature,
//!     data: &[1, 2, 3, 4, 5],
//! };
//! let serialized = wincode::serialize(&data).unwrap();
//! let deserialized: Data<'_> = wincode::deserialize(&serialized).unwrap();
//! assert_eq!(data, deserialized);
//! # }
//! ```
//!
//! ### `&[u8; N]`
//! ```
//! # #[cfg(all(feature = "alloc", feature = "derive"))] {
//! use wincode::{SchemaWrite, SchemaRead};
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaWrite, SchemaRead)]
//! struct HeaderRef<'a> {
//!     magic: &'a [u8; 7],
//! }
//!
//! let header = HeaderRef { magic: b"W1NC0D3" };
//! let serialized = wincode::serialize(&header).unwrap();
//! let deserialized: HeaderRef<'_> = wincode::deserialize(&serialized).unwrap();
//! assert_eq!(header, deserialized);
//! # }
//! ```
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
//! impl<'de> SchemaRead<'de> for Message {
//!     type Dst = Message;
//!
//!     fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
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
