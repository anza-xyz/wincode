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
//! # Zero copy deserialization
//!
//! `wincode` supports zero copy deserialization of contiguous byte slices
//! (serialized with `Vec<u8>`, `Box<[u8]>`, `[u8; N]`, etc.).
//!
//! ```
//! # #[cfg(feature = "derive")] {
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
//! let deserialized = wincode::deserialize(&serialized).unwrap();
//! assert_eq!(byte_ref, deserialized);
//! # }  
//! ```
//! # Derive attributes
//!
//! ## Top level
//! |Attribute|Type|Default|Description
//! |---|---|---|---|
//! |`from`|`Type`|`None`|Indicates that type is a mapping from another type (example in previous section)|
//! |`no_suppress_unused`|`bool`|`false`|Disable unused field lints suppression. Only usable on structs with `from`.|
//! |`struct_extensions`|`bool`|`false`|Generates placement initialization helpers on `SchemaRead` struct implementations|
//! |`tag_encoding`|`Type`|`None`|Specifies the encoding/decoding schema to use for the variant discriminant. Only usable on enums.|
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
//! ### `tag_encoding`
//!
//! Allows specifying the encoding/decoding schema to use for the variant discriminant. Only usable on enums.
//!
//! <div class="warning">
//! There is no bincode analog to this attribute.
//! Specifying this attribute will make your enum incompatible with bincode's default enum encoding.
//! If you need strict bincode compatibility, you should implement a custom <code>Deserialize</code> and
//! <code>Serialize</code> impl for your enum on the serde / bincode side.
//! </div>
//!
//! Example:
//! ```
//! # #[cfg(all(feature = "derive", feature = "alloc"))] {
//! use wincode::{SchemaWrite, SchemaRead};
//!
//! # #[derive(Debug, PartialEq, Eq)]
//! #[derive(SchemaWrite, SchemaRead)]
//! #[wincode(tag_encoding = "u8")]
//! enum Enum {
//!     A,
//!     B,
//!     C,
//! }
//!
//! assert_eq!(&wincode::serialize(&Enum::B).unwrap(), &1u8.to_le_bytes());
//! # }
//! ```
//!
//! ### `struct_extensions`
//!
//! You may have some exotic serialization logic that requires you to implement `SchemaRead` manually
//! for a type. In these scenarios, you'll likely want to leverage some additional helper methods
//! to reduce the amount of boilerplate that is typically required when dealing with uninitialized
//! fields.
//!
//! `#[wincode(struct_extensions)]` generates a corresponding uninit builder struct for the type.
//! The name of the builder struct is the name of the type with `UninitBuilder` appended.
//! E.g., `Header` -> `HeaderUninitBuilder`.
//!
//! The builder has automatic initialization tracking that does bookkeeping of which fields have been initialized.
//! Calling `write_<field_name>` or `read_<field_name>`, for example, will mark the field as
//! initialized so that it's properly dropped if the builder is dropped on error or panic.
//!
//! The builder struct has the following methods:
//! - `from_maybe_uninit_mut`
//!   - Creates a new builder from a mutable `MaybeUninit` reference to the type.
//! - `into_assume_init_mut`
//!   - Assumes the builder is fully initialized, drops it, and returns a mutable reference to the inner type.
//! - `assume_init_forget`
//!   - Forgets the builder, disabling the drop logic.
//! - `is_init`
//!   - Checks if the builder is fully initialized by checking if all field initialization bits are set.
//!
//! For each field, the builder struct provides the following methods:
//! - `uninit_<field_name>_mut`
//!   - Gets a mutable `MaybeUninit` projection to the `<field_name>` slot.
//! - `read_<field_name>`
//!   - Reads into a `MaybeUninit`'s `<field_name>` slot from the given [`Reader`](io::Reader).
//! - `write_<field_name>`
//!   - Writes a `MaybeUninit`'s `<field_name>` slot with the given value.
//! - `init_<field_name>_with`
//!   - Initializes the `<field_name>` slot with a given initializer function.
//! - `assume_init_<field_name>`
//!   - Marks the `<field_name>` slot as initialized.
//!
//! #### Safety
//!
//! Correct code will call `assume_init_forget` or `assume_init_mut` once all fields have been initialized.
//! Failing to do so will result in the initialized fields being dropped when the builder is dropped, which
//! is undefined behavior if the `MaybeUninit` is later assumed to be initialized (e.g., on successful deserialization).
//!
//! #### Example
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
//!         // Normally we have to do a big ugly cast like this
//!         // to get a mutable `MaybeUninit<Payload>`.
//!         let payload = unsafe {
//!             &mut *(&raw mut (*dst.as_mut_ptr()).payload).cast::<MaybeUninit<Payload>>()
//!         };
//!         // Note that the order matters here. Values are dropped in reverse
//!         // declaration order, and we need to ensure `header_builder` is dropped
//!         // before `payload_builder` in the event of an error or panic.
//!         let mut payload_builder = PayloadUninitBuilder::from_maybe_uninit_mut(payload);
//!         unsafe {
//!             // payload.header will be marked as initialized if the function succeeds.
//!             payload_builder.init_header_with(|header| {
//!                 // Read directly into the projected MaybeUninit<Header> slot.
//!                 let mut header_builder = HeaderUninitBuilder::from_maybe_uninit_mut(header);
//!                 header_builder.read_num_required_signatures(reader)?;
//!                 header_builder.read_num_signed_accounts(reader)?;
//!                 header_builder.read_num_unsigned_accounts(reader)?;
//!                 unsafe { header_builder.assume_init_forget() };
//!                 Ok(())
//!             })?;
//!         }
//!         // Alternatively, we could have done `payload_builder.read_header(reader)?;`
//!         // rather than reading all the fields individually.
//!         payload_builder.read_data(reader)?;
//!         // Message is fully initialized, so we forget the builders
//!         // to avoid dropping the initialized fields.
//!         unsafe { payload_builder.assume_init_forget() };
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
//! ## Field level
//! |Attribute|Type|Default|Description
//! |---|---|---|---|
//! |`with`|`Type`|`None`|Overrides the default `SchemaRead` or `SchemaWrite` implementation for the field.|
//!
//! ## Variant level (enum variants)
//! |Attribute|Type|Default|Description
//! |---|---|---|---|
//! |`tag`|`Expr`|`None`|Specifies the discriminant expression for the variant. Only usable on enums.|
//!
//! ### `tag`
//!
//! Specifies the discriminant expression for the variant. Only usable on enums.
//!
//! <div class="warning">
//! There is no bincode analog to this attribute.
//! Specifying this attribute will make your enum incompatible with bincode's default enum encoding.
//! If you need strict bincode compatibility, you should implement a custom <code>Deserialize</code> and
//! <code>Serialize</code> impl for your enum on the serde / bincode side.
//! </div>
//!
//! Example:
//! ```
//! # #[cfg(all(feature = "derive", feature = "alloc"))] {
//! use wincode::{SchemaWrite, SchemaRead};
//!
//! #[derive(SchemaWrite, SchemaRead)]
//! enum Enum {
//!     #[wincode(tag = 5)]
//!     A,
//!     #[wincode(tag = 8)]
//!     B,
//!     #[wincode(tag = 13)]
//!     C,
//! }
//!
//! assert_eq!(&wincode::serialize(&Enum::A).unwrap(), &5u32.to_le_bytes());
//! # }
//! ```
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
#[cfg(feature = "derive")]
pub use wincode_derive::*;
// Include tuple impls.
include!(concat!(env!("OUT_DIR"), "/tuples.rs"));
