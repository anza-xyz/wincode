//! Schema adapters that serialize a type by converting it to and from the value
//! of an intermediate "wire" schema.

#[cfg(feature = "alloc")]
use crate::len::SeqLen;
use {
    crate::{
        TypeMeta,
        config::ConfigCore,
        error::{ReadError, ReadResult, WriteResult},
        io::{ReadError as IoReadError, Reader, Writer},
        schema::{SchemaRead, SchemaWrite},
    },
    core::{marker::PhantomData, mem::MaybeUninit},
};

/// Serialize a `Target` by going through an intermediate wire representation
/// using the standard library [`From`]/[`Into`] conversions.
///
/// `Wire` is a *schema* (any `SchemaWrite`/`SchemaRead` implementor), and the
/// intermediate value is the type that schema serializes — its
/// [`SchemaWrite::Src`] on write and [`SchemaRead::Dst`] on read. On write the
/// `Target` is converted into that value (via `From<&Target>`) and serialized
/// with `Wire`; on read the value is deserialized with `Wire` and converted back
/// into the `Target` (via `Target: From<…>`).
///
/// Because `Wire` is a schema rather than the value itself, the wire side may be:
/// - a self-describing type, where the value is the type itself — e.g. `i64`, or
///   any type deriving [`SchemaWrite`](wincode_derive::SchemaWrite) /
///   [`SchemaRead`](wincode_derive::SchemaRead);
/// - a schema adapter over some other value — e.g.
///   [`containers::Vec<u8, UseIntLen<u16>>`](crate::containers::Vec), whose value
///   is `Vec<u8>`.
///
/// The `Target` is the type of the annotated field. Use the `_` inference token
/// to have it filled in automatically from the field type:
///
/// ```
/// # #[cfg(feature = "derive")] {
/// # use wincode::adapter::FromInto;
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// // Our in-memory type with a layout we don't want to serialize directly.
/// #[derive(Debug, PartialEq, Clone, Copy)]
/// struct Celsius(f64);
///
/// // The on-the-wire representation: hundredths of a degree as an integer.
/// impl From<&Celsius> for i64 {
///     fn from(c: &Celsius) -> i64 {
///         (c.0 * 100.0) as i64
///     }
/// }
/// impl From<i64> for Celsius {
///     fn from(raw: i64) -> Celsius {
///         Celsius(raw as f64 / 100.0)
///     }
/// }
///
/// #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
/// struct Reading {
///     #[wincode(with = "FromInto<i64, _>")]
///     temp: Celsius,
/// }
///
/// let reading = Reading { temp: Celsius(21.5) };
/// let bytes = wincode::serialize(&reading).unwrap();
/// assert_eq!(reading, wincode::deserialize(&bytes).unwrap());
/// # }
/// ```
pub struct FromInto<Wire, Target>(PhantomData<Wire>, PhantomData<Target>);

unsafe impl<C, Wire, Target> SchemaWrite<C> for FromInto<Wire, Target>
where
    C: ConfigCore,
    Wire: SchemaWrite<C>,
    Wire::Src: Sized + for<'a> From<&'a Target>,
{
    type Src = Target;

    // The serialized form is exactly the wire value's, so the size is forwarded.
    // The conversion means the `Target`'s in-memory representation does not match
    // the serialized form, so `zero_copy` is cleared.
    const TYPE_META: TypeMeta = <Wire as SchemaWrite<C>>::TYPE_META.keep_zero_copy(false);

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        if let TypeMeta::Static { size, .. } = <Self as SchemaWrite<C>>::TYPE_META {
            return Ok(size);
        }
        let wire: Wire::Src = src.into();
        <Wire as SchemaWrite<C>>::size_of(&wire)
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        let wire: Wire::Src = src.into();
        <Wire as SchemaWrite<C>>::write(writer, &wire)
    }
}

unsafe impl<'de, C, Wire, Target> SchemaRead<'de, C> for FromInto<Wire, Target>
where
    C: ConfigCore,
    Wire: SchemaRead<'de, C>,
    Target: From<Wire::Dst>,
{
    type Dst = Target;

    const TYPE_META: TypeMeta = <Wire as SchemaRead<'de, C>>::TYPE_META.keep_zero_copy(false);

    #[inline]
    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let wire = <Wire as SchemaRead<'de, C>>::get(reader)?;
        dst.write(Target::from(wire));
        Ok(())
    }
}

/// Deserializes using the wire schema `T` normally, but yields
/// `T::Dst::default()` when the reader is exhausted (hits EOF) instead of
/// erroring.
///
/// The purpose is backward compatibility when new fields are appended to the
/// tail of a persisted struct: older, shorter encodings that predate those
/// fields still decode, with the missing trailing fields filled from their
/// [`Default`] value. Reading a full encoding is unaffected.
///
/// Writing is unchanged — the value is serialized exactly as `T` would,
/// producing bytes that decode identically with or without this adapter. Only
/// the read path differs, so this is purely a decode-time compatibility shim.
///
/// Apply it via the `with` attribute on the (necessarily trailing) fields it
/// covers, naming the field's own schema as `T`:
///
/// ```
/// # #[cfg(feature = "derive")] {
/// # use wincode::adapter::DefaultOnEmptyRead;
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
/// struct Record {
///     id: u32,
///     // Appended in a later version; older encodings omit it entirely.
///     #[wincode(with = "DefaultOnEmptyRead<u64>")]
///     added_later: u64,
/// }
///
/// // A full encoding round-trips as usual.
/// let record = Record { id: 7, added_later: 42 };
/// let bytes = wincode::serialize(&record).unwrap();
/// assert_eq!(record, wincode::deserialize(&bytes).unwrap());
///
/// // An older encoding that predates `added_later` decodes to its default.
/// let legacy = wincode::serialize(&7u32).unwrap();
/// let decoded: Record = wincode::deserialize(&legacy).unwrap();
/// assert_eq!(decoded, Record { id: 7, added_later: 0 });
/// # }
/// ```
///
/// # Warning
///
/// The fallback is driven purely by running out of bytes, so it is only sound
/// where "no more bytes" unambiguously means "this optional tail is absent":
///
/// - **Do not use it on sequence elements.** When more items follow, a missing
///   field does not produce EOF — the read simply continues into the bytes that
///   encode the *next* item. Instead of defaulting the absent field, the decoder
///   consumes the following item's data, desynchronizing the rest of the
///   sequence. The fallback only helps when the missing bytes are genuinely the
///   end of input.
/// - **Do not use it on a middle field followed by an always-present field.**
///   The fallback catches *any* size-limit error from `T`, including a
///   partially-present value, so a genuinely truncated field is masked instead
///   of reported and the fields after it are misaligned. It is only safe on a
///   trailing run of fields where every field from the first
///   `DefaultOnEmptyRead` onward is itself optional-on-EOF.
///
/// Prefer applying it to trailing fields of a **top-level struct** decoded with
/// [`deserialize_exact`](crate::deserialize_exact), where reaching EOF exactly
/// at a field boundary is well defined and the end-of-input check is
/// straightforward and cheap.
pub struct DefaultOnEmptyRead<T>(PhantomData<T>);

unsafe impl<'de, C, T> SchemaRead<'de, C> for DefaultOnEmptyRead<T>
where
    C: ConfigCore,
    T: SchemaRead<'de, C>,
    T::Dst: Default,
{
    type Dst = T::Dst;

    // TYPE_META is intentionally left at the default `Dynamic`: decoding may read
    // either 0 bytes (the EOF fallback) or `T`'s full encoding, so the decoded
    // size is not fixed and a reader must not prefetch a static size.

    #[inline]
    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        match <T as SchemaRead<'de, C>>::read(reader, dst) {
            Ok(()) => Ok(()),
            Err(ReadError::Io(IoReadError::ReadSizeLimit(_))) => {
                dst.write(Self::Dst::default());
                Ok(())
            }
            Err(e) => Err(e),
        }
    }
}

unsafe impl<C, T> SchemaWrite<C> for DefaultOnEmptyRead<T>
where
    C: ConfigCore,
    T: SchemaWrite<C>,
{
    type Src = T::Src;

    const TYPE_META: TypeMeta = <T as SchemaWrite<C>>::TYPE_META;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <T as SchemaWrite<C>>::size_of(src)
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        <T as SchemaWrite<C>>::write(writer, src)
    }
}

/// Reads a value with the `Inner` schema purely to advance the reader, then throws
/// it away and yields [`Default::default()`] instead.
///
/// `Inner` is a *schema*, its bytes are consumed exactly as `Inner` would consume them
/// — including any validation `Inner` performs — so the surrounding stream stays in sync,
/// but the decoded value is dropped and the field is filled with the [`Default`] of `Inner`'s
/// [`SchemaRead::Dst`].
///
/// It is meant for fields you don't want to persist, such as a deprecated field
/// kept only for wire compatibility. On read the encoded value is stepped over and
/// reset to its [`Default`]; on write the value held in the instance is likewise
/// ignored and `Inner`'s [`Default`] is serialized in its place. The two directions
/// agree, so `Discard` works on types deriving both
/// [`SchemaWrite`](wincode_derive::SchemaWrite) and [`SchemaRead`] — with the
/// caveat that the original value is *not* preserved across a round-trip: a
/// discarded field always reads back, and re-serializes, as the default.
///
/// For a length-prefixed sequence, prefer [`DiscardSeq`], which steps over every
/// element without allocating a backing buffer.
///
/// ```
/// # #[cfg(feature = "derive")] {
/// # use wincode::adapter::Discard;
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
/// struct Full {
///     ignored: u32,
///     kept: u16,
/// }
///
/// #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
/// struct Partial {
///     #[wincode(with = "Discard<u32>")]
///     ignored: u32,
///     kept: u16,
/// }
///
/// // On read, `ignored` is stepped over and reset to its default.
/// let bytes = wincode::serialize(&Full { ignored: 7, kept: 9 }).unwrap();
/// assert_eq!(
///     wincode::deserialize::<Partial>(&bytes).unwrap(),
///     Partial { ignored: 0, kept: 9 },
/// );
///
/// // On write, the held value of `ignored` is discarded and its default is
/// // serialized, so the output matches a `Full` whose `ignored` is `0`.
/// let out = wincode::serialize(&Partial { ignored: 7, kept: 9 }).unwrap();
/// assert_eq!(out, wincode::serialize(&Full { ignored: 0, kept: 9 }).unwrap());
/// # }
/// ```
pub struct Discard<Inner>(PhantomData<Inner>);

unsafe impl<'de, C, Inner> SchemaRead<'de, C> for Discard<Inner>
where
    C: ConfigCore,
    Inner: SchemaRead<'de, C>,
    Inner::Dst: Default,
{
    type Dst = Inner::Dst;

    // Not zero-copy: a fresh `Default` is yielded, not a view of the wire bytes.
    const TYPE_META: TypeMeta = Inner::TYPE_META.keep_zero_copy(false);

    #[inline]
    fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        // No byte-skip fast path (unlike `DiscardSeq`): a single value has no
        // per-element bounds checks to hoist, and dropping the decoded value lets
        // the optimizer elide the copy out of the reader.
        Inner::get(reader)?;
        dst.write(Default::default());
        Ok(())
    }
}

unsafe impl<C, Inner> SchemaWrite<C> for Discard<Inner>
where
    C: ConfigCore,
    Inner: SchemaWrite<C>,
    Inner::Src: Default,
{
    type Src = Inner::Src;

    // Not zero-copy: the `Default` is written, not the instance's own bytes.
    const TYPE_META: TypeMeta = Inner::TYPE_META.keep_zero_copy(false);

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        if let TypeMeta::Static { size, .. } = Inner::TYPE_META {
            return Ok(size);
        }
        Inner::size_of(&Default::default())
    }

    #[inline]
    fn write(writer: impl Writer, _src: &Self::Src) -> WriteResult<()> {
        // Ignore the provided value and match what `read` reconstructs.
        Inner::write(writer, &Default::default())
    }
}

/// Discards a length-prefixed sequence: reads the length (encoded per `Len`) and
/// steps over every element with the element schema `T`, advancing the reader
/// exactly as decoding the sequence would, yet never allocates a backing buffer and
/// always yields an empty [`Vec`].
///
/// Every wincode sequence — `Vec`, `String`, slices, sets, and maps — shares the
/// same *length prefix + elements* wire layout, so this discards **any** of them;
/// `T` only names one element's wire form:
///
/// - a `Vec<u32>`: `DiscardSeq<u32, Len>`;
/// - a `String`: `DiscardSeq<u8, Len>` (identical bytes to a `Vec<u8>`);
/// - a map such as `HashMap<K, V>` / `BTreeMap<K, V>`: `DiscardSeq<(K, V), Len>`,
///   since each entry is encoded as a `(K, V)` pair;
/// - nested sequences, with no allocation at any level:
///   `DiscardSeq<DiscardSeq<u8, L2>, L1>` for a `Vec<Vec<u8>>`.
///
/// The produced value is always an empty `Vec<T::Dst>`, and that type is
/// incidental. Deprecating a field is then just repointing it at `DiscardSeq` and
/// changing its type to the matching `Vec<…>`: the field is dead, so its concrete
/// collection type no longer matters — only that the bytes are consumed and the
/// stream stays aligned.
///
/// The length prefix is still validated against the configured preallocation
/// limit, so a hostile length errors out identically to a real read.
///
/// Like [`Discard`], the sequence held in the instance is ignored on write and an
/// empty sequence is emitted, matching what `read` reconstructs. Use the
/// configuration's default length encoding, e.g.
/// [`BincodeLen`](crate::len::BincodeLen), to match how the field was originally
/// encoded.
///
/// ```
/// # #[cfg(all(feature = "alloc", feature = "derive"))] {
/// # use wincode::{adapter::DiscardSeq, len::BincodeLen};
/// # use wincode_derive::{SchemaWrite, SchemaRead};
/// #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
/// struct Full {
///     data: Vec<u32>,
///     tag: u8,
/// }
///
/// #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
/// struct Partial {
///     #[wincode(with = "DiscardSeq<u32, BincodeLen>")]
///     data: Vec<u32>,
///     tag: u8,
/// }
///
/// // On read, `data` is stepped over and reset to an empty `Vec`.
/// let bytes = wincode::serialize(&Full { data: vec![1, 2, 3], tag: 42 }).unwrap();
/// assert_eq!(
///     wincode::deserialize::<Partial>(&bytes).unwrap(),
///     Partial { data: Vec::new(), tag: 42 },
/// );
///
/// // On write, `data` is discarded and an empty sequence is serialized, so the
/// // output matches a `Full` with empty `data`.
/// let out = wincode::serialize(&Partial { data: vec![1, 2, 3], tag: 42 }).unwrap();
/// assert_eq!(out, wincode::serialize(&Full { data: vec![], tag: 42 }).unwrap());
/// # }
/// ```
#[cfg(feature = "alloc")]
pub struct DiscardSeq<T, Len>(PhantomData<T>, PhantomData<Len>);

#[cfg(feature = "alloc")]
unsafe impl<'de, C, T, Len> SchemaRead<'de, C> for DiscardSeq<T, Len>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaRead<'de, C>,
{
    type Dst = alloc::vec::Vec<T::Dst>;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = Len::read_prealloc_check::<T::Dst>(reader.by_ref())?;
        if let TypeMeta::Static { size, .. } = T::TYPE_META {
            // Reserve the whole `len * size`-byte body up front so the per-element
            // decodes below elide their own bounds checks. `get` still validates
            // each element, so non-zero-copy types are handled correctly too.
            //
            // SAFETY: exactly `len` decodes of `size` bytes run through the trusted window
            let mut trusted = unsafe { reader.as_trusted_for_seq(len, size)? };
            for _ in 0..len {
                T::get(trusted.by_ref())?;
            }
        } else {
            for _ in 0..len {
                T::get(reader.by_ref())?;
            }
        }
        dst.write(alloc::vec::Vec::new());
        Ok(())
    }
}

#[cfg(feature = "alloc")]
unsafe impl<C, T, Len> SchemaWrite<C> for DiscardSeq<T, Len>
where
    C: ConfigCore,
    Len: SeqLen<C>,
    T: SchemaWrite<C>,
    T::Src: Sized,
{
    type Src = alloc::vec::Vec<T::Src>;

    #[inline]
    fn size_of(_src: &Self::Src) -> WriteResult<usize> {
        // An empty sequence: just the length prefix for 0.
        Len::write_bytes_needed(0)
    }

    #[inline]
    fn write(writer: impl Writer, _src: &Self::Src) -> WriteResult<()> {
        // Ignore the provided sequence; emit an empty one, matching `read`.
        Len::write(writer, 0)
    }
}

#[cfg(all(test, feature = "derive", feature = "alloc"))]
mod tests {
    use {
        crate::{
            SchemaRead, SchemaWrite,
            adapter::{DefaultOnEmptyRead, Discard, DiscardSeq, FromInto},
            deserialize,
            len::BincodeLen,
            serialize,
        },
        alloc::{collections::BTreeMap, string::String, vec::Vec},
    };

    /// A self-describing wire schema: the wire value is a plain `u32`.
    #[test]
    fn scalar_wire() {
        #[derive(Debug, PartialEq, Clone, Copy)]
        struct Id(u32);

        impl From<&Id> for u32 {
            fn from(id: &Id) -> u32 {
                id.0
            }
        }
        impl From<u32> for Id {
            fn from(raw: u32) -> Id {
                Id(raw)
            }
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Msg {
            #[wincode(with = "FromInto<u32, _>")]
            id: Id,
        }

        let msg = Msg {
            id: Id(0xdead_beef),
        };
        let bytes = serialize(&msg).unwrap();
        // Serialized form is identical to a bare `u32`.
        assert_eq!(bytes, serialize(&0xdead_beef_u32).unwrap());
        assert_eq!(msg, deserialize(&bytes).unwrap());
    }

    /// `Wire` is a schema *adapter* whose value type differs from itself:
    /// `containers::Vec<u8, _>` serializes a `Vec<u8>`.
    #[test]
    fn adapter_wire() {
        use crate::{containers, len::UseIntLen};

        #[derive(Debug, PartialEq, Clone)]
        struct Name(String);

        impl From<&Name> for Vec<u8> {
            fn from(name: &Name) -> Vec<u8> {
                name.0.as_bytes().to_vec()
            }
        }
        impl From<Vec<u8>> for Name {
            fn from(bytes: Vec<u8>) -> Name {
                Name(String::from_utf8(bytes).unwrap())
            }
        }

        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Msg {
            #[wincode(with = "FromInto<containers::Vec<u8, UseIntLen<u16>>, _>")]
            name: Name,
        }

        let msg = Msg {
            name: Name("wincode".into()),
        };
        let bytes = serialize(&msg).unwrap();
        // u16 length prefix + the raw bytes.
        assert_eq!(bytes.len(), 2 + "wincode".len());
        assert_eq!(msg, deserialize(&bytes).unwrap());
    }

    #[test]
    fn default_on_empty_read() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Record {
            id: u32,
            #[wincode(with = "DefaultOnEmptyRead<u64>")]
            added_later: u64,
        }

        // Full encoding round-trips unchanged, and writing is identical to a
        // plain `u32` + `u64`.
        let record = Record {
            id: 7,
            added_later: 42,
        };
        let bytes = serialize(&record).unwrap();
        assert_eq!(bytes.len(), 4 + 8);
        assert_eq!(record, deserialize(&bytes).unwrap());

        // A legacy encoding that stops after `id` decodes `added_later` to its
        // default rather than erroring on EOF.
        let legacy = serialize(&7u32).unwrap();
        assert_eq!(
            deserialize::<Record>(&legacy).unwrap(),
            Record {
                id: 7,
                added_later: 0,
            }
        );

        // The fallback triggers on any `ReadSizeLimit`, so a *partially* present
        // inner value (not just a clean field boundary) also decodes to the
        // default. This is partly deliberate and partly a consequence of the
        // reader interface: readers do not expose how many bytes remain, and
        // probing that is neither efficient nor guaranteed to work across all
        // reader implementations, so we cannot distinguish a clean boundary from
        // a truncated field. Here 4 bytes cover `id` and the stray tail is too
        // short for the `u64`.
        let truncated = [0u8; 6];
        assert_eq!(
            deserialize::<Record>(&truncated).unwrap(),
            Record {
                id: 0,
                added_later: 0,
            }
        );
    }

    #[test]
    fn discard_seq_nested() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Full {
            pairs: Vec<(u32, u16)>,
            singles: Vec<u32>,
            nested: Vec<Vec<u8>>,
            map: BTreeMap<u32, u64>,
            tag: u8,
        }

        #[derive(SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Partial {
            // Composite static element via the trusted-window path.
            #[wincode(with = "DiscardSeq<(u32, u16), BincodeLen>")]
            pairs: Vec<(u32, u16)>,
            // `Discard` composed as the element schema.
            #[wincode(with = "DiscardSeq<Discard<u32>, BincodeLen>")]
            singles: Vec<u32>,
            // Nested `DiscardSeq`: discards `Vec<Vec<u8>>` with no allocation at
            // any level while still yielding `Vec<Vec<u8>>`.
            #[wincode(with = "DiscardSeq<DiscardSeq<u8, BincodeLen>, BincodeLen>")]
            nested: Vec<Vec<u8>>,
            // A map is a sequence of `(K, V)` entries; the field type is now an
            // incidental `Vec`.
            #[wincode(with = "DiscardSeq<(u32, u64), BincodeLen>")]
            map: Vec<(u32, u64)>,
            tag: u8,
        }

        let bytes = serialize(&Full {
            pairs: vec![(1, 2), (3, 4)],
            singles: vec![10, 20, 30],
            nested: vec![vec![1, 2], vec![], vec![9]],
            map: BTreeMap::from([(1, 10), (2, 20), (3, 30)]),
            tag: 7,
        })
        .unwrap();
        assert_eq!(
            deserialize::<Partial>(&bytes).unwrap(),
            Partial {
                pairs: Vec::new(),
                singles: Vec::new(),
                nested: Vec::new(),
                map: Vec::new(),
                tag: 7,
            },
        );
    }

    #[test]
    fn discard_seq_validates_non_zero_copy_elements() {
        #[derive(SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Partial {
            #[wincode(with = "DiscardSeq<bool, BincodeLen>")]
            flags: Vec<bool>,
        }

        let ok = serialize(&vec![true, false]).unwrap();
        assert_eq!(
            deserialize::<Partial>(&ok).unwrap(),
            Partial { flags: Vec::new() },
        );

        // A non-canonical bool byte must still be rejected, not skipped.
        let mut bad = ok.clone();
        *bad.last_mut().unwrap() = 2;
        assert!(deserialize::<Partial>(&bad).is_err());
    }

    #[test]
    fn discard_string_as_bytes() {
        #[derive(SchemaWrite, SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Full {
            text: String,
            tag: u8,
        }

        // A `String` shares its wire format with `Vec<u8>`, so it is discarded as
        // raw bytes via `DiscardSeq<u8>`: no allocation, and the following field
        // stays aligned.
        #[derive(SchemaRead, Debug, PartialEq)]
        #[wincode(internal)]
        struct Partial {
            #[wincode(with = "DiscardSeq<u8, BincodeLen>")]
            text: Vec<u8>,
            tag: u8,
        }

        let bytes = serialize(&Full {
            text: "hello".into(),
            tag: 7,
        })
        .unwrap();
        assert_eq!(
            deserialize::<Partial>(&bytes).unwrap(),
            Partial {
                text: Vec::new(),
                tag: 7,
            },
        );
    }
}
