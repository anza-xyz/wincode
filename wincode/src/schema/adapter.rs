//! Schema adapters that serialize a type by converting it to and from the value
//! of an intermediate "wire" schema.

use {
    crate::{
        TypeMeta,
        config::ConfigCore,
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
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
/// # use wincode::FromInto;
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

#[cfg(all(test, feature = "derive"))]
mod tests {
    use crate::{FromInto, SchemaRead, SchemaWrite, deserialize, serialize};

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
    #[cfg(feature = "alloc")]
    #[test]
    fn adapter_wire() {
        use {
            crate::{containers, len::UseIntLen},
            alloc::{string::String, vec::Vec},
        };

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
}
