//! [`SchemaRead`](crate::SchemaRead) context newtypes.

/// Length context.
///
/// Used for providing an already read or in-memory length value
/// to a type that would otherwise read it from a [`Reader`](crate::io::Reader).
///
/// # Examples
///
/// ```
/// # use wincode::{
/// #     SchemaRead, SchemaReadContext, SchemaWrite, Deserialize,
/// #     config::Config, context,
/// #     io::{Writer, Reader}, WriteResult, ReadResult,
/// # };
/// # use core::mem::MaybeUninit;
/// # #[derive(Debug, PartialEq)]
/// struct Header {
///     data_len: u8,
/// }
///
/// # #[derive(Debug, PartialEq)]
/// struct Data {
///     header: Header,
///     data: Vec<u8>,
/// }
///
/// unsafe impl<C: Config> SchemaWrite<C> for Data {
///     type Src = Self;
///
///     fn size_of(src: &Self::Src) -> WriteResult<usize> {
///         Ok(1 + src.data.len())
///     }
///
///     fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
///         writer.write(&[src.header.data_len])?;
///         writer.write(&src.data)?;
///         Ok(())
///     }
/// }
///
/// unsafe impl<'de, C: Config> SchemaRead<'de, C> for Data {
///     type Dst = Self;
///
///     fn read(
///         mut reader: impl Reader<'de>,
///         dst: &mut MaybeUninit<Self::Dst>,
///     ) -> ReadResult<()> {
///         let len = reader.take_byte()?;
///
///         let data = <Vec<u8> as SchemaReadContext<C, _>>::get_with_context(
///             context::Len(len as usize),
///             reader
///         )?;
///
///         dst.write(Self {
///             header: Header { data_len: len },
///             data,
///         });
///
///         Ok(())
///     }
/// }
///
/// let data = Data {
///     header: Header { data_len: 8},
///     data: vec![0u8; 8],
/// };
/// let bytes = wincode::serialize(&data).unwrap();
/// let deserialized = wincode::deserialize(&bytes).unwrap();
/// assert_eq!(data, deserialized);
/// ```
pub struct Len(pub usize);
