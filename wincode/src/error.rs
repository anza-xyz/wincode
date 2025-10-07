//! Error types and helpers.
use {core::str::Utf8Error, thiserror::Error};

#[derive(Error, Debug)]
pub enum Error {
    #[error("Attempting to read {0} bytes")]
    ReadSizeLimit(usize),
    #[error("Attempting to write {0} bytes")]
    WriteSizeLimit(usize),
    #[error(
        "Encoded sequence length exceeded preallocation limit of {limit} bytes (needed {needed} \
         bytes)"
    )]
    PreallocationSizeLimit { needed: usize, limit: usize },
    #[error("Encoded sequence length would overflow {0}")]
    SizeHintOverflow(&'static str),
    #[error("Could not cast integer type to pointer sized type")]
    PointerSizedDecodeError,
    #[error("Invalid bool encoding: {0}")]
    InvalidBoolEncoding(u8),
    #[error("Invalid tag encoding: {0}")]
    InvalidTagEncoding(usize),
    #[error("Writer has trailing bytes: {0}")]
    WriterTrailingBytes(usize),
    #[error(transparent)]
    InvalidUtf8Encoding(#[from] Utf8Error),
    #[error("Computing size of type would overflow usize::MAX")]
    SizeOfOverflow,
    #[error("Buffer length would overflow usize::MAX (needed {0})")]
    BufferLengthOverflow(usize),
    #[error("Invalid char lead: {0}")]
    InvalidCharLead(u8),
}

pub type Result<T> = core::result::Result<T, Error>;

#[cold]
pub const fn read_size_limit(len: usize) -> Error {
    Error::ReadSizeLimit(len)
}

#[cold]
pub const fn write_size_limit(len: usize) -> Error {
    Error::WriteSizeLimit(len)
}

#[cold]
pub const fn preallocation_size_limit(needed: usize, limit: usize) -> Error {
    Error::PreallocationSizeLimit { needed, limit }
}

#[cold]
pub const fn size_hint_overflow(max_length: &'static str) -> Error {
    Error::SizeHintOverflow(max_length)
}

#[cold]
pub const fn pointer_sized_decode_error() -> Error {
    Error::PointerSizedDecodeError
}

#[cold]
pub const fn invalid_bool_encoding(byte: u8) -> Error {
    Error::InvalidBoolEncoding(byte)
}

#[cold]
pub const fn invalid_tag_encoding(tag: usize) -> Error {
    Error::InvalidTagEncoding(tag)
}

#[cold]
pub const fn writer_trailing_bytes(bytes: usize) -> Error {
    Error::WriterTrailingBytes(bytes)
}

#[cold]
pub const fn invalid_utf8_encoding(error: Utf8Error) -> Error {
    Error::InvalidUtf8Encoding(error)
}

#[cold]
pub const fn size_of_overflow() -> Error {
    Error::SizeOfOverflow
}

#[cold]
pub const fn buffer_length_overflow(len: usize) -> Error {
    Error::BufferLengthOverflow(len)
}

#[cold]
pub const fn invalid_char_lead(val: u8) -> Error {
    Error::InvalidCharLead(val)
}
