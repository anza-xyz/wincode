//! Error types and helpers.
use {crate::io, core::str::Utf8Error, thiserror::Error};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    WriteError(#[from] WriteError),
    #[error(transparent)]
    ReadError(#[from] ReadError),
}

#[derive(Error, Debug)]
pub enum WriteError {
    #[error(transparent)]
    Io(#[from] io::WriteError),
    #[error(transparent)]
    InvalidUtf8Encoding(#[from] Utf8Error),
    #[error("Sequence length would overflow length encoding scheme: {0}")]
    LengthEncodingOverflow(&'static str),
}

#[derive(Error, Debug)]
pub enum ReadError {
    #[error(transparent)]
    Io(#[from] io::ReadError),
    #[error(transparent)]
    InvalidUtf8Encoding(#[from] Utf8Error),
    #[error("Could not cast integer type to pointer sized type")]
    PointerSizedReadError,
    #[error(
        "Encoded sequence length exceeded preallocation limit of {limit} bytes (needed {needed} \
         bytes)"
    )]
    PreallocationSizeLimit { needed: usize, limit: usize },
    #[error("Invalid tag encoding: {0}")]
    InvalidTagEncoding(usize),
    #[error("Invalid bool encoding: {0}")]
    InvalidBoolEncoding(u8),
    #[error("Sequence length would overflow length encoding scheme: {0}")]
    LengthEncodingOverflow(&'static str),
    #[error("Invalid char lead: {0}")]
    InvalidCharLead(u8),
}

pub type Result<T> = core::result::Result<T, Error>;
pub type WriteResult<T> = core::result::Result<T, WriteError>;
pub type ReadResult<T> = core::result::Result<T, ReadError>;

#[cold]
pub const fn preallocation_size_limit(needed: usize, limit: usize) -> ReadError {
    ReadError::PreallocationSizeLimit { needed, limit }
}

#[cold]
pub const fn read_length_encoding_overflow(max_length: &'static str) -> ReadError {
    ReadError::LengthEncodingOverflow(max_length)
}

#[cold]
pub const fn write_length_encoding_overflow(max_length: &'static str) -> WriteError {
    WriteError::LengthEncodingOverflow(max_length)
}

#[cold]
pub const fn pointer_sized_decode_error() -> ReadError {
    ReadError::PointerSizedReadError
}

#[cold]
pub const fn invalid_bool_encoding(byte: u8) -> ReadError {
    ReadError::InvalidBoolEncoding(byte)
}

#[cold]
pub const fn invalid_tag_encoding(tag: usize) -> ReadError {
    ReadError::InvalidTagEncoding(tag)
}

#[cold]
pub const fn invalid_utf8_encoding(error: Utf8Error) -> ReadError {
    ReadError::InvalidUtf8Encoding(error)
}

#[cold]
pub const fn invalid_char_lead(val: u8) -> ReadError {
    ReadError::InvalidCharLead(val)
}
