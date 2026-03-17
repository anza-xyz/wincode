use {
    crate::{
        ReadResult, SchemaRead, SchemaWrite, WriteResult,
        config::Config,
        error::invalid_utf8_encoding,
        io::{ReadError as IoReadError, Reader, Writer},
        len::SeqLen,
    },
    alloc::vec::Vec,
    core::{mem::MaybeUninit, str},
    ecow::EcoString,
};

unsafe impl<C: Config> SchemaWrite<C> for EcoString {
    type Src = Self;

    #[inline]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        <str as SchemaWrite<C>>::size_of(src.as_str())
    }

    #[inline]
    fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        C::LengthEncoding::prealloc_check::<u8>(src.len())?;
        <str as SchemaWrite<C>>::write(writer, src.as_str())
    }
}

unsafe impl<'de, C: Config> SchemaRead<'de, C> for EcoString {
    type Dst = Self;

    #[inline]
    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let len = C::LengthEncoding::read_prealloc_check::<u8>(reader.by_ref())?;

        match reader.take_scoped(len) {
            Ok(bytes) => match str::from_utf8(bytes) {
                Ok(s) => {
                    dst.write(EcoString::from(s));
                    Ok(())
                }
                Err(err) => Err(invalid_utf8_encoding(err)),
            },
            Err(IoReadError::UnsupportedZeroCopy) => {
                if len <= EcoString::INLINE_LIMIT {
                    let mut buf = [MaybeUninit::uninit(); EcoString::INLINE_LIMIT];
                    reader.copy_into_slice(&mut buf[..len])?;
                    // SAFETY: `copy_into_slice` initialized the first `len` bytes of `buf`.
                    let bytes =
                        unsafe { core::slice::from_raw_parts(buf.as_ptr().cast::<u8>(), len) };
                    let string = str::from_utf8(bytes).map_err(invalid_utf8_encoding)?;
                    dst.write(EcoString::from(string));
                    Ok(())
                } else {
                    let mut bytes = Vec::with_capacity(len);
                    reader.copy_into_slice(bytes.spare_capacity_mut())?;
                    // SAFETY: `copy_into_slice` fills the entire spare-capacity slice.
                    unsafe { bytes.set_len(len) };
                    let string = str::from_utf8(&bytes).map_err(invalid_utf8_encoding)?;
                    let mut eco = EcoString::with_capacity(string.len());
                    eco.push_str(string);
                    dst.write(eco);
                    Ok(())
                }
            }
            Err(err) => Err(err.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{
            deserialize,
            io::{ReadError as IoReadError, Reader},
            proptest_config::proptest_cfg,
            serialize,
        },
        proptest::prelude::*,
    };

    struct NoScopedReader<'a> {
        inner: &'a [u8],
    }

    impl<'a> NoScopedReader<'a> {
        fn new(inner: &'a [u8]) -> Self {
            Self { inner }
        }
    }

    impl<'a> Reader<'a> for NoScopedReader<'a> {
        type Trusted<'b>
            = Self
        where
            Self: 'b;

        fn fill_buf(&mut self, n_bytes: usize) -> crate::io::ReadResult<&[u8]> {
            Ok(&self.inner[..n_bytes.min(self.inner.len())])
        }

        fn fill_exact(&mut self, n_bytes: usize) -> crate::io::ReadResult<&[u8]> {
            let Some(src) = self.inner.get(..n_bytes) else {
                return Err(crate::io::read_size_limit(n_bytes));
            };
            Ok(src)
        }

        fn copy_into_slice(
            &mut self,
            dst: &mut [core::mem::MaybeUninit<u8>],
        ) -> crate::io::ReadResult<()> {
            let len = dst.len();
            let Some(src) = self.inner.get(..len) else {
                return Err(crate::io::read_size_limit(len));
            };
            // SAFETY: `dst` points to `len` writable bytes and does not overlap `src`.
            unsafe {
                core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u8>(), len)
            };
            self.inner = &self.inner[len..];
            Ok(())
        }

        fn take_array<const N: usize>(&mut self) -> crate::io::ReadResult<[u8; N]> {
            let Some((src, rest)) = self.inner.split_first_chunk() else {
                return Err(crate::io::read_size_limit(N));
            };
            self.inner = rest;
            Ok(*src)
        }

        fn take_scoped(&mut self, _len: usize) -> crate::io::ReadResult<&[u8]> {
            Err(IoReadError::UnsupportedZeroCopy)
        }

        unsafe fn consume_unchecked(&mut self, amt: usize) {
            self.inner = unsafe { self.inner.get_unchecked(amt..) };
        }

        fn consume(&mut self, amt: usize) -> crate::io::ReadResult<()> {
            if self.inner.len() < amt {
                return Err(crate::io::read_size_limit(amt));
            }
            self.inner = &self.inner[amt..];
            Ok(())
        }

        unsafe fn as_trusted_for(
            &mut self,
            n_bytes: usize,
        ) -> crate::io::ReadResult<Self::Trusted<'_>> {
            let Some((src, rest)) = self.inner.split_at_checked(n_bytes) else {
                return Err(crate::io::read_size_limit(n_bytes));
            };
            self.inner = rest;
            Ok(Self::new(src))
        }
    }

    #[test]
    fn test_small_string_roundtrip() {
        let value = EcoString::from("hello");
        let serialized = serialize(&value).unwrap();
        let deserialized = deserialize::<EcoString>(&serialized).unwrap();
        assert_eq!(deserialized, value);
    }

    #[test]
    fn test_same_encoding_as_string() {
        proptest!(proptest_cfg(), |(value: String)| {
            let eco = EcoString::from(value.as_str());
            let eco_serialized = serialize(&eco).unwrap();
            let string_serialized = serialize(&value).unwrap();
            prop_assert_eq!(&eco_serialized, &string_serialized);

            let deserialized = deserialize::<EcoString>(&eco_serialized).unwrap();
            prop_assert_eq!(deserialized, eco);
        });
    }

    #[test]
    fn test_bincode_compat() {
        proptest!(proptest_cfg(), |(value: String)| {
            let eco = EcoString::from(value.as_str());
            let bincode_serialized = bincode::serialize(&eco).unwrap();
            let wincode_serialized = serialize(&eco).unwrap();
            prop_assert_eq!(&wincode_serialized, &bincode_serialized);

            let bincode_deserialized: EcoString = bincode::deserialize(&bincode_serialized).unwrap();
            let wincode_deserialized: EcoString = deserialize(&wincode_serialized).unwrap();
            prop_assert_eq!(&wincode_deserialized, &eco);
            prop_assert_eq!(&wincode_deserialized, &bincode_deserialized);
        });
    }

    #[test]
    fn test_roundtrip_without_take_scoped_support() {
        proptest!(proptest_cfg(), |(value: String)| {
            let eco = EcoString::from(value.as_str());
            let serialized = serialize(&eco).unwrap();
            let reader = NoScopedReader::new(&serialized);
            let deserialized = <EcoString as SchemaRead<'_, crate::config::DefaultConfig>>::get(reader).unwrap();
            prop_assert_eq!(deserialized, eco);
        });
    }
}
