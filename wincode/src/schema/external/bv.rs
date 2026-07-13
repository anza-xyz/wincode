use {
    crate::{
        ReadResult, SchemaRead, SchemaWrite, TypeMeta, WriteResult,
        config::Config,
        error::{invalid_tag_encoding, invalid_value},
        io::{Reader, Writer},
        len::SeqLen,
    },
    bv::{BitVec, Bits, BlockType},
    core::mem::MaybeUninit,
};

#[inline(always)]
fn serialized_block<Block: BlockType>(src: &BitVec<Block>, index: usize) -> Block {
    #[cfg(feature = "bv-strict")]
    {
        src.get_block(index)
    }
    #[cfg(not(feature = "bv-strict"))]
    {
        src.get_raw_block(index)
    }
}

#[cfg(feature = "bv-strict")]
#[inline]
fn expected_block_count<Block: BlockType>(bits_len: u64) -> ReadResult<usize> {
    let block_bits = Block::nbits() as u64;
    let block_count = bits_len.div_ceil(block_bits);
    usize::try_from(block_count).map_err(|_| invalid_value("BitVec block count overflow"))
}

unsafe impl<C: Config, Block: BlockType + SchemaWrite<C, Src = Block>> SchemaWrite<C>
    for BitVec<Block>
{
    type Src = BitVec<Block>;

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        let n_blocks = src.block_len();
        let blocks_size = 1 /* Option tag */ + if n_blocks == 0 {
            0
        } else {
            let len_size = C::LengthEncoding::write_bytes_needed(n_blocks)?;
            len_size + if let TypeMeta::Static { size, zero_copy: _ } = Block::TYPE_META {
                n_blocks * size
            } else {
                (0..n_blocks).map(|i| Block::size_of(&serialized_block(src, i))).try_fold(0, |acc, r| r.map(|n| acc + n))?
            }
        };
        let bit_len_size = <u64 as SchemaWrite<C>>::size_of(&src.len())?;
        Ok(blocks_size + bit_len_size)
    }

    #[inline]
    fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        let n_blocks = src.block_len();
        if n_blocks == 0 {
            writer.write(&[0])?; // None
        } else {
            C::LengthEncoding::prealloc_check::<Block>(n_blocks)?;
            writer.write(&[1])?; // Some
            C::LengthEncoding::write(writer.by_ref(), n_blocks)?;
            if let TypeMeta::Static { size, zero_copy: _ } = Block::TYPE_META {
                // SAFETY: `Block` has a static serialized size of `size` bytes, so the total
                // byte count written by successful run of the loop below is `size * n_blocks`.
                #[allow(clippy::arithmetic_side_effects)]
                let mut writer = unsafe { writer.as_trusted_for(size * n_blocks)? };
                for i in 0..n_blocks {
                    Block::write(writer.by_ref(), &serialized_block(src, i))?;
                }
                writer.finish()?;
            } else {
                for i in 0..n_blocks {
                    Block::write(writer.by_ref(), &serialized_block(src, i))?;
                }
            }
        }
        <u64 as SchemaWrite<C>>::write(writer, &src.len())
    }
}

unsafe impl<'de, C: Config, Block: BlockType + SchemaRead<'de, C, Dst = Block>> SchemaRead<'de, C>
    for BitVec<Block>
{
    type Dst = BitVec<Block>;

    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let blocks = match reader.take_byte()? {
            0 => Box::<[Block]>::default(),
            1 => {
                let blocks = <Box<[Block]> as SchemaRead<C>>::get(reader.by_ref())?;
                #[cfg(feature = "bv-strict")]
                if blocks.is_empty() {
                    return Err(invalid_value("BitVec block storage is empty"));
                }
                blocks
            }
            tag => return Err(invalid_tag_encoding(tag as usize)),
        };
        let bits_len = <u64 as SchemaRead<'de, C>>::get(reader)?;

        #[cfg(feature = "bv-strict")]
        {
            let expected_blocks = expected_block_count::<Block>(bits_len)?;
            if blocks.len() != expected_blocks {
                return Err(invalid_value(
                    "BitVec block count does not match bit length",
                ));
            }

            let used_bits_in_final_block = Block::mod_nbits(bits_len);
            if used_bits_in_final_block != 0 {
                let padding_mask = !Block::low_mask(used_bits_in_final_block);
                let Some(final_block) = blocks.last() else {
                    return Err(invalid_value("BitVec missing final block"));
                };
                if *final_block & padding_mask != Block::zero() {
                    return Err(invalid_value(
                        "BitVec final block has non-zero padding bits",
                    ));
                }
            }
        }

        // Strict decoding already guarantees sufficient capacity through the exact
        // block-count check. Non-strict decoding permits surplus blocks, but the
        // declared length must still fit; `truncate` cannot grow the `BitVec` and
        // would otherwise silently produce a shorter value.
        #[cfg(not(feature = "bv-strict"))]
        if bits_len > Block::mul_nbits(blocks.len()) {
            return Err(invalid_value("BitVec bit length exceeds block capacity"));
        }

        // `BitVec::from` preserves empty storage as `Some([])`, which violates `bv`'s
        // internal invariant. Non-strict decoding accepts that Serde representation,
        // but normalizes it to the equivalent valid empty `BitVec`.
        let mut bv = if blocks.is_empty() {
            Self::Dst::new()
        } else {
            Self::Dst::from(blocks)
        };
        bv.truncate(bits_len);
        dst.write(bv);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{
            config::{self, Configuration},
            deserialize,
            proptest_config::proptest_cfg,
            serialize, serialized_size,
        },
        bincode::Options,
        proptest::prelude::*,
    };

    /// Ensures interoperability tests do not use `bv`'s invalid `Some([])` representation.
    fn normalized_bitvec<Block: BlockType>(blocks: impl Bits<Block = Block>) -> BitVec<Block> {
        if blocks.bit_len() == 0 {
            BitVec::new()
        } else {
            BitVec::from_bits(blocks)
        }
    }

    #[test]
    fn test_bitvec_padding() {
        let mut bv = BitVec::<u8>::from(vec![0xff]);
        bv.truncate(3);

        let wincode_bytes = serialize(&bv).unwrap();
        let block_pos = wincode_bytes.len() - 1 - core::mem::size_of::<u64>();

        #[cfg(feature = "bv-strict")]
        assert_eq!(wincode_bytes[block_pos], 0b0000_0111);

        #[cfg(not(feature = "bv-strict"))]
        assert_eq!(wincode_bytes[block_pos], 0b1111_1111);

        let bincode_deserialized: BitVec<u8> = bincode::deserialize(&wincode_bytes).unwrap();
        assert_eq!(bincode_deserialized, bv);
        let wincode_deserialized: BitVec<u8> = deserialize(&wincode_bytes).unwrap();
        assert_eq!(wincode_deserialized, bv);

        let bincode_bytes = bincode::serialize(&bv).unwrap();

        #[cfg(feature = "bv-strict")]
        assert!(deserialize::<BitVec<u8>>(&bincode_bytes).is_err());

        #[cfg(not(feature = "bv-strict"))]
        {
            let deserialized: BitVec<u8> = deserialize(&bincode_bytes).unwrap();
            assert_eq!(deserialized, bv);
        }
    }

    #[test]
    fn test_bitvec_varint_dirty_padding() {
        let mut bv = BitVec::<usize>::from(vec![usize::MAX]);
        bv.truncate(3);

        let c = Configuration::default().with_varint_encoding();
        let bincode_c = bincode::DefaultOptions::new().with_varint_encoding();

        let schema_serialized = config::serialize(&bv, c).unwrap();
        assert_eq!(
            config::serialized_size(&bv, c).unwrap() as usize,
            schema_serialized.len()
        );

        let bincode_deserialized: BitVec = bincode_c.deserialize(&schema_serialized).unwrap();
        assert_eq!(bincode_deserialized, bv);
        let schema_deserialized: BitVec = config::deserialize(&schema_serialized, c).unwrap();
        assert_eq!(schema_deserialized, bv);

        let bincode_serialized = bincode_c.serialize(&bv).unwrap();

        #[cfg(feature = "bv-strict")]
        {
            assert_ne!(schema_serialized, bincode_serialized);
            assert!(config::deserialize::<BitVec, _>(&bincode_serialized, c).is_err());
        }

        #[cfg(not(feature = "bv-strict"))]
        {
            assert_eq!(schema_serialized, bincode_serialized);
            assert_eq!(
                config::deserialize::<BitVec, _>(&bincode_serialized, c).unwrap(),
                bv
            );
        }
    }

    #[test]
    fn test_bitvec_spare_blocks() {
        let mut bv = BitVec::<u8>::from(vec![0xff, 0xaa]);
        bv.truncate(8);
        assert_eq!(bv.block_len(), 1);
        assert_eq!(bv.block_capacity(), 2);

        let wincode_bytes = serialize(&bv).unwrap();
        let bincode_bytes = bincode::serialize(&bv).unwrap();

        let bincode_deserialized: BitVec<u8> = bincode::deserialize(&wincode_bytes).unwrap();
        assert_eq!(bincode_deserialized, bv);

        #[cfg(feature = "bv-strict")]
        {
            let wincode_deserialized: BitVec<u8> = deserialize(&wincode_bytes).unwrap();
            assert_eq!(wincode_deserialized, bv);
        }

        #[cfg(feature = "bv-strict")]
        assert!(deserialize::<BitVec<u8>>(&bincode_bytes).is_err());

        #[cfg(not(feature = "bv-strict"))]
        {
            let deserialized: BitVec<u8> = deserialize(&bincode_bytes).unwrap();
            assert_eq!(deserialized, bv);
        }
    }

    #[test]
    fn test_bitvec_read_invalid_length() {
        let bv = BitVec::<u8>::from(vec![0xff]);
        let mut bytes = bincode::serialize(&bv).unwrap();
        let len_pos = bytes.len() - core::mem::size_of::<u64>();
        bytes[len_pos..].copy_from_slice(&9u64.to_le_bytes());

        assert!(bincode::deserialize::<BitVec<u8>>(&bytes).is_err());
        assert!(deserialize::<BitVec<u8>>(&bytes).is_err());
    }

    #[test]
    fn test_bitvec_empty_block_storage() {
        let bv = BitVec::<u8>::from(Vec::new());
        let bincode_bytes = bincode::serialize(&bv).unwrap();

        assert!(bincode::deserialize::<BitVec<u8>>(&bincode_bytes).is_err());

        #[cfg(feature = "bv-strict")]
        assert!(deserialize::<BitVec<u8>>(&bincode_bytes).is_err());

        #[cfg(not(feature = "bv-strict"))]
        {
            let deserialized: BitVec<u8> = deserialize(&bincode_bytes).unwrap();
            assert_eq!(deserialized, bv);
        }

        let wincode_bytes = serialize(&bv).unwrap();
        let bincode_deserialized: BitVec<u8> = bincode::deserialize(&wincode_bytes).unwrap();
        assert_eq!(bincode_deserialized, bv);
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_bitvec_blocks(blocks: Vec<usize>) {
            let bv = normalized_bitvec(blocks);

            let bincode_serialized = bincode::serialize(&bv).unwrap();
            let schema_serialized = serialize(&bv).unwrap();
            prop_assert_eq!(serialized_size(&bv).unwrap() as usize, schema_serialized.len());
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BitVec = bincode::deserialize(&schema_serialized).unwrap();
            let schema_deserialized: BitVec = deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(bv.clone(), bincode_deserialized);
            prop_assert_eq!(bv, schema_deserialized);
        }

        #[test]
        fn test_bitvec_bits(bits: Vec<bool>) {
            let bv = normalized_bitvec(bits);

            let bincode_serialized = bincode::serialize(&bv).unwrap();
            let schema_serialized = serialize(&bv).unwrap();
            prop_assert_eq!(serialized_size(&bv).unwrap() as usize, schema_serialized.len());
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BitVec<u8> = bincode::deserialize(&schema_serialized).unwrap();
            let schema_deserialized: BitVec<u8> = deserialize(&bincode_serialized).unwrap();
            prop_assert_eq!(bv.clone(), bincode_deserialized);
            prop_assert_eq!(bv, schema_deserialized);
        }

        #[test]
        fn test_bitvec_varint(blocks: Vec<usize>) {
            let bv = normalized_bitvec(blocks);

            let c = Configuration::default().with_varint_encoding();
            let bincode_c = bincode::DefaultOptions::new().with_varint_encoding();

            let bincode_serialized = bincode_c.serialize(&bv).unwrap();
            let schema_serialized = config::serialize(&bv, c).unwrap();
            prop_assert_eq!(config::serialized_size(&bv, c).unwrap() as usize, schema_serialized.len());
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BitVec = bincode_c.deserialize(&schema_serialized).unwrap();
            let schema_deserialized: BitVec = config::deserialize(&bincode_serialized, c).unwrap();
            prop_assert_eq!(bv.clone(), bincode_deserialized);
            prop_assert_eq!(bv, schema_deserialized);
        }
    }
}
