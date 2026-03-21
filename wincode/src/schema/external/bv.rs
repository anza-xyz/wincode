use {
    crate::{
        ReadResult, SchemaRead, SchemaWrite, TypeMeta, WriteResult,
        config::Config,
        error::invalid_tag_encoding,
        io::{Reader, Writer},
        len::SeqLen,
    },
    bv::{BitVec, Bits, BlockType},
    core::mem::MaybeUninit,
};

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
                (0..n_blocks).map(|i| Block::size_of(&src.get_raw_block(i))).try_fold(0, |acc, r| r.map(|n| acc + n))?
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
            writer.write(&[1])?; // Some
            C::LengthEncoding::write(writer.by_ref(), n_blocks)?;
            if let TypeMeta::Static { size, zero_copy: _ } = Block::TYPE_META {
                // SAFETY: `Block` has a static serialized size of `size` bytes, so the total
                // byte count written by successful run of the loop below is `size * n_blocks`.
                #[allow(clippy::arithmetic_side_effects)]
                let mut writer = unsafe { writer.as_trusted_for(size * n_blocks)? };
                for i in 0..n_blocks {
                    Block::write(writer.by_ref(), &src.get_raw_block(i))?;
                }
            } else {
                for i in 0..n_blocks {
                    Block::write(writer.by_ref(), &src.get_raw_block(i))?;
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
        let mut bv = match reader.take_byte()? {
            0 => BitVec::new(),
            1 => {
                let blocks = <Box<[Block]> as SchemaRead<C>>::get(reader.by_ref())?;
                Self::Dst::from(blocks)
            }
            tag => return Err(invalid_tag_encoding(tag as usize)),
        };
        let bits_len = <u64 as SchemaRead<'de, C>>::get(reader)?;
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

    /// Ensures tests comparing serde and wincode serialized formats use consistent encoding
    ///
    /// Serde serialization depends on how BitVec was created, empty vec can be either
    /// 0 (inner `None`) or 1,0 (`Some` with inner len equal 0) if created with `from_bits`.
    fn normalized_bitvec<Block: BlockType>(blocks: impl Bits<Block = Block>) -> BitVec<Block> {
        if blocks.bit_len() == 0 {
            BitVec::new()
        } else {
            BitVec::from_bits(blocks)
        }
    }

    #[test]
    fn test_bitvec_empty() {
        // BitVec::new() has inner=None; BitVec::from_bits with empty blocks has inner=Some([]),
        // which differ in serde encoding. Both should round-trip correctly through our impl.
        let bv_new: BitVec = BitVec::new();
        let bv_from_bits: BitVec = BitVec::from_bits(Vec::<usize>::new());

        let serialized_new = serialize(&bv_new).unwrap();
        assert_eq!(
            serialized_size(&bv_new).unwrap() as usize,
            serialized_new.len()
        );
        let deserialized_new: BitVec = deserialize(&serialized_new).unwrap();
        assert_eq!(bv_new, deserialized_new);

        let serialized_from_bits = serialize(&bv_from_bits).unwrap();
        assert_eq!(
            serialized_size(&bv_from_bits).unwrap() as usize,
            serialized_from_bits.len()
        );
        let deserialized_from_bits: BitVec = deserialize(&serialized_from_bits).unwrap();
        assert_eq!(bv_from_bits, deserialized_from_bits);
    }

    proptest! {
        #![proptest_config(proptest_cfg())]

        #[test]
        fn test_bitvec(blocks: Vec<usize>) {
            let bv = normalized_bitvec(blocks);

            let bincode_serialized = bincode::serialize(&bv).unwrap();
            let schema_serialized = serialize(&bv).unwrap();
            prop_assert_eq!(serialized_size(&bv).unwrap() as usize, schema_serialized.len());
            prop_assert_eq!(&bincode_serialized, &schema_serialized);

            let bincode_deserialized: BitVec = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BitVec = deserialize(&schema_serialized).unwrap();
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

            let bincode_deserialized: BitVec<u8> = bincode::deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BitVec<u8> = deserialize(&schema_serialized).unwrap();
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

            let bincode_deserialized: BitVec = bincode_c.deserialize(&bincode_serialized).unwrap();
            let schema_deserialized: BitVec = config::deserialize(&schema_serialized, c).unwrap();
            prop_assert_eq!(bv.clone(), bincode_deserialized);
            prop_assert_eq!(bv, schema_deserialized);
        }
    }
}
