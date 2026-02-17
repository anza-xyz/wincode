#![no_main]

use {
    libfuzzer_sys::fuzz_target,
    solana_address::Address,
    solana_entry::{
        block_component::{
            BlockComponent, BlockFooterV1, BlockHeaderV1, BlockMarkerV1, FinalCertificate,
            GenesisCertificate, NotarRewardCertificate, SkipRewardCertificate, UpdateParentV1,
            VersionedBlockFooter, VersionedBlockHeader, VersionedBlockMarker,
            VersionedUpdateParent, VotesAggregate,
        },
        entry::Entry,
    },
    solana_fee_calculator::FeeCalculator,
    solana_hash::Hash,
    solana_message::{
        compiled_instruction::CompiledInstruction,
        v0::{Message as V0Message, MessageAddressTableLookup},
        Message as LegacyMessage, MessageHeader, VersionedMessage,
    },
    solana_nonce::{
        state::{Data as NonceData, DurableNonce, State as NonceState},
        versions::Versions as NonceVersions,
    },
    solana_signature::Signature,
    solana_transaction::{versioned::VersionedTransaction, Transaction},
};

macro_rules! fuzz_roundtrip {
    ($data:expr, $ty:ty) => {
        if let Ok(value) = wincode::deserialize::<$ty>($data) {
            let serialized = wincode::serialize(&value).expect("serialize should succeed");
            let roundtrip: $ty =
                wincode::deserialize(&serialized).expect("roundtrip deserialize should succeed");
            assert_eq!(value, roundtrip, "roundtrip failed for {}", stringify!($ty));
        }
    };
}

fuzz_target!(|data: &[u8]| {
    fuzz_roundtrip!(data, Address);
    fuzz_roundtrip!(data, Hash);
    fuzz_roundtrip!(data, DurableNonce);
    fuzz_roundtrip!(data, Signature);
    fuzz_roundtrip!(data, FeeCalculator);
    fuzz_roundtrip!(data, MessageHeader);
    fuzz_roundtrip!(data, CompiledInstruction);
    fuzz_roundtrip!(data, MessageAddressTableLookup);
    fuzz_roundtrip!(data, NonceData);
    fuzz_roundtrip!(data, NonceState);
    fuzz_roundtrip!(data, NonceVersions);
    fuzz_roundtrip!(data, LegacyMessage);
    fuzz_roundtrip!(data, V0Message);
    fuzz_roundtrip!(data, VersionedMessage);
    fuzz_roundtrip!(data, Transaction);
    fuzz_roundtrip!(data, VersionedTransaction);
    fuzz_roundtrip!(data, Entry);
    fuzz_roundtrip!(data, SkipRewardCertificate);
    fuzz_roundtrip!(data, NotarRewardCertificate);
    fuzz_roundtrip!(data, BlockFooterV1);
    fuzz_roundtrip!(data, BlockHeaderV1);
    fuzz_roundtrip!(data, UpdateParentV1);
    fuzz_roundtrip!(data, GenesisCertificate);
    fuzz_roundtrip!(data, FinalCertificate);
    fuzz_roundtrip!(data, VotesAggregate);
    fuzz_roundtrip!(data, VersionedBlockFooter);
    fuzz_roundtrip!(data, VersionedBlockHeader);
    fuzz_roundtrip!(data, VersionedUpdateParent);
    fuzz_roundtrip!(data, BlockMarkerV1);
    fuzz_roundtrip!(data, VersionedBlockMarker);
    fuzz_roundtrip!(data, BlockComponent);
});
