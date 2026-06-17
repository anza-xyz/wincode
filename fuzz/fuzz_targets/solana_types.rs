#![no_main]

use {
    agave_votor_messages::{
        certificate::{Certificate, CertificateType},
        consensus_message::{Block, ConsensusMessage, VoteMessage},
        reward_certificate::{NotarRewardCertificate, SkipRewardCertificate},
        vote::{
            FinalizationVote, GenesisVote, NotarizationFallbackVote, NotarizationVote,
            SkipFallbackVote, SkipVote, Vote,
        },
    },
    libfuzzer_sys::fuzz_target,
    solana_address::Address,
    solana_entry::{
        block_component::{
            BlockComponent, BlockFinalizationCert, BlockFooterV1, BlockHeaderV1, BlockMarkerV1,
            GenesisCertBlockMarker, UpdateParentV1, VersionedBlockFooter, VersionedBlockHeader,
            VersionedBlockMarker, VersionedUpdateParent, VotesAggregate,
        },
        entry::Entry,
    },
    solana_fee_calculator::FeeCalculator,
    solana_gossip::{
        contact_info::ContactInfo,
        crds_data::{CrdsData, LowestSlot, SnapshotHashes, Vote as CrdsVote},
        crds_gossip_pull::CrdsFilter,
        crds_value::CrdsValue,
        duplicate_shred::DuplicateShred,
        epoch_slots::{CompressedSlots, EpochSlots, Flate2, Uncompressed},
        restart_crds_values::{RestartHeaviestFork, RestartLastVotedForkSlots},
    },
    solana_hash::Hash,
    solana_message::{
        compiled_instruction::CompiledInstruction,
        v0::{Message as V0Message, MessageAddressTableLookup},
        v1::Message as V1Message,
        Message as LegacyMessage, MessageHeader, VersionedMessage,
    },
    solana_nonce::{
        state::{Data as NonceData, DurableNonce, State as NonceState},
        versions::Versions as NonceVersions,
    },
    solana_signature::Signature,
    solana_transaction::{versioned::VersionedTransaction, Transaction},
    solana_version::Version,
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
    fuzz_roundtrip!(data, V1Message);
    fuzz_roundtrip!(data, VersionedMessage);
    fuzz_roundtrip!(data, Transaction);
    fuzz_roundtrip!(data, VersionedTransaction);
    fuzz_roundtrip!(data, Entry);
    fuzz_roundtrip!(data, SkipRewardCertificate);
    fuzz_roundtrip!(data, NotarRewardCertificate);
    fuzz_roundtrip!(data, NotarizationVote);
    fuzz_roundtrip!(data, FinalizationVote);
    fuzz_roundtrip!(data, SkipVote);
    fuzz_roundtrip!(data, NotarizationFallbackVote);
    fuzz_roundtrip!(data, SkipFallbackVote);
    fuzz_roundtrip!(data, GenesisVote);
    fuzz_roundtrip!(data, Vote);
    fuzz_roundtrip!(data, VoteMessage);
    fuzz_roundtrip!(data, CertificateType);
    fuzz_roundtrip!(data, Certificate);
    fuzz_roundtrip!(data, ConsensusMessage);
    fuzz_roundtrip!(data, Block);
    fuzz_roundtrip!(data, BlockFooterV1);
    fuzz_roundtrip!(data, BlockHeaderV1);
    fuzz_roundtrip!(data, UpdateParentV1);
    fuzz_roundtrip!(data, GenesisCertBlockMarker);
    fuzz_roundtrip!(data, BlockFinalizationCert);
    fuzz_roundtrip!(data, VotesAggregate);
    fuzz_roundtrip!(data, VersionedBlockFooter);
    fuzz_roundtrip!(data, VersionedBlockHeader);
    fuzz_roundtrip!(data, VersionedUpdateParent);
    fuzz_roundtrip!(data, BlockMarkerV1);
    fuzz_roundtrip!(data, VersionedBlockMarker);
    fuzz_roundtrip!(data, BlockComponent);
    fuzz_roundtrip!(data, CrdsValue);
    fuzz_roundtrip!(data, ContactInfo);
    fuzz_roundtrip!(data, CrdsVote);
    fuzz_roundtrip!(data, CrdsData);
    fuzz_roundtrip!(data, SnapshotHashes);
    fuzz_roundtrip!(data, LowestSlot);
    fuzz_roundtrip!(data, CrdsFilter);
    fuzz_roundtrip!(data, DuplicateShred);
    fuzz_roundtrip!(data, EpochSlots);
    fuzz_roundtrip!(data, CompressedSlots);
    fuzz_roundtrip!(data, Uncompressed);
    fuzz_roundtrip!(data, Flate2);
    fuzz_roundtrip!(data, RestartLastVotedForkSlots);
    fuzz_roundtrip!(data, RestartHeaviestFork);
    fuzz_roundtrip!(data, Version);
});
