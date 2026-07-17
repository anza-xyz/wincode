#![no_main]

// Solana crates still derive against wincode 0.5.x. Keep this target on that
// exact release until the Solana dependency stack supports wincode 0.6.x.
use {
    agave_votor_messages::{
        consensus_message::{Certificate, CertificateType, ConsensusMessage, VoteMessage},
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
            BlockComponent, BlockFooterV1, BlockHeaderV1, BlockMarkerV1, FinalCertificate,
            GenesisCertificate, UpdateParentV1, VersionedBlockFooter, VersionedBlockHeader,
            VersionedBlockMarker, VersionedUpdateParent, VotesAggregate,
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
    wincode_0_5 as wincode,
};

macro_rules! fuzz_roundtrip {
    ($data:expr, $ty:ty) => {
        if let Ok(value) = wincode::deserialize_exact::<$ty>($data) {
            let serialized = wincode::serialize(&value).expect("serialize should succeed");
            assert_eq!($data, serialized, "deserialize -> serialize != orignal_data for type {}\nserialized {:?}\noriginal   {:?}", stringify!($ty), serialized, $data,);
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
