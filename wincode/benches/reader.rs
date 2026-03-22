#![allow(clippy::arithmetic_side_effects)]
use {
    bincode::Decode,
    criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main},
    rand::{random, random_bool},
    serde::{Deserialize, Serialize},
    std::{
        fs::{File, OpenOptions},
        hint::black_box,
        io::{BufReader, Write},
        mem::MaybeUninit,
    },
    wincode::{
        DeserializeOwned as _, ReadResult, SchemaRead, SchemaWrite, WriteResult,
        config::Config,
        io::{Reader, Writer, std_read::BufReadAdapter},
        serialize, serialized_size,
    },
};

#[derive(Serialize, Deserialize, SchemaWrite, SchemaRead, Clone, Decode)]
struct SimpleStruct {
    id: u64,
    value: u64,
    flag: bool,
}

#[derive(Clone, Copy, SchemaWrite, SchemaRead, Serialize, Deserialize, Decode)]
struct PodStruct {
    a: [u8; 32],
    b: [u8; 16],
    c: [u8; 8],
    d: [u8; 8],
}

fn bench_vec_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<SimpleStruct>");

    for size in [1_000, 10_000] {
        let data: Vec<SimpleStruct> = (0..size)
            .map(|i| SimpleStruct {
                id: i,
                value: i * 2,
                flag: i % 2 == 0,
            })
            .collect();
        let data_size = serialized_size(&data).unwrap();
        group.throughput(Throughput::Bytes(data_size));
        let serialized = serialize(&data).unwrap();
        OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open("./serialized.bin")
            .unwrap()
            .write_all(&serialized)
            .unwrap();

        group.bench_function(
            BenchmarkId::new("wincode/deserialize-buf-read-direct", size),
            |b| {
                b.iter_batched(
                    || BufReader::new(File::open("./serialized.bin").unwrap()),
                    |reader| {
                        black_box(wincode::deserialize_from::<Vec<SimpleStruct>>(reader).unwrap())
                    },
                    criterion::BatchSize::PerIteration,
                );
            },
        );

        group.bench_function(BenchmarkId::new("wincode/deserialize", size), |b| {
            b.iter_batched(
                || BufReadAdapter::from_read(File::open("./serialized.bin").unwrap()),
                |reader| black_box(wincode::deserialize_from::<Vec<SimpleStruct>>(reader).unwrap()),
                criterion::BatchSize::PerIteration,
            );
        });

        group.bench_function(BenchmarkId::new("bincode/deserialize", size), |b| {
            b.iter_batched(
                || BufReader::new(File::open("./serialized.bin").unwrap()),
                |reader| {
                    black_box(bincode1::deserialize_from::<_, Vec<SimpleStruct>>(reader).unwrap())
                },
                criterion::BatchSize::PerIteration,
            );
        });

        group.bench_function(BenchmarkId::new("bincode2/deserialize", size), |b| {
            b.iter_batched(
                || BufReader::new(File::open("./serialized.bin").unwrap()),
                |mut reader| {
                    black_box(
                        bincode::decode_from_std_read::<Vec<SimpleStruct>, _, _>(
                            &mut reader,
                            bincode::config::legacy(),
                        )
                        .unwrap(),
                    )
                },
                criterion::BatchSize::PerIteration,
            );
        });
    }

    group.finish();
}

fn bench_vec_comparison_pod(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<PodStruct>");

    for size in [1_000, 10_000] {
        let data: Vec<PodStruct> = (0..size)
            .map(|i| PodStruct {
                a: [i as u8; 32],
                b: [i as u8; 16],
                c: [i as u8; 8],
                d: [i as u8; 8],
            })
            .collect();
        let data_size = serialized_size(&data).unwrap();
        group.throughput(Throughput::Bytes(data_size));
        let serialized = serialize(&data).unwrap();
        OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open("./serialized.bin")
            .unwrap()
            .write_all(&serialized)
            .unwrap();

        group.bench_function(
            BenchmarkId::new("wincode/deserialize-buf-read-direct", size),
            |b| {
                b.iter_batched(
                    || BufReader::new(File::open("./serialized.bin").unwrap()),
                    |reader| {
                        black_box(wincode::deserialize_from::<Vec<PodStruct>>(reader).unwrap())
                    },
                    criterion::BatchSize::PerIteration,
                );
            },
        );

        group.bench_function(BenchmarkId::new("wincode/deserialize", size), |b| {
            b.iter_batched(
                || BufReadAdapter::from_read(File::open("./serialized.bin").unwrap()),
                |reader| black_box(wincode::deserialize_from::<Vec<PodStruct>>(reader).unwrap()),
                criterion::BatchSize::PerIteration,
            );
        });

        group.bench_function(BenchmarkId::new("bincode/deserialize", size), |b| {
            b.iter_batched(
                || BufReader::new(File::open("./serialized.bin").unwrap()),
                |reader| {
                    black_box(bincode1::deserialize_from::<_, Vec<PodStruct>>(reader).unwrap())
                },
                criterion::BatchSize::PerIteration,
            );
        });

        group.bench_function(BenchmarkId::new("bincode2/deserialize", size), |b| {
            b.iter_batched(
                || BufReader::new(File::open("./serialized.bin").unwrap()),
                |mut reader| {
                    black_box(
                        bincode::decode_from_std_read::<Vec<PodStruct>, _, _>(
                            &mut reader,
                            bincode::config::legacy(),
                        )
                        .unwrap(),
                    )
                },
                criterion::BatchSize::PerIteration,
            );
        });
    }

    group.finish();
}

fn bench_vec_comparison_versioned_message(c: &mut Criterion) {
    let mut group = c.benchmark_group("Vec<VersionedMessage>");

    for size in [10, 100, 1_000] {
        let data: Vec<VersionedMessage> = (0..size).map(|_| rand_versioned_message()).collect();
        let data_size = serialized_size(&data).unwrap();
        group.throughput(Throughput::Bytes(data_size));
        let serialized = serialize(&data).unwrap();
        OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open("./serialized.bin")
            .unwrap()
            .write_all(&serialized)
            .unwrap();

        group.bench_function(
            BenchmarkId::new("wincode/deserialize-buf-read-direct", size),
            |b| {
                b.iter_batched(
                    || BufReader::new(File::open("./serialized.bin").unwrap()),
                    |reader| {
                        black_box(<Vec<VersionedMessageCtx>>::deserialize_from(reader).unwrap())
                    },
                    criterion::BatchSize::PerIteration,
                );
            },
        );

        group.bench_function(BenchmarkId::new("wincode/deserialize", size), |b| {
            b.iter_batched(
                || BufReadAdapter::from_read(File::open("./serialized.bin").unwrap()),
                |reader| black_box(<Vec<VersionedMessagePeek>>::deserialize_from(reader).unwrap()),
                criterion::BatchSize::PerIteration,
            );
        });
    }

    group.finish();
}

const MESSAGE_VERSION_PREFIX: u8 = 128;

#[derive(SchemaRead, SchemaWrite)]
struct MessageHeader {
    num_required_signatures: u8,
    num_unsigned_accounts: u8,
    num_signed_accounts: u8,
}

#[repr(transparent)]
#[derive(SchemaRead, SchemaWrite)]
struct Address([u8; 32]);

#[repr(transparent)]
#[derive(SchemaRead, SchemaWrite)]
struct Hash([u8; 32]);

#[derive(SchemaRead, SchemaWrite)]
struct LegacyMessage {
    header: MessageHeader,
    account_key: Address,
    recent_blockhash: Hash,
}

#[derive(SchemaWrite, SchemaRead)]
struct V0Message {
    header: MessageHeader,
    account_key: Address,
    recent_blockhash: Hash,
    slot: u64,
}

enum VersionedMessage {
    Legacy(LegacyMessage),
    V0(V0Message),
}

unsafe impl<C: Config> SchemaWrite<C> for VersionedMessage {
    type Src = Self;

    // V0 and V1 add +1 for message version prefix
    #[allow(clippy::arithmetic_side_effects)]
    #[inline(always)]
    fn size_of(src: &Self::Src) -> WriteResult<usize> {
        match src {
            VersionedMessage::Legacy(message) => {
                <LegacyMessage as SchemaWrite<C>>::size_of(message)
            }
            VersionedMessage::V0(message) => {
                Ok(1 + <V0Message as SchemaWrite<C>>::size_of(message)?)
            }
        }
    }

    // V0 and V1 add +1 for message version prefix
    #[allow(clippy::arithmetic_side_effects)]
    #[inline(always)]
    fn write(mut writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
        match src {
            VersionedMessage::Legacy(message) => {
                <LegacyMessage as SchemaWrite<C>>::write(writer, message)
            }
            VersionedMessage::V0(message) => {
                <u8 as SchemaWrite<C>>::write(writer.by_ref(), &MESSAGE_VERSION_PREFIX)?;
                <V0Message as SchemaWrite<C>>::write(writer, message)
            }
        }
    }
}

struct VersionedMessagePeek;
unsafe impl<'de, C: Config> SchemaRead<'de, C> for VersionedMessagePeek {
    type Dst = VersionedMessage;

    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let variant = reader.peek_byte()?;

        if variant & MESSAGE_VERSION_PREFIX != 0 {
            // Safety: at least 1 byte can be consumed, since it was peeked
            unsafe { reader.consume_unchecked(1) };
            use wincode::error::invalid_tag_encoding;

            let version = variant & !MESSAGE_VERSION_PREFIX;
            return match version {
                0 => {
                    let msg = <V0Message as SchemaRead<C>>::get(reader)?;
                    dst.write(VersionedMessage::V0(msg));
                    Ok(())
                }

                _ => Err(invalid_tag_encoding(version as usize)),
            };
        };
        let legacy = <LegacyMessage as SchemaRead<C>>::get(reader)?;
        dst.write(VersionedMessage::Legacy(legacy));

        Ok(())
    }
}

struct VersionedMessageCtx;
unsafe impl<'de, C: Config> SchemaRead<'de, C> for VersionedMessageCtx {
    type Dst = VersionedMessage;

    fn read(mut reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        let variant = reader.take_byte()?;

        if variant & MESSAGE_VERSION_PREFIX != 0 {
            use wincode::error::invalid_tag_encoding;

            let version = variant & !MESSAGE_VERSION_PREFIX;
            return match version {
                0 => {
                    let msg = <V0Message as SchemaRead<C>>::get(reader)?;
                    dst.write(VersionedMessage::V0(msg));
                    Ok(())
                }

                _ => Err(invalid_tag_encoding(version as usize)),
            };
        };

        let header = {
            let mut reader = unsafe { reader.as_trusted_for(2) }?;
            MessageHeader {
                num_required_signatures: variant,
                num_unsigned_accounts: reader.take_byte()?,
                num_signed_accounts: reader.take_byte()?,
            }
        };
        let account_key = <Address as SchemaRead<C>>::get(reader.by_ref())?;
        let recent_blockhash = <Hash as SchemaRead<C>>::get(reader.by_ref())?;

        dst.write(VersionedMessage::Legacy(LegacyMessage {
            header,
            account_key,
            recent_blockhash,
        }));

        Ok(())
    }
}

fn random_message_header() -> MessageHeader {
    MessageHeader {
        num_required_signatures: random::<u8>().min(MESSAGE_VERSION_PREFIX - 1),
        num_unsigned_accounts: random(),
        num_signed_accounts: random(),
    }
}

fn random_address() -> Address {
    Address(core::array::from_fn(|_| random()))
}

fn random_hash() -> Hash {
    Hash(core::array::from_fn(|_| random()))
}

fn rand_versioned_message() -> VersionedMessage {
    if random_bool(0.5) {
        VersionedMessage::Legacy(LegacyMessage {
            header: random_message_header(),
            account_key: random_address(),
            recent_blockhash: random_hash(),
        })
    } else {
        VersionedMessage::V0(V0Message {
            header: random_message_header(),
            account_key: random_address(),
            recent_blockhash: random_hash(),
            slot: random(),
        })
    }
}

criterion_group!(
    benches,
    bench_vec_comparison_versioned_message,
    bench_vec_comparison,
    bench_vec_comparison_pod,
);
criterion_main!(benches);
