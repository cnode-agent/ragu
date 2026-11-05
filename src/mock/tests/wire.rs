use alloc::{string::ToString as _, vec::Vec};

use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe as _,
    pasta::Fp,
};
use ragu_primitives::{Element, allocator::Allocator};
use rand::{SeedableRng as _, rngs::StdRng};

use super::test_params;
use crate::{
    ApplicationBuilder, Encoded, Header, Index, Pcd, Proof, Step, StepCtx, Suffix, WireHeader,
    wire::Error,
};

const HEADER_SIZE: usize = 4;
type TestApp = crate::Application<'static, HEADER_SIZE>;
type TestPcd<H> = Pcd<H>;
type TestProof = Proof;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ValueData {
    value: u64,
}

/// Header carrying one field element, with a wire codec for its data.
struct ValueHeader;

impl Header for ValueHeader {
    type Data = ValueData;
    type Output = Kind![Fp; Element<'_, _>];

    const SUFFIX: Suffix = Suffix::new(0);

    fn encode<'dr, D: Driver<'dr, F = Fp>, A: Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        data: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Element::alloc(dr, allocator, data.map(|data| Fp::from(data.value)))
    }
}

impl WireHeader for ValueHeader {
    fn data_to_bytes(data: &Self::Data) -> Vec<u8> {
        data.value.to_le_bytes().to_vec()
    }

    fn data_from_bytes(bytes: &[u8]) -> Option<Self::Data> {
        let bytes: &[u8; 8] = bytes.try_into().ok()?;
        Some(ValueData {
            value: u64::from_le_bytes(*bytes),
        })
    }
}

/// A header with the same shape but a different suffix.
struct OtherHeader;

impl Header for OtherHeader {
    type Data = ValueData;
    type Output = Kind![Fp; Element<'_, _>];

    const SUFFIX: Suffix = Suffix::new(1);

    fn encode<'dr, D: Driver<'dr, F = Fp>, A: Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        data: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Element::alloc(dr, allocator, data.map(|data| Fp::from(data.value)))
    }
}

impl WireHeader for OtherHeader {
    fn data_to_bytes(data: &Self::Data) -> Vec<u8> {
        data.value.to_le_bytes().to_vec()
    }

    fn data_from_bytes(bytes: &[u8]) -> Option<Self::Data> {
        let bytes: &[u8; 8] = bytes.try_into().ok()?;
        Some(ValueData {
            value: u64::from_le_bytes(*bytes),
        })
    }
}

/// Seed step producing a [`ValueHeader`].
struct ValueSeedStep;

impl Step for ValueSeedStep {
    type Shared = ();
    type Aux<'source> = ();
    type Left = ();
    type Output = ValueHeader;
    type Right = ();
    type Witness<'source> = u64;

    const INDEX: Index = Index::new(0);

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = Fp>, const HS: usize>(
        &self,
        ctx: &mut StepCtx<'_, 'dr, D>,
        witness: DriverValue<D, Self::Witness<'source>>,
        _left: DriverValue<D, <Self::Left as Header>::Data>,
        _right: DriverValue<D, <Self::Right as Header>::Data>,
    ) -> Result<(
        (
            Encoded<'dr, D, Self::Left, HS>,
            Encoded<'dr, D, Self::Right, HS>,
            Encoded<'dr, D, Self::Output, HS>,
        ),
        (),
        DriverValue<D, <Self::Output as Header>::Data>,
        DriverValue<D, Self::Aux<'source>>,
    )>
    where
        Self: 'dr,
    {
        let output = witness.map(|value| ValueData { value });
        Ok((
            (
                Encoded::from_gadget(()),
                Encoded::from_gadget(()),
                Encoded::new(ctx.dr, &mut (), output.clone())?,
            ),
            (),
            output,
            D::unit(),
        ))
    }
}

fn value_app() -> TestApp {
    ApplicationBuilder::new(test_params())
        .register(ValueSeedStep)
        .expect("register")
        .finalize()
        .expect("finalize")
}

fn value_pcd(value: u64) -> TestPcd<ValueHeader> {
    value_app()
        .seed(&mut StdRng::from_seed([7; 32]), ValueSeedStep, value)
        .expect("seed")
        .0
}

#[test]
fn proof_round_trip() {
    let proof = value_pcd(7).proof().clone();
    let bytes = proof.to_bytes();
    assert_eq!(bytes.len(), TestProof::encoded_len());
    let decoded = TestProof::from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.to_bytes(), bytes);

    let bootstrap = Proof::bootstrap::<HEADER_SIZE>();
    let bytes = bootstrap.to_bytes();
    let decoded = TestProof::from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.to_bytes(), bytes);
}

#[test]
fn pcd_round_trip() {
    let pcd = value_pcd(42);
    let bytes = pcd.to_bytes().expect("encode");
    let decoded = TestPcd::<ValueHeader>::from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.data(), &ValueData { value: 42 });
    assert_eq!(decoded.proof().to_bytes(), pcd.proof().to_bytes());

    let unit = Proof::bootstrap::<HEADER_SIZE>().carry::<()>(());
    let bytes = unit.to_bytes().expect("encode");
    let decoded = TestPcd::<()>::from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.data(), &());
}

#[test]
fn rejects_every_envelope_component_mutation() {
    let bytes = value_pcd(7).proof().to_bytes();
    for (offset, reason) in [
        (0, "invalid proof magic"),
        (8, "unsupported proof envelope version"),
        (10, "proof payload kind mismatch"),
        (12, "unsupported proof schema version"),
        (14, "unsupported proof protocol version"),
        (16, "mock proofs carry no rank"),
        (20, "mock data length exceeds the limit"),
    ] {
        let mut mutated = bytes.clone();
        mutated[offset] ^= 1;
        assert!(
            matches!(TestProof::from_bytes(&mutated), Err(Error::Invalid { offset: at, reason: why, .. }) if at == offset && why == reason),
            "offset {offset} must fail with {reason}"
        );
    }
}

#[test]
fn rejects_truncation_and_trailing_bytes() {
    let proof = value_pcd(7).proof().to_bytes();
    assert!(matches!(
        TestProof::from_bytes(&proof[..proof.len() - 1]),
        Err(Error::Length { .. })
    ));
    let mut longer = proof.clone();
    longer.push(0);
    assert!(matches!(
        TestProof::from_bytes(&longer),
        Err(Error::Length { .. })
    ));

    let bytes = value_pcd(42).to_bytes().expect("encode");
    assert!(matches!(
        TestPcd::<ValueHeader>::from_bytes(&bytes[..bytes.len() - 1]),
        Err(Error::Length { .. })
    ));
    let mut longer = bytes.clone();
    longer.push(0);
    assert!(matches!(
        TestPcd::<ValueHeader>::from_bytes(&longer),
        Err(Error::Length { .. })
    ));
}

#[test]
fn rejects_suffix_mismatch() {
    let bytes = value_pcd(42).to_bytes().expect("encode");
    assert!(matches!(
        TestPcd::<OtherHeader>::from_bytes(&bytes),
        Err(Error::Invalid {
            reason: "mock PCD header suffix mismatch",
            ..
        })
    ));
}

#[test]
fn rejects_data_rejected_by_its_header() {
    let bytes = value_pcd(42).to_bytes().expect("encode");
    // One more byte of data than the codec accepts: fix up both length
    // fields so only the codec's own rejection remains.
    let mut longer = Vec::with_capacity(bytes.len() + 1);
    longer.extend_from_slice(&bytes);
    longer.push(0);
    longer[20..28].copy_from_slice(&9u64.to_le_bytes());
    let payload_length = bytes.len() - 8 - 8; // offset of the payload's data length
    longer[payload_length..payload_length + 8].copy_from_slice(&9u64.to_le_bytes());
    assert!(matches!(
        TestPcd::<ValueHeader>::from_bytes(&longer),
        Err(Error::Invalid {
            reason: "header data rejected by its header",
            ..
        })
    ));
}

#[test]
fn rejects_data_length_disagreeing_with_the_envelope() {
    let mut bytes = value_pcd(42).to_bytes().expect("encode");
    // The payload's declared data length follows the proof and suffix.
    let length_offset = bytes.len() - 8 - 8;
    bytes[length_offset] ^= 1;
    assert!(matches!(
        TestPcd::<ValueHeader>::from_bytes(&bytes),
        Err(Error::Invalid {
            reason: "mock PCD data length does not match the envelope",
            ..
        })
    ));
}

#[test]
fn rejects_binding_mismatch() {
    let mut bytes = value_pcd(7).proof().to_bytes();
    // The binding hash follows the step index and two hashes in the payload.
    bytes[28 + 8 + 64] ^= 1;
    assert!(matches!(
        TestProof::from_bytes(&bytes),
        Err(Error::Invalid {
            reason: "invalid mock proof payload",
            ..
        })
    ));
}

#[test]
fn real_format_payload_kinds_fail_closed() {
    for tag in [1u16, 2, 5] {
        let mut bytes = value_pcd(7).proof().to_bytes();
        bytes[10..12].copy_from_slice(&tag.to_le_bytes());
        assert!(matches!(
            TestProof::from_bytes(&bytes),
            Err(Error::Invalid {
                reason: "proof payload kind mismatch",
                ..
            })
        ));
    }
}

#[cfg(feature = "serde")]
mod serde_tests {
    use serde::de::{DeserializeSeed, value::SeqDeserializer};

    use super::*;

    #[test]
    fn serde_round_trip() {
        let proof = value_pcd(7).proof().clone();
        let json = serde_json::to_string(&proof).expect("serialize");
        let decoded: TestProof = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(decoded.to_bytes(), proof.to_bytes());

        let pcd = value_pcd(42);
        let json = serde_json::to_string(&pcd).expect("serialize");
        let decoded: TestPcd<ValueHeader> = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(decoded.data(), &ValueData { value: 42 });
    }

    #[test]
    fn serde_rejects_corruption() {
        let mut bytes = value_pcd(7).proof().to_bytes();
        bytes[0] ^= 1;
        let json = serde_json::to_string(&bytes).expect("serialize bytes");
        let error = match serde_json::from_str::<TestProof>(&json) {
            Ok(_) => panic!("corrupted bytes must fail to decode"),
            Err(error) => error,
        };
        assert!(error.to_string().contains("invalid proof magic"), "{error}");
    }

    struct EmptyWithHugeHint;

    impl<'de> serde::de::SeqAccess<'de> for EmptyWithHugeHint {
        type Error = serde::de::value::Error;

        fn next_element_seed<T: DeserializeSeed<'de>>(
            &mut self,
            _: T,
        ) -> core::result::Result<Option<T::Value>, Self::Error> {
            Ok(None)
        }

        fn size_hint(&self) -> Option<usize> {
            Some(usize::MAX)
        }
    }

    #[test]
    fn sequence_size_hint_does_not_control_allocation() {
        use serde::de::Visitor;
        struct P;
        impl<'de> Visitor<'de> for P {
            type Value = TestProof;
            fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str("a mock proof")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                seq: A,
            ) -> core::result::Result<Self::Value, A::Error> {
                use serde::Deserialize as _;
                TestProof::deserialize(serde::de::value::SeqAccessDeserializer::new(seq))
            }
        }
        let error = match P.visit_seq(EmptyWithHugeHint).map(|_| ()) {
            Ok(()) => panic!("empty input must fail to decode"),
            Err(error) => error,
        };
        assert!(error.to_string().contains("truncated"), "{error}");
    }

    #[test]
    fn sequence_buffer_stops_at_the_envelope_length() {
        use serde::{Deserialize as _, de::value::Error as DeError};
        // One byte beyond a mock proof's fixed length is refused.
        let input = value_pcd(7)
            .proof()
            .to_bytes()
            .into_iter()
            .chain(core::iter::repeat(0u8));
        let error = match TestProof::deserialize(SeqDeserializer::<_, DeError>::new(input)) {
            Ok(_) => panic!("overlong input must fail to decode"),
            Err(error) => error,
        };
        assert!(
            error.to_string().contains("exceeds its fixed length"),
            "{error}"
        );
    }
}
