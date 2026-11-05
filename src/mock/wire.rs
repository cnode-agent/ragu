//! Canonical byte encoding for mock proofs and proof-carrying data.
//!
//! This mirrors `ragu_pcd::wire` (added in #875) for the mock: [`Proof`] and
//! [`Pcd`] reach bytes through `to_bytes` / `from_bytes` with a 28-byte
//! versioned envelope, and the optional `serde` adapters carry the same
//! bytes. The mock shares the real format's magic, envelope layout and
//! envelope version, and occupies its own payload kinds (3 and 4), so a mock
//! encoding fed to a real decoder — or the reverse — fails closed on the
//! payload kind rather than being reinterpreted.
//!
//! # Envelope
//!
//! | Offset | Size | Meaning |
//! | --- | --- | --- |
//! | 0 | 8 | Magic: `RAGUPCD` and a NUL |
//! | 8 | 2 | Envelope version: 3 |
//! | 10 | 2 | Payload kind: 3 mock proof, 4 mock PCD |
//! | 12 | 2 | Schema version of that payload kind: 1 |
//! | 14 | 2 | Protocol version: 1 (the mock binding hashes) |
//! | 16 | 4 | Rank: always 0; the mock has no rank axis |
//! | 20 | 8 | Data length in bytes: 0 for a proof; the header data's length for a PCD |
//!
//! A mock proof's payload is its compressed serialization. A mock PCD's
//! payload is its proof, the header suffix, the data length, and the header
//! data as opaque bytes supplied by the header's [`WireHeader`] codec.
//!
//! Decoding checks the envelope, then the exact length the payload implies,
//! before decoding any of it. A proof's internal binding is checked as the
//! compressed serialization checks it. A PCD's header suffix must match the
//! receiving type's [`Header::SUFFIX`]. As in the real format, this
//! establishes representation, not proof validity: check the data against
//! the expected application with [`Application::verify`] before accepting a
//! decoded PCD.
//!
//! # Versions
//!
//! The schema version fixes a payload's field order and codecs; the envelope
//! version fixes the layout above; the protocol version follows the mock's
//! hashing semantics. Changing any of them means a new version and explicit
//! dispatch in the decoder — never silent reinterpretation.
//!
//! [`Application::verify`]: crate::Application::verify

use alloc::vec::Vec;

use super::{
    header::{Header, Suffix},
    proof::{Pcd, Proof},
};

#[cfg(feature = "serde")]
mod serde;

/// The envelope prepended to every encoding, in bytes.
pub(crate) const ENVELOPE_SIZE: usize = 28;

const MAGIC: &[u8; 8] = b"RAGUPCD\0";
// Matches `ragu_pcd::wire`: one layout, one version namespace.
const ENVELOPE_VERSION: u16 = 3;
// Follows the mock's hashing semantics: the header, witness, binding and
// rerandomization digests in `mock::proof`.
const PROTOCOL_VERSION: u16 = 1;
const MOCK_PROOF_SCHEMA_VERSION: u16 = 1;
const MOCK_PCD_SCHEMA_VERSION: u16 = 1;
/// Largest header data admitted by the byte format, in bytes.
const MAX_PCD_DATA: u64 = 1 << 24;
/// Header suffix and data length.
const PCD_HEAD_LEN: usize = 8 + 8;

/// Each mock representation has its own payload kind and schema version,
/// disjoint from the real format's kinds 1 and 2.
#[derive(Clone, Copy)]
enum PayloadKind {
    MockProof,
    MockPcd,
}

impl PayloadKind {
    fn tag(self) -> u16 {
        match self {
            Self::MockProof => 3,
            Self::MockPcd => 4,
        }
    }

    fn schema_version(self) -> u16 {
        match self {
            Self::MockProof => MOCK_PROOF_SCHEMA_VERSION,
            Self::MockPcd => MOCK_PCD_SCHEMA_VERSION,
        }
    }
}

/// A malformed byte encoding, or a value that has none.
///
/// Mirrors `ragu_pcd::wire::Error`. Offending byte slices borrow the input
/// rather than copying hostile data. New versions of the format may add
/// variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error<'a> {
    /// The value to encode has no encoding.
    Unencodable,
    /// The input is not the exact encoded length of the expected value.
    Length {
        /// The length every valid encoding has.
        expected: usize,
        /// The length received.
        actual: usize,
    },
    /// The next value extends beyond the input.
    Truncated {
        /// Start of the missing value.
        offset: usize,
        /// Number of bytes requested.
        requested: usize,
        /// Available bytes at that position.
        bytes: &'a [u8],
    },
    /// Bytes are not a canonical representation of the expected value.
    Invalid {
        /// Start of the offending value.
        offset: usize,
        /// The offending bytes.
        bytes: &'a [u8],
        /// Explanation of the rejected representation.
        reason: &'static str,
    },
}

impl core::fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Unencodable => f.write_str("the value has no encoding"),
            Self::Length { expected, actual } => {
                write!(
                    f,
                    "incorrect encoded length: expected {expected} bytes, got {actual}"
                )
            }
            Self::Truncated {
                offset,
                requested,
                bytes,
            } => write!(
                f,
                "truncated input at byte {offset}: need {requested} bytes, have {}",
                bytes.len()
            ),
            Self::Invalid { offset, reason, .. } => {
                write!(f, "invalid encoding at byte {offset}: {reason}")
            }
        }
    }
}
impl core::error::Error for Error<'_> {}

fn write_envelope(payload: PayloadKind, data_len: u64, bytes: &mut Vec<u8>) {
    bytes.extend_from_slice(MAGIC);
    for word in [
        ENVELOPE_VERSION,
        payload.tag(),
        payload.schema_version(),
        PROTOCOL_VERSION,
    ] {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    // The mock has no rank axis.
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes.extend_from_slice(&data_len.to_le_bytes());
}

/// Checks the envelope and bounds its dimensions before any payload is read.
fn open<'a>(bytes: &'a [u8], payload: PayloadKind) -> Result<(&'a [u8], u64), Error<'a>> {
    if bytes.len() < ENVELOPE_SIZE {
        return Err(Error::Truncated {
            offset: 0,
            requested: ENVELOPE_SIZE,
            bytes,
        });
    }
    let envelope = &bytes[..ENVELOPE_SIZE];
    let mut known = Vec::with_capacity(ENVELOPE_SIZE);
    write_envelope(payload, 0, &mut known);
    // Report the exact rejected component. Every check precedes payload decoding.
    for (start, end, reason) in [
        (0, 8, "invalid proof magic"),
        (8, 10, "unsupported proof envelope version"),
        (10, 12, "proof payload kind mismatch"),
        (12, 14, "unsupported proof schema version"),
        (14, 16, "unsupported proof protocol version"),
    ] {
        if envelope[start..end] != known[start..end] {
            return Err(Error::Invalid {
                offset: start,
                bytes: &envelope[start..end],
                reason,
            });
        }
    }
    let rank_bytes = &envelope[16..20];
    if rank_bytes != [0; 4] {
        return Err(Error::Invalid {
            offset: 16,
            bytes: rank_bytes,
            reason: "mock proofs carry no rank",
        });
    }
    let data_len_bytes = &envelope[20..28];
    let data_len = u64::from_le_bytes(data_len_bytes.try_into().expect("8-byte length"));
    let over_limit = match payload {
        PayloadKind::MockProof => data_len != 0,
        PayloadKind::MockPcd => data_len > MAX_PCD_DATA,
    };
    if over_limit {
        return Err(Error::Invalid {
            offset: 20,
            bytes: data_len_bytes,
            reason: "mock data length exceeds the limit",
        });
    }
    Ok((&bytes[ENVELOPE_SIZE..], data_len))
}

impl Proof {
    /// Encodes this proof with its version envelope.
    ///
    /// Unlike [`Proof::serialize`], which fills the fixed-size buffer the
    /// real proof's compressed encoding occupies, this is the versioned wire
    /// format. It checks representation, not proof validity.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::encoded_len());
        write_envelope(PayloadKind::MockProof, 0, &mut bytes);
        bytes.extend_from_slice(self.serialize().as_ref());
        bytes
    }

    /// The exact encoded length of a mock proof, envelope included. Bound
    /// transport input to this size before buffering it.
    #[must_use]
    pub const fn encoded_len() -> usize {
        ENVELOPE_SIZE + super::proof::PROOF_SIZE_COMPRESSED
    }

    /// Decodes one mock proof, checking the envelope, the exact length and
    /// the internal binding as the compressed serialization checks it.
    ///
    /// Attach the accompanying output data with [`Proof::carry`] and check it
    /// against the expected application with
    /// [`Application::verify`](crate::Application::verify) before accepting
    /// the proof or using it as a child.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error<'_>> {
        let (payload, _) = open(bytes, PayloadKind::MockProof)?;
        let expected = Self::encoded_len();
        if bytes.len() != expected {
            return Err(Error::Length {
                expected,
                actual: bytes.len(),
            });
        }
        let payload: &[u8; super::proof::PROOF_SIZE_COMPRESSED] =
            payload.try_into().expect("payload length checked");
        Self::try_from(payload).map_err(|_| Error::Invalid {
            offset: ENVELOPE_SIZE,
            bytes: payload,
            reason: "invalid mock proof payload",
        })
    }

    /// The exact length of a mock proof encoding, checked as
    /// [`from_bytes`](Self::from_bytes) checks it.
    #[cfg(any(test, feature = "serde"))]
    fn framed_len(bytes: &[u8]) -> Result<usize, Error<'_>> {
        open(bytes, PayloadKind::MockProof)?;
        Ok(Self::encoded_len())
    }
}

/// A [`Header`] whose data round-trips through the wire format.
///
/// The header data travels as opaque bytes supplied by this codec; the
/// envelope bounds its length and decoding checks the suffix against the
/// receiving type. Implementations must accept exactly the values their
/// `data_to_bytes` can produce, and reject every other input.
pub trait WireHeader: Header {
    /// Encodes header data as opaque bytes.
    fn data_to_bytes(data: &Self::Data) -> Vec<u8>;

    /// Rebuilds header data from its bytes, or `None` if they are not a
    /// value of this header.
    fn data_from_bytes(bytes: &[u8]) -> Option<Self::Data>;
}

impl WireHeader for () {
    fn data_to_bytes(_: &()) -> Vec<u8> {
        Vec::new()
    }

    fn data_from_bytes(bytes: &[u8]) -> Option<Self::Data> {
        bytes.is_empty().then_some(())
    }
}

impl<H: WireHeader> Pcd<H> {
    /// Encodes this PCD with its version envelope: the proof, the header
    /// suffix, and the header data as opaque bytes.
    ///
    /// This checks representation, not proof validity.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Unencodable`] if the data exceeds the format's length
    /// limit.
    pub fn to_bytes(&self) -> Result<Vec<u8>, Error<'static>> {
        let data = H::data_to_bytes(&self.data);
        if data.len() as u64 > MAX_PCD_DATA {
            return Err(Error::Unencodable);
        }
        let mut bytes = Vec::with_capacity(
            ENVELOPE_SIZE + super::proof::PROOF_SIZE_COMPRESSED + PCD_HEAD_LEN + data.len(),
        );
        write_envelope(PayloadKind::MockPcd, data.len() as u64, &mut bytes);
        bytes.extend_from_slice(self.proof.serialize().as_ref());
        bytes.extend_from_slice(&H::SUFFIX.get().to_le_bytes());
        bytes.extend_from_slice(&(data.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&data);
        Ok(bytes)
    }

    /// Decodes one mock PCD, checking the envelope, the exact length the data
    /// length implies, the proof payload as the compressed serialization
    /// checks it, the header suffix against `H`, and the data through `H`'s
    /// codec.
    ///
    /// This establishes representation, not proof validity: check the data
    /// against the expected application with
    /// [`Application::verify`](crate::Application::verify) before accepting
    /// the decoded PCD.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error<'_>> {
        let (payload, data_len) = open(bytes, PayloadKind::MockPcd)?;
        let proof_len = super::proof::PROOF_SIZE_COMPRESSED;
        let expected = ENVELOPE_SIZE + proof_len + PCD_HEAD_LEN + data_len as usize;
        if bytes.len() != expected {
            return Err(Error::Length {
                expected,
                actual: bytes.len(),
            });
        }
        let (proof_bytes, rest) = payload.split_at(proof_len);
        let proof_bytes: &[u8; super::proof::PROOF_SIZE_COMPRESSED] =
            proof_bytes.try_into().expect("payload length checked");
        let proof = Proof::try_from(proof_bytes).map_err(|_| Error::Invalid {
            offset: ENVELOPE_SIZE,
            bytes: proof_bytes,
            reason: "invalid mock proof payload",
        })?;

        let suffix_offset = ENVELOPE_SIZE + proof_len;
        let suffix = u64::from_le_bytes(rest[..8].try_into().expect("8-byte suffix"));
        let suffix = Suffix::from_value(suffix).ok_or(Error::Invalid {
            offset: suffix_offset,
            bytes: &rest[..8],
            reason: "invalid header suffix",
        })?;
        if suffix != H::SUFFIX {
            return Err(Error::Invalid {
                offset: suffix_offset,
                bytes: &rest[..8],
                reason: "mock PCD header suffix mismatch",
            });
        }
        let length_offset = suffix_offset + 8;
        let declared = u64::from_le_bytes(rest[8..16].try_into().expect("8-byte length"));
        if declared != data_len {
            return Err(Error::Invalid {
                offset: length_offset,
                bytes: &rest[8..16],
                reason: "mock PCD data length does not match the envelope",
            });
        }
        let data_bytes = &rest[16..];
        let data = H::data_from_bytes(data_bytes).ok_or(Error::Invalid {
            offset: length_offset + 8,
            bytes: data_bytes,
            reason: "header data rejected by its header",
        })?;
        Ok(proof.carry::<H>(data))
    }

    /// The exact length of the encoding whose envelope `bytes` begins with,
    /// checked as [`from_bytes`](Self::from_bytes) checks it.
    #[cfg(any(test, feature = "serde"))]
    fn framed_len(bytes: &[u8]) -> Result<usize, Error<'_>> {
        let (_, data_len) = open(bytes, PayloadKind::MockPcd)?;
        Ok(ENVELOPE_SIZE + super::proof::PROOF_SIZE_COMPRESSED + PCD_HEAD_LEN + data_len as usize)
    }
}
