//! Error types for the `.olean` reader.

use std::fmt;

/// A typed failure while reading a `.olean` file.
///
/// Malformed input must always produce an `Error`, never a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// File shorter than the fixed 88-byte header.
    HeaderTruncated { len: usize },
    /// First 5 bytes are not the `olean` magic.
    BadMagic { got: [u8; 5] },
    /// Header version we do not know how to read.
    UnsupportedVersion { version: u8 },
    /// A read past the end of the payload.
    Truncated { offset: u64, len: u64 },
    /// A stored pointer resolves outside the payload.
    PtrOutOfBounds { ptr: u64, resolved: i128 },
    /// A stored pointer is not 8-byte aligned.
    MisalignedPtr { ptr: u64 },
    /// A compacted object with a non-zero reference count.
    NonPersistentRc { offset: u64, rc: i32 },
    /// A tag that must not appear in a compacted region.
    ForbiddenTag { offset: u64, tag: u8 },
    /// Object whose declared extent is incoherent.
    BadObjectSize { offset: u64 },
    /// A string object violating size/terminator/UTF-8 laws.
    StringIntegrity { offset: u64, reason: String },
    /// A bignum object with an incoherent limb region.
    MpzIntegrity { offset: u64 },
    /// The root does not have the expected ModuleData shape.
    RootShape { reason: String },
    /// A semantic decode (Name, Import, pair, ...) hit an unexpected shape.
    DecodeShape { offset: u64, reason: String },
}

pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::HeaderTruncated { len } => {
                write!(f, "file too short for header: {len} bytes")
            }
            Error::BadMagic { got } => {
                write!(
                    f,
                    "bad magic: expected `olean`, got {}",
                    String::from_utf8_lossy(got)
                )
            }
            Error::UnsupportedVersion { version } => {
                write!(f, "unsupported olean version {version}")
            }
            Error::Truncated { offset, len } => {
                write!(f, "truncated: read at {offset} in {len}-byte payload")
            }
            Error::PtrOutOfBounds { ptr, resolved } => {
                write!(f, "pointer {ptr:#x} resolves out of bounds ({resolved})")
            }
            Error::MisalignedPtr { ptr } => write!(f, "pointer {ptr:#x} not 8-byte aligned"),
            Error::NonPersistentRc { offset, rc } => {
                write!(f, "object at {offset} has non-persistent rc {rc}")
            }
            Error::ForbiddenTag { offset, tag } => {
                write!(f, "forbidden object tag {tag} at {offset}")
            }
            Error::BadObjectSize { offset } => write!(f, "impossible object size at {offset}"),
            Error::StringIntegrity { offset, reason } => {
                write!(f, "string object at {offset}: {reason}")
            }
            Error::MpzIntegrity { offset } => write!(f, "bignum object at {offset} incoherent"),
            Error::RootShape { reason } => write!(f, "root shape: {reason}"),
            Error::DecodeShape { offset, reason } => {
                write!(f, "decode at {offset}: {reason}")
            }
        }
    }
}

impl std::error::Error for Error {}
