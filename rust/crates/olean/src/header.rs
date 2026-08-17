//! The fixed 88-byte `.olean` header.
//!
//! Layout (packed, little-endian):
//! | offset | size | content                          |
//! |--------|------|----------------------------------|
//! | 0      | 5    | magic `"olean"`                  |
//! | 5      | 1    | version (currently 2)            |
//! | 6      | 1    | flags (bit 0: GMP bignums)       |
//! | 7      | 33   | Lean version string, NUL padded  |
//! | 40     | 40   | build githash, NUL padded        |
//! | 80     | 8    | base_addr                        |
//!
//! See `src/library/module.cpp` (struct `olean_header`) in Lean 4.

use crate::error::{Error, Result};

pub const MAGIC: [u8; 5] = *b"olean";
pub const HEADER_LEN: usize = 88;
/// Version 2 is the only version produced by v4.x toolchains so far.
pub const SUPPORTED_VERSION: u8 = 2;
/// Bit 0 of `flags`: persisted bignums use GMP encoding.
pub const FLAG_GMP: u8 = 0b1;

/// Parsed `.olean` file header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Header {
    pub version: u8,
    pub flags: u8,
    pub lean_version: String,
    pub githash: String,
    pub base_addr: u64,
}

impl Header {
    /// Parse the header from the first `HEADER_LEN` bytes of a file.
    pub fn parse(bytes: &[u8]) -> Result<Header> {
        if bytes.len() < HEADER_LEN {
            return Err(Error::HeaderTruncated { len: bytes.len() });
        }
        let magic: [u8; 5] = bytes[0..5].try_into().unwrap();
        if magic != MAGIC {
            return Err(Error::BadMagic { got: magic });
        }
        let version = bytes[5];
        if version != SUPPORTED_VERSION {
            return Err(Error::UnsupportedVersion { version });
        }
        let flags = bytes[6];
        let lean_version = read_cstr(&bytes[7..40]);
        let githash = read_cstr(&bytes[40..80]);
        let base_addr = u64::from_le_bytes(bytes[80..88].try_into().unwrap());
        Ok(Header {
            version,
            flags,
            lean_version,
            githash,
            base_addr,
        })
    }

    /// Whether the file's bignums use GMP encoding.
    pub fn uses_gmp(&self) -> bool {
        self.flags & FLAG_GMP != 0
    }
}

/// Read a NUL-terminated string from a fixed-size field.
fn read_cstr(field: &[u8]) -> String {
    let end = field.iter().position(|&b| b == 0).unwrap_or(field.len());
    String::from_utf8_lossy(&field[..end]).into_owned()
}
