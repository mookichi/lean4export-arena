//! Lean object model for compacted regions.
//!
//! Every 8-byte word in a compacted region is either:
//! - a **scalar** (`word & 1 == 1`): a boxed small value, `value = word >> 1`
//! - a **pointer** (`word & 1 == 0`): an offset, resolved against `base_addr`
//!
//! Pointed-to objects start with an 8-byte `lean_object` header:
//! ```c
//! typedef struct {
//!     int      m_rc;       // 4 bytes (0 in compacted regions)
//!     unsigned m_cs_sz:16; // 2 bytes (object size in compacted regions)
//!     unsigned m_other:8;  // 1 byte  (ctor: number of object fields)
//!     unsigned m_tag:8;    // 1 byte
//! } lean_object;
//! ```
//!
//! Tags >= 244 are runtime kinds (see `lean.h`); 0..243 are constructors.

use crate::error::{Error, Result};

/// Largest constructor tag: tags 0..=243 are constructors.
pub const TAG_MAX_CTOR: u8 = 243;
pub const TAG_PROMISE: u8 = 244;
pub const TAG_CLOSURE: u8 = 245;
pub const TAG_ARRAY: u8 = 246;
pub const TAG_STRUCT_ARRAY: u8 = 247;
pub const TAG_SCALAR_ARRAY: u8 = 248;
pub const TAG_STRING: u8 = 249;
pub const TAG_MPZ: u8 = 250;
pub const TAG_THUNK: u8 = 251;
pub const TAG_TASK: u8 = 252;
pub const TAG_REF: u8 = 253;
pub const TAG_EXTERNAL: u8 = 254;
pub const TAG_RESERVED: u8 = 255;

/// A resolved reference inside a compacted region.
///
/// `ptr` values are absolute addresses stored in the file; the reader
/// resolves them to file offsets against the payload's base address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ref(pub u64);

impl Ref {
    /// True if this word is a scalar (boxed small value), not a pointer.
    pub fn is_scalar(&self) -> bool {
        self.0 & 1 == 1
    }
    /// The boxed scalar value.
    pub fn scalar(&self) -> u64 {
        self.0 >> 1
    }
}

/// The 8-byte header common to every compacted object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ObjHeader {
    pub rc: i32,
    pub cs_sz: u16,
    pub other: u8,
    pub tag: u8,
}

impl ObjHeader {
    /// True for constructor tags.
    pub fn is_ctor(&self) -> bool {
        self.tag <= TAG_MAX_CTOR
    }
}

/// Reader over a `.olean` file (or a module's parts): the 88-byte
/// headers followed by the compacted region payloads.
///
/// Object pointers are stored as absolute addresses relative to the
/// part's `base_addr`; `deref` resolves them to offsets in the
/// concatenated byte buffer.
///
/// A module built with the module system is split into several part files
/// (`.olean`, `.olean.server`, `.olean.private`) that were compacted into
/// one shared in-memory region: all parts share a common base address
/// family and pointers may cross part boundaries. [`Region::from_parts`]
/// rebuilds that single virtual address space from the part files.
pub struct Region {
    /// All segment bytes concatenated, in part order.
    bytes: Vec<u8>,
    /// (base_addr, byte offset in `bytes`, byte length) per part.
    segments: Vec<(u64, u64, u64)>,
    /// Header length: each segment's root pointer is its first payload
    /// word, at `segment offset + payload_offset`.
    payload_offset: u64,
}

impl Region {
    /// Single-segment region: `bytes` is a whole `.olean` file,
    /// `base_addr` from its header, `payload_offset` the header length
    /// (88).
    pub fn new(bytes: &[u8], base_addr: u64, payload_offset: u64) -> Region {
        Region {
            bytes: bytes.to_vec(),
            segments: vec![(base_addr, 0, bytes.len() as u64)],
            payload_offset,
        }
    }

    /// Multi-part region: each part is the bytes of one part file plus the
    /// `base_addr` recorded in its own header. The parts are concatenated
    /// in order, forming the shared virtual address space the compactor
    /// produced.
    pub fn from_parts(parts: Vec<(Vec<u8>, u64)>, payload_offset: u64) -> Region {
        let mut bytes = Vec::new();
        let mut segments = Vec::with_capacity(parts.len());
        for (part, base_addr) in parts {
            let off = bytes.len() as u64;
            bytes.extend_from_slice(&part);
            segments.push((base_addr, off, part.len() as u64));
        }
        Region {
            bytes,
            segments,
            payload_offset,
        }
    }

    /// Number of segments (parts).
    pub fn num_segments(&self) -> usize {
        self.segments.len()
    }

    /// Resolve a stored pointer to an offset in the concatenated buffer.
    pub fn deref(&self, ptr: u64) -> Result<u64> {
        if ptr & 1 == 1 {
            return Err(Error::DecodeShape {
                offset: 0,
                reason: format!("deref of scalar {ptr:#x}"),
            });
        }
        for (base, off, len) in &self.segments {
            let base = *base;
            let len = *len;
            if base <= ptr && ptr < base + len {
                let abs = off + (ptr - base);
                if !abs.is_multiple_of(8) {
                    return Err(Error::MisalignedPtr { ptr });
                }
                return Ok(abs);
            }
        }
        Err(Error::PtrOutOfBounds {
            ptr,
            resolved: i128::MIN,
        })
    }

    /// Read a little-endian u64 at a file offset.
    pub fn read_u64(&self, off: u64) -> Result<u64> {
        let end = off
            .checked_add(8)
            .ok_or(Error::Truncated { offset: off, len: self.bytes.len() as u64 })?;
        if end > self.bytes.len() as u64 {
            return Err(Error::Truncated {
                offset: off,
                len: self.bytes.len() as u64,
            });
        }
        let mut b = [0u8; 8];
        b.copy_from_slice(&self.bytes[off as usize..end as usize]);
        Ok(u64::from_le_bytes(b))
    }

    /// Read `len` bytes at a file offset.
    pub fn read_bytes(&self, off: u64, len: u64) -> Result<&[u8]> {
        let end = off
            .checked_add(len)
            .ok_or(Error::Truncated { offset: off, len: self.bytes.len() as u64 })?;
        if end > self.bytes.len() as u64 {
            return Err(Error::Truncated {
                offset: off,
                len: self.bytes.len() as u64,
            });
        }
        Ok(&self.bytes[off as usize..end as usize])
    }

    /// Read the root pointer of segment 0: the first word of its payload.
    pub fn root_ptr(&self) -> Result<Ref> {
        self.root_ptr_at(0)
    }

    /// Read the root pointer of segment `seg`.
    pub fn root_ptr_at(&self, seg: usize) -> Result<Ref> {
        let (_, off, _) = self
            .segments
            .get(seg)
            .ok_or(Error::DecodeShape {
                offset: 0,
                reason: format!("segment index {seg} out of range"),
            })?;
        Ok(Ref(self.read_u64(off + self.payload_offset)?))
    }

    /// File offset of the start of the payload of segment 0.
    pub fn payload_offset(&self) -> u64 {
        self.payload_offset
    }

    /// Read an object header at a file offset.
    pub fn obj_header(&self, off: u64) -> Result<ObjHeader> {
        let word = self.read_u64(off)?;
        let rc = (word & 0xffff_ffff) as u32 as i32;
        if rc != 0 {
            return Err(Error::NonPersistentRc { offset: off, rc });
        }
        let packed = (word >> 32) as u32;
        let tag = (packed >> 24) as u8;
        let other = ((packed >> 16) & 0xff) as u8;
        let cs_sz = (packed & 0xffff) as u16;
        Ok(ObjHeader {
            rc,
            cs_sz,
            other,
            tag,
        })
    }

    /// Read object field `i` (a word) of a constructor at `off`.
    pub fn ctor_field(&self, off: u64, i: u8) -> Result<Ref> {
        if i == 255 {
            return Err(Error::DecodeShape {
                offset: off,
                reason: "ctor field index out of range".into(),
            });
        }
        Ok(Ref(self.read_u64(off + 8 + 8 * u64::from(i))?))
    }

    /// Read the scalar (non-pointer) fields of a constructor.
    ///
    /// Scalar fields follow the object fields. `obj_fields` is the number
    /// of object fields (the header's `other`), `scalar_bytes` the total
    /// number of scalar bytes.
    pub fn ctor_scalars(&self, off: u64, obj_fields: u8, scalar_bytes: u16) -> Result<&[u8]> {
        let start = off + 8 + 8 * u64::from(obj_fields);
        self.read_bytes(start, u64::from(scalar_bytes))
    }

    /// Read an array: header + size(8) + capacity(8) + data.
    pub fn array_info(&self, off: u64) -> Result<(u64, u64)> {
        let size = self.read_u64(off + 8)?;
        let capacity = self.read_u64(off + 16)?;
        if size > capacity {
            return Err(Error::DecodeShape {
                offset: off,
                reason: "array size > capacity".into(),
            });
        }
        Ok((size, capacity))
    }

    /// Read array element `i` as a word.
    pub fn array_elem(&self, off: u64, i: u64) -> Result<Ref> {
        Ok(Ref(self.read_u64(off + 24 + 8 * i)?))
    }

    /// Read a string object at `off` (tag 249).
    ///
    /// Layout: header(8) + byte_size(8, includes NUL) + capacity(8) +
    /// utf8_len(8) + data.
    pub fn read_string(&self, off: u64) -> Result<String> {
        let byte_size = self.read_u64(off + 8)?;
        if byte_size == 0 {
            return Err(Error::StringIntegrity {
                offset: off,
                reason: "zero byte size".into(),
            });
        }
        let bytes = self.read_bytes(off + 32, byte_size)?;
        // Lean strings are NUL-terminated UTF-8.
        if bytes.last() != Some(&0) {
            return Err(Error::StringIntegrity {
                offset: off,
                reason: "missing NUL terminator".into(),
            });
        }
        match std::str::from_utf8(&bytes[..bytes.len() - 1]) {
            Ok(s) => Ok(s.to_string()),
            Err(_) => Err(Error::StringIntegrity {
                offset: off,
                reason: "not valid UTF-8".into(),
            }),
        }
    }

    /// Read a bignum (mpz) object at `off` (tag 250), returning its decimal
    /// string representation.
    ///
    /// Two encodings exist (GMP and Lean-native), selected by header flags.
    pub fn read_mpz(&self, off: u64, uses_gmp: bool) -> Result<String> {
        if uses_gmp {
            self.read_mpz_gmp(off)
        } else {
            self.read_mpz_native(off)
        }
    }

    fn read_mpz_gmp(&self, off: u64) -> Result<String> {
        // mpz_object: header(8) + __mpz_struct.
        // __mpz_struct: _mp_alloc(4) + _mp_size(4) + _mp_d(8).
        // For small numbers GMP stores limbs inline in _mp_d (relocated);
        // the digits pointer is base_addr-relative.
        let alloc = self.read_u32(off + 8)?;
        let size = self.read_u32(off + 12)?;
        let d_ptr = self.read_u64(off + 16)?;
        // Limb size: 8 bytes on 64-bit. Allocated limbs live in the object
        // immediately after the struct (the compactor relocates _mp_d).
        let nlimbs = alloc as u64;
        let data_start = off + 24;
        let limb_bytes = self.read_bytes(data_start, nlimbs * 8)?;
        let mut limbs = Vec::with_capacity(nlimbs as usize);
        for i in 0..nlimbs as usize {
            let mut b = [0u8; 8];
            b.copy_from_slice(&limb_bytes[i * 8..i * 8 + 8]);
            limbs.push(u64::from_le_bytes(b));
        }
        // The GMP limb at _mp_d[0] may live inline; the compactor writes it
        // at data_start. Build the magnitude from limbs.
        let _ = d_ptr; // relocation already applied by the compactor
        let magnitude = big_from_limbs(&limbs);
        if size == 0 {
            Ok("0".into())
        } else if size > 0 {
            Ok(magnitude.to_string())
        } else {
            Ok(format!("-{magnitude}"))
        }
    }

    fn read_mpz_native(&self, off: u64) -> Result<String> {
        // Lean-native encoding (see runtime/mpz.h):
        //   struct mpz { bool m_sign; size_t m_size; mpn_digit * m_digits; };
        // layout: header(8) + m_sign(bool, +8) + pad + m_size(u64, +16)
        //         + m_digits(ptr, +24); digits copied inline at +32 by the
        //         compactor (compact.cpp `insert_mpz`), with `m_digits`
        //         relocated to point at them.
        let sign = self.read_u32(off + 8)?; // bool: 0 = positive, 1 = negative
        let size = self.read_u64(off + 16)?;
        let digits_ptr = self.read_u64(off + 24)?;
        let _ = digits_ptr;
        let n = size;
        let data_start = off + 32;
        let limb_bytes = self.read_bytes(data_start, n.checked_mul(8).ok_or(Error::BadObjectSize { offset: off })?)?;
        let mut limbs = Vec::with_capacity(n as usize);
        for i in 0..n as usize {
            let mut b = [0u8; 8];
            b.copy_from_slice(&limb_bytes[i * 8..i * 8 + 8]);
            limbs.push(u64::from_le_bytes(b));
        }
        let magnitude = big_from_limbs(&limbs);
        if n == 0 || (n == 1 && limbs[0] == 0) {
            Ok("0".into())
        } else if sign == 0 {
            Ok(magnitude.to_string())
        } else {
            Ok(format!("-{magnitude}"))
        }
    }

    fn read_u32(&self, off: u64) -> Result<u32> {
        let end = off
            .checked_add(4)
            .ok_or(Error::Truncated { offset: off, len: self.bytes.len() as u64 })?;
        if end > self.bytes.len() as u64 {
            return Err(Error::Truncated {
                offset: off,
                len: self.bytes.len() as u64,
            });
        }
        let mut b = [0u8; 4];
        b.copy_from_slice(&self.bytes[off as usize..end as usize]);
        Ok(u32::from_le_bytes(b))
    }
}

/// Build a decimal string from little-endian 64-bit limbs.
fn big_from_limbs(limbs: &[u64]) -> num_bigint_fallback::BigInt {
    num_bigint_fallback::BigInt::from_le_limbs(limbs)
}

/// Minimal big-integer fallback so the crate has zero dependencies.
mod num_bigint_fallback {
    /// A small arbitrary-precision unsigned integer as decimal digits.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct BigInt {
        /// Little-endian 64-bit limbs.
        limbs: Vec<u64>,
    }

    impl std::fmt::Display for BigInt {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&self.as_decimal())
        }
    }

    impl BigInt {
        pub fn from_le_limbs(limbs: &[u64]) -> BigInt {
            let mut ls = limbs.to_vec();
            while ls.len() > 1 && *ls.last().unwrap() == 0 {
                ls.pop();
            }
            BigInt { limbs: ls }
        }

        fn as_decimal(&self) -> String {
            if self.limbs.is_empty() || (self.limbs.len() == 1 && self.limbs[0] == 0) {
                return "0".to_string();
            }
            // Binary -> decimal by reading the limb bits from most significant
            // to least: digits = digits * 2 + bit. O(n^2) but fine for the
            // numbers that appear in practice.
            let mut digits: Vec<u8> = vec![0];
            for &limb in self.limbs.iter().rev() {
                for bit in (0..64).rev() {
                    // digits *= 2
                    let mut carry = 0u8;
                    for d in digits.iter_mut() {
                        let v = *d * 2 + carry;
                        *d = v % 10;
                        carry = v / 10;
                    }
                    if carry > 0 {
                        digits.push(carry);
                    }
                    // digits += bit
                    if (limb >> bit) & 1 == 1 {
                        add_one(&mut digits);
                    }
                }
            }
            // Remove leading zeros (digits are little-endian).
            while digits.len() > 1 && *digits.last().unwrap() == 0 {
                digits.pop();
            }
            digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
        }
    }

    fn add_one(digits: &mut Vec<u8>) {
        let mut i = 0;
        loop {
            if i >= digits.len() {
                digits.push(0);
            }
            if digits[i] < 9 {
                digits[i] += 1;
                return;
            }
            digits[i] = 0;
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bigint_basic() {
        assert_eq!(num_bigint_fallback::BigInt::from_le_limbs(&[0]).to_string(), "0");
        assert_eq!(num_bigint_fallback::BigInt::from_le_limbs(&[42]).to_string(), "42");
        // 2^64 = 18446744073709551616
        assert_eq!(
            num_bigint_fallback::BigInt::from_le_limbs(&[0, 1]).to_string(),
            "18446744073709551616"
        );
    }
}
