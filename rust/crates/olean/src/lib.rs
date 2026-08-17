//! Reader for Lean 4 `.olean` files.
//!
//! A `.olean` file is a compacted region: the in-memory layout of a Lean
//! object graph, serialized as 64-bit words.  Pointers are stored as
//! absolute addresses relative to a `base_addr` recorded in the file header.
//! See `OLEAN_FORMAT.md` (repo root) for the full layout documentation.
//!
//! ```no_run
//! use olean::{OLean, value};
//! let bytes = std::fs::read("file.olean").unwrap();
//! let olean = OLean::parse(&bytes).unwrap();
//! let dm = olean.decode().unwrap();
//! # let _: &value::ModuleData = &dm.data;
//! # let _: &value::Arenas = &dm.arenas;
//! ```

pub mod decode;
pub mod error;
pub mod export;
pub mod header;
pub mod object;
pub mod region;
pub mod value;

pub use decode::Decoder;
pub use error::{Error, Result};
pub use header::{Header, MAGIC};
pub use object::Region;

use crate::value::ModuleData;

/// A parsed `.olean` file (or a module's parts): header plus a reader over
/// the compacted payload(s).
pub struct OLean {
    pub header: Header,
    region: Region,
}

/// The result of decoding a module: the `ModuleData` plus the arena set
/// its `Name`/`Level`/`Expr` handles refer into (the handles are only
/// meaningful while the arenas live).
pub struct DecodedModule {
    pub data: ModuleData,
    pub arenas: crate::value::Arenas,
}

impl OLean {
    /// Parse the header and set up the region reader. `bytes` must be the
    /// complete contents of a single `.olean` file.
    pub fn parse(bytes: &[u8]) -> Result<OLean> {
        let header = Header::parse(bytes)?;
        let region = Region::new(bytes, header.base_addr, header::HEADER_LEN as u64);
        Ok(OLean { header, region })
    }

    /// Parse a module's part files (`.olean`, `.olean.server`,
    /// `.olean.private`, in that order) as one shared virtual address
    /// space. Each part contributes a segment; pointers may cross part
    /// boundaries. Segment 0 is the exported part, and the private part is
    /// the last segment.
    pub fn parse_parts(parts: Vec<Vec<u8>>) -> Result<OLean> {
        if parts.is_empty() {
            return Err(Error::DecodeShape {
                offset: 0,
                reason: "no module parts to parse".into(),
            });
        }
        let header = Header::parse(&parts[0])?;
        let mut segments = Vec::with_capacity(parts.len());
        for part in parts {
            let h = Header::parse(&part)?;
            segments.push((part, h.base_addr));
        }
        let region = Region::from_parts(segments, header::HEADER_LEN as u64);
        Ok(OLean { header, region })
    }

    /// Decode the root `ModuleData` object of segment 0 (the exported part
    /// of a multi-part module, or the only part of a plain module),
    /// interning into a fresh arena set.
    pub fn decode(&self) -> Result<DecodedModule> {
        let mut arenas = crate::value::Arenas::new();
        let data = self.decode_with(0, true, &mut arenas)?;
        Ok(DecodedModule { data, arenas })
    }

    /// Decode the root `ModuleData` object of segment `part` into `arenas`.
    /// The borrows are tied together so the decoder may hold both the
    /// region and the arenas for the duration of the call.
    pub fn decode_part<'a>(&'a self, part: usize, arenas: &'a mut crate::value::Arenas) -> Result<ModuleData> {
        Decoder::new(&self.region, self.header.uses_gmp(), arenas).module_data_part(part)
    }

    /// Decode only `isModule`, imports and constants of segment `part`
    /// (skipping the large persistent-extension state) into `arenas`.
    pub fn decode_part_lite<'a>(&'a self, part: usize, arenas: &'a mut crate::value::Arenas) -> Result<ModuleData> {
        Decoder::new(&self.region, self.header.uses_gmp(), arenas).module_data_lite(part)
    }

    /// Internal: decode segment `part` with the given `full` flag into
    /// `arenas`.
    fn decode_with<'a>(
        &'a self,
        part: usize,
        full: bool,
        arenas: &'a mut crate::value::Arenas,
    ) -> Result<ModuleData> {
        let mut d = Decoder::new(&self.region, self.header.uses_gmp(), arenas);
        if full {
            d.module_data_part(part)
        } else {
            d.module_data_lite(part)
        }
    }

    /// The region reader (for lower-level access).
    pub fn region(&self) -> &Region {
        &self.region
    }
}
