//! Per-file MPZ scan: walk each .olean part from its own root, counting
//! objects and dumping MPZ raw fields (4-byte vs 8-byte digit decode).
use olean::object::{Region, TAG_MPZ};

fn main() {
    let files: Vec<String> = std::env::args().skip(1).collect();
    let mut total_mpz = 0u64;
    for f in &files {
        let bytes = std::fs::read(f).unwrap();
        let hdr = match olean::Header::parse(&bytes) {
            Ok(h) => h,
            Err(_) => { println!("{f}: bad header"); continue; }
        };
        let region = Region::new(&bytes, hdr.base_addr, 88);
        let mut stack = vec![region.root_ptr().unwrap().0];
        let mut seen = std::collections::HashSet::new();
        let mut mpz_offsets = Vec::new();
        let mut total = 0u64;
        let mut err = None;
        'walk: while let Some(ptr) = stack.pop() {
            if ptr & 1 == 1 { continue; }
            let off = match region.deref(ptr) {
                Ok(o) => o,
                Err(e) => { err = Some(format!("deref {ptr:#x}: {e}")); break 'walk; }
            };
            if !seen.insert(off) { continue; }
            total += 1;
            let hdr = match region.obj_header(off) {
                Ok(h) => h,
                Err(e) => { err = Some(format!("hdr @{off}: {e}")); break 'walk; }
            };
            if hdr.is_ctor() {
                for i in 0..u64::from(hdr.other) {
                    stack.push(region.ctor_field(off, i as u8).unwrap().0);
                }
            } else if hdr.tag == TAG_MPZ {
                mpz_offsets.push(off);
            } else if hdr.tag == olean::object::TAG_ARRAY {
                let (size, _) = region.array_info(off).unwrap();
                for i in 0..size {
                    stack.push(region.array_elem(off, i).unwrap().0);
                }
            } else if hdr.tag == olean::object::TAG_STRING {
                let _ = region.read_string(off).unwrap();
            }
        }
        let fname = std::path::Path::new(f).file_name().unwrap().to_str().unwrap();
        if !mpz_offsets.is_empty() {
            println!("== {fname}: objects={total} mpz={} {}", mpz_offsets.len(),
                     err.as_ref().map(|e| format!("(stopped: {e})")).unwrap_or_default());
            for off in &mpz_offsets {
                let h = region.obj_header(*off).unwrap();
                let w8 = region.read_u64(*off + 8).unwrap();
                let w16 = region.read_u64(*off + 16).unwrap();
                let w24 = region.read_u64(*off + 24).unwrap();
                println!("   MPZ @ {off}: other={} cs_sz={} w8={w8:#x} w16={w16:#x} w24={w24:#x}", h.other, h.cs_sz);
                let raw = region.read_bytes(*off, 64).unwrap();
                let hex: Vec<String> = raw.iter().map(|b| format!("{b:02x}")).collect();
                println!("     header+32B: {}", hex[..40].join(" "));
                let n = w16 as usize;
                if n > 0 && n < 1_000_000 {
                    let b4 = region.read_bytes(*off + 32, (n * 4) as u64).unwrap();
                    let mut v4 = 0u128;
                    for i in (0..n).rev() {
                        v4 = (v4 << 32) | u32::from_le_bytes(b4[i*4..i*4+4].try_into().unwrap()) as u128;
                    }
                    println!("     4-byte digits: {v4}");
                    total_mpz += 1;
                } else {
                    println!("     (size out of range)");
                }
            }
        }
    }
    println!("TOTAL mpz objects with size>=1: {total_mpz}");
}
