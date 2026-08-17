//! Object-graph walker: visits every reachable object from the root,
//! validating headers, extents, strings, and bignums.
//!
//! Iterative and budgeted: hostile input becomes a typed [`Error`], never a
//! stack fault or a runaway loop.

use std::collections::HashSet;

use crate::error::{Error, Result};
use crate::object::{Region, TAG_ARRAY, TAG_CLOSURE, TAG_MPZ, TAG_SCALAR_ARRAY, TAG_STRING, TAG_THUNK, TAG_TASK, TAG_REF};

/// Traversal budget: hard cap on visited objects.
#[derive(Debug, Clone, Copy)]
pub struct WalkBudget {
    pub max_objects: u64,
}

impl Default for WalkBudget {
    fn default() -> Self {
        // The largest pinned-toolchain module holds ~170k objects; 20M
        // leaves three orders of headroom while bounding hostile inputs.
        WalkBudget {
            max_objects: 20_000_000,
        }
    }
}

/// Counts of each object kind visited during a walk.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WalkReport {
    pub objects: u64,
    pub ctors: u64,
    pub arrays: u64,
    pub scalar_arrays: u64,
    pub strings: u64,
    pub mpz: u64,
    pub thunks: u64,
    pub tasks: u64,
    pub refs: u64,
    pub scalar_refs: u64,
}

/// Walk the whole object graph from the root, checking every pointer,
/// header, string, and bignum.
pub fn walk(region: &Region, budget: WalkBudget) -> Result<WalkReport> {
    let mut report = WalkReport::default();
    let mut seen: HashSet<u64> = HashSet::new();
    let mut stack: Vec<u64> = vec![region.root_ptr()?.0];
    while let Some(ptr) = stack.pop() {
        if ptr & 1 == 1 {
            report.scalar_refs += 1;
            continue;
        }
        let off = region.deref(ptr)?;
        if !seen.insert(off) {
            continue;
        }
        report.objects += 1;
        if report.objects > budget.max_objects {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!("budget exhausted after {} objects", report.objects),
            });
        }
        let hdr = region.obj_header(off)?;
        if hdr.is_ctor() {
            report.ctors += 1;
            let min = 8 + 8 * u64::from(hdr.other);
            let extent = u64::from(hdr.cs_sz);
            if extent < min || extent % 8 != 0 {
                return Err(Error::BadObjectSize { offset: off });
            }
            for i in 0..u64::from(hdr.other) {
                stack.push(region.ctor_field(off, i as u8)?.0);
            }
            // Validate the scalar tail bytes exist (no interpretation).
            region.read_bytes(off + min, extent - min)?;
        } else {
            match hdr.tag {
                TAG_ARRAY => {
                    report.arrays += 1;
                    let (size, _cap) = region.array_info(off)?;
                    for i in 0..size {
                        stack.push(region.array_elem(off, i)?.0);
                    }
                }
                TAG_SCALAR_ARRAY => {
                    report.scalar_arrays += 1;
                    let (size, capacity) = region.array_info(off)?;
                    // Allocation spans capacity * elem bytes; elem size is
                    // in `other`.
                    let elem = u64::from(hdr.other).max(1);
                    let extent = capacity
                        .checked_mul(elem)
                        .ok_or(Error::BadObjectSize { offset: off })?;
                    region.read_bytes(off + 24, extent)?;
                    let _ = size;
                }
                TAG_STRING => {
                    report.strings += 1;
                    region.read_string(off)?;
                }
                TAG_MPZ => {
                    report.mpz += 1;
                    // Validate shape without interpreting: read the struct.
                    region.read_bytes(off + 8, 16)?;
                }
                TAG_THUNK => {
                    report.thunks += 1;
                    for i in 0..2u64 {
                        let p = region.read_u64(off + 8 + 8 * i)?;
                        if p != 0 {
                            stack.push(p);
                        }
                    }
                }
                TAG_TASK => {
                    report.tasks += 1;
                    let p = region.read_u64(off + 8)?;
                    if p != 0 {
                        stack.push(p);
                    }
                }
                TAG_REF => {
                    report.refs += 1;
                    stack.push(region.read_u64(off + 8)?);
                }
                TAG_CLOSURE => {
                    return Err(Error::ForbiddenTag {
                        offset: off,
                        tag: hdr.tag,
                    });
                }
                _ => {
                    return Err(Error::ForbiddenTag {
                        offset: off,
                        tag: hdr.tag,
                    });
                }
            }
        }
    }
    Ok(report)
}
