//! Decoding of the compacted-region object graph into the [`crate::value`]
//! data model.
//!
//! All layouts here were verified empirically against `.olean` files built
//! with Lean 4 v4.30.0 and cross-checked against Lean's own
//! `readModuleData` (see `OLEAN_FORMAT.md` in the repo root).
//!
//! Highlights:
//! - scalar fields (Bool, small enums) follow the object fields of a ctor,
//!   packed byte-wise into 8-byte slots in field order;
//! - `Nat` fields are boxed scalars (`v << 1 | 1`) or MPZ objects;
//! - `lam`/`forallE`/`letE` carry a runtime data word plus a byte for
//!   `binderInfo`/`nondep` in their scalar section.
//!
//! Decoded `Name`/`Level`/`Expr` values are interned into the shared
//! [`Arenas`] passed to the decoder, so structurally equal values (the
//! region shares subobjects heavily) occupy a single node and index
//! equality is structural equality.

use std::collections::HashMap;

use crate::error::{Error, Result};
use crate::object::{ObjHeader, Region, TAG_ARRAY, TAG_MPZ, TAG_STRING};
use crate::value::{
    Arenas, AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
    DefinitionSafety, DefinitionVal, Expr, ExprNode, Import, InductiveVal, Level, LevelNode,
    Literal, ModuleData, Name, NameKey, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
    ReducibilityHints, TheoremVal,
};

/// Hard cap on recursion depth while decoding (a `.olean` is a DAG; deep
/// expressions occur in practice with a few thousand nested binders).
pub const MAX_DEPTH: u32 = 100_000;

/// A decoded word: either a boxed scalar value or a pointer to an object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Slot {
    Scalar(u64),
    Ptr(u64),
}

/// Decoder over a compacted region, memoizing decoded values by object
/// offset (the region shares subobjects heavily, and Lean reuses the same
/// `Expr`/`Name`/`Level` values).
pub struct Decoder<'r> {
    region: &'r Region,
    uses_gmp: bool,
    depth: u32,
    /// The shared arena set every decoded value is interned into.
    arenas: &'r mut Arenas,
    /// Decoded names by object offset (`Name` handles; the arena keeps the
    /// nodes alive and dedups identical content).
    names: HashMap<u64, Name>,
    levels: HashMap<u64, Level>,
    /// Decoded expressions by object offset (`Expr` handles).
    exprs: HashMap<u64, Expr>,
    consts: HashMap<u64, ConstantInfo>,
}

impl<'r> Decoder<'r> {
    pub fn new(region: &'r Region, uses_gmp: bool, arenas: &'r mut Arenas) -> Decoder<'r> {
        Decoder {
            region,
            uses_gmp,
            depth: 0,
            arenas,
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            consts: HashMap::new(),
        }
    }

    // ---- primitives -------------------------------------------------------

    fn enter(&mut self) -> Result<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(Error::DecodeShape {
                offset: 0,
                reason: format!("decoder recursion limit ({MAX_DEPTH}) exceeded"),
            });
        }
        Ok(())
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Classify a stored word.
    fn slot(&self, w: u64) -> Result<Slot> {
        if w & 1 == 1 {
            Ok(Slot::Scalar(w >> 1))
        } else {
            Ok(Slot::Ptr(self.region.deref(w)?))
        }
    }

    /// Expect a boxed scalar or a small MPZ at `w`, returning a `u64`.
    fn nat_u64(&mut self, w: u64) -> Result<u64> {
        match self.slot(w)? {
            Slot::Scalar(v) => Ok(v),
            Slot::Ptr(off) => {
                let hdr = self.region.obj_header(off)?;
                if hdr.tag != TAG_MPZ {
                    return Err(Error::DecodeShape {
                        offset: off,
                        reason: format!("expected MPZ for Nat, got tag {}", hdr.tag),
                    });
                }
                let s = self.region.read_mpz(off, self.uses_gmp)?;
                s.parse::<u64>().map_err(|_| Error::DecodeShape {
                    offset: off,
                    reason: format!("Nat value {s} does not fit in u64"),
                })
            }
        }
    }

    /// Expect a boxed scalar or MPZ at `w`, returning its decimal string.
    fn nat_str(&mut self, w: u64) -> Result<String> {
        match self.slot(w)? {
            Slot::Scalar(v) => Ok(v.to_string()),
            Slot::Ptr(off) => {
                let hdr = self.region.obj_header(off)?;
                if hdr.tag != TAG_MPZ {
                    return Err(Error::DecodeShape {
                        offset: off,
                        reason: format!("expected MPZ for Nat, got tag {}", hdr.tag),
                    });
                }
                self.region.read_mpz(off, self.uses_gmp)
            }
        }
    }

    fn string(&mut self, w: u64) -> Result<String> {
        match self.slot(w)? {
            Slot::Scalar(v) => Err(Error::DecodeShape {
                offset: 0,
                reason: format!("expected String object, got scalar {v}"),
            }),
            Slot::Ptr(off) => {
                let hdr = self.region.obj_header(off)?;
                if hdr.tag != TAG_STRING {
                    return Err(Error::DecodeShape {
                        offset: off,
                        reason: format!("expected String, got tag {}", hdr.tag),
                    });
                }
                self.region.read_string(off)
            }
        }
    }

    /// The scalar-section byte at `byte_index` of the ctor at `off`.
    fn scalar_byte(&self, off: u64, hdr: ObjHeader, byte_index: u64) -> Result<u8> {
        let scalar_bytes = hdr.cs_sz as u64 - 8 - 8 * u64::from(hdr.other);
        if byte_index >= scalar_bytes {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!(
                    "scalar byte {byte_index} out of range ({scalar_bytes} scalar bytes)"
                ),
            });
        }
        Ok(self.region.read_bytes(off + 8 + 8 * u64::from(hdr.other) + byte_index, 1)?[0])
    }

    // ---- Name -------------------------------------------------------------

    /// Decode a `Name` value from a word, returning its interned handle.
    pub fn name(&mut self, w: u64) -> Result<Name> {
        match self.slot(w)? {
            Slot::Scalar(v) => {
                if v == 0 {
                    Ok(Name(0))
                } else {
                    Err(Error::DecodeShape {
                        offset: 0,
                        reason: format!("unexpected scalar {v} in Name position"),
                    })
                }
            }
            Slot::Ptr(off) => {
                if let Some(n) = self.names.get(&off) {
                    return Ok(*n);
                }
                self.enter()?;
                let res = self.name_uncached(off);
                self.leave();
                let n = res?;
                self.names.insert(off, n);
                Ok(n)
            }
        }
    }

    fn name_uncached(&mut self, off: u64) -> Result<Name> {
        let hdr = self.region.obj_header(off)?;
        match hdr.tag {
            0 => Ok(Name(0)),
            1 | 2 => {
                let pre = self.name(self.region.ctor_field(off, 0)?.0)?;
                // `lean_name_hash`: the `UInt64` in the first scalar slot
                // (byte offset 8 + 8*other), which drives `NameMap` ordering.
                let hash = self.scalar_u64(off, hdr)?;
                if hdr.tag == 1 {
                    let comp = self.string(self.region.ctor_field(off, 1)?.0)?;
                    let s = self.arenas.names.intern_str(&comp);
                    Ok(self.arenas.names.intern_key(NameKey::Str(pre.0, s), hash))
                } else {
                    let comp = self.nat_str(self.region.ctor_field(off, 1)?.0)?;
                    let i = self.arenas.names.intern_str(&comp);
                    Ok(self.arenas.names.intern_key(NameKey::Num(pre.0, i), hash))
                }
            }
            t => Err(Error::DecodeShape {
                offset: off,
                reason: format!("unexpected tag {t} in Name position"),
            }),
        }
    }

    /// The `UInt64` in the first scalar slot of the ctor at `off`.
    fn scalar_u64(&self, off: u64, hdr: ObjHeader) -> Result<u64> {
        let scalar_bytes = hdr.cs_sz as u64 - 8 - 8 * u64::from(hdr.other);
        if scalar_bytes < 8 {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!(
                    "expected 8 scalar bytes for hash, got {scalar_bytes}"
                ),
            });
        }
        let b = self.region.read_bytes(off + 8 + 8 * u64::from(hdr.other), 8)?;
        Ok(u64::from_le_bytes(b.try_into().unwrap()))
    }

    // ---- Level ------------------------------------------------------------

    /// Decode a `Level` value from a word, returning its interned handle.
    pub fn level(&mut self, w: u64) -> Result<Level> {
        if let Slot::Scalar(_) = self.slot(w)? {
            // `Level.zero` is a nullary constructor, stored as box(0).
            return Ok(Level(0));
        }
        let off = self.region.deref(w)?;
        if let Some(l) = self.levels.get(&off) {
            return Ok(*l);
        }
        self.enter()?;
        let res = self.level_uncached(off);
        self.leave();
        let l = res?;
        self.levels.insert(off, l);
        Ok(l)
    }

    fn level_uncached(&mut self, off: u64) -> Result<Level> {
        let hdr = self.region.obj_header(off)?;
        let node = match hdr.tag {
            0 => LevelNode::Zero,
            1 => LevelNode::Succ(self.level(self.region.ctor_field(off, 0)?.0)?.0),
            2 => LevelNode::Max(
                self.level(self.region.ctor_field(off, 0)?.0)?.0,
                self.level(self.region.ctor_field(off, 1)?.0)?.0,
            ),
            3 => LevelNode::Imax(
                self.level(self.region.ctor_field(off, 0)?.0)?.0,
                self.level(self.region.ctor_field(off, 1)?.0)?.0,
            ),
            4 => LevelNode::Param(self.name(self.region.ctor_field(off, 0)?.0)?),
            5 => LevelNode::MVar(self.name(self.region.ctor_field(off, 0)?.0)?),
            t => {
                return Err(Error::DecodeShape {
                    offset: off,
                    reason: format!("unexpected tag {t} in Level position"),
                })
            }
        };
        Ok(self.arenas.levels.intern(node))
    }

    // ---- List -------------------------------------------------------------

    /// Decode a Lean `List` of values (`nil` = box(0), `cons` = tag 1).
    fn list<T>(
        &mut self,
        w: u64,
        mut elem: impl FnMut(&mut Self, u64) -> Result<T>,
    ) -> Result<Vec<T>> {
        let mut out = Vec::new();
        let mut cur = w;
        let mut guard = 0u32;
        loop {
            match self.slot(cur)? {
                Slot::Scalar(v) => {
                    if v != 0 {
                        return Err(Error::DecodeShape {
                            offset: 0,
                            reason: format!("unexpected scalar {v} as List tail"),
                        });
                    }
                    return Ok(out);
                }
                Slot::Ptr(off) => {
                    guard += 1;
                    if guard > MAX_DEPTH {
                        return Err(Error::DecodeShape {
                            offset: off,
                            reason: "list too long".into(),
                        });
                    }
                    let hdr = self.region.obj_header(off)?;
                    if hdr.tag != 1 || hdr.other != 2 {
                        return Err(Error::DecodeShape {
                            offset: off,
                            reason: format!("expected List cons, got tag {}", hdr.tag),
                        });
                    }
                    out.push(elem(self, self.region.ctor_field(off, 0)?.0)?);
                    cur = self.region.ctor_field(off, 1)?.0;
                }
            }
        }
    }

    // ---- Expr -------------------------------------------------------------

    /// Decode an `Expr` value from a word, returning its interned handle.
    pub fn expr(&mut self, w: u64) -> Result<Expr> {
        match self.slot(w)? {
            Slot::Scalar(v) => Err(Error::DecodeShape {
                offset: 0,
                reason: format!("Expr cannot be a scalar (got {v})"),
            }),
            Slot::Ptr(off) => {
                if let Some(e) = self.exprs.get(&off) {
                    return Ok(*e);
                }
                self.enter()?;
                let res = self.expr_uncached(off);
                self.leave();
                let e = res?;
                self.exprs.insert(off, e);
                Ok(e)
            }
        }
    }

    fn expr_uncached(&mut self, off: u64) -> Result<Expr> {
        let hdr = self.region.obj_header(off)?;
        let f = |i: u8| self.region.ctor_field(off, i);
        let node = match hdr.tag {
            0 => ExprNode::BVar(self.nat_u64(f(0)?.0)?),
            1 => ExprNode::FVar(self.name(f(0)?.0)?),
            2 => ExprNode::MVar(self.name(f(0)?.0)?),
            3 => ExprNode::Sort(self.level(f(0)?.0)?),
            4 => {
                let n = self.name(f(0)?.0)?;
                let us = self.list(f(1)?.0, |d, w| Ok(d.level(w)?.0))?;
                let llist = self.arenas.exprs.intern_level_list(us);
                ExprNode::Const(n, llist)
            }
            5 => {
                let fst = self.expr(f(0)?.0)?;
                let snd = self.expr(f(1)?.0)?;
                ExprNode::App(fst.0, snd.0)
            }
            6 | 7 => {
                let bi = self.binder_info(off, hdr)?;
                let lam = hdr.tag == 6;
                let n = self.name(f(0)?.0)?;
                let t = self.expr(f(1)?.0)?;
                let b = self.expr(f(2)?.0)?;
                if lam {
                    ExprNode::Lam(n, t.0, b.0, bi)
                } else {
                    ExprNode::ForallE(n, t.0, b.0, bi)
                }
            }
            8 => {
                // letE: [name, type, value, body] + data word + nondep byte.
                let nondep = self.scalar_byte(off, hdr, 8)? != 0;
                let n = self.name(f(0)?.0)?;
                let t = self.expr(f(1)?.0)?;
                let v = self.expr(f(2)?.0)?;
                let b = self.expr(f(3)?.0)?;
                ExprNode::LetE(n, t.0, v.0, b.0, nondep)
            }
            9 => {
                // lit: the slot holds a `Literal` object (or, for a small
                // `natVal`, occasionally a boxed scalar directly).
                let lit_w = f(0)?.0;
                let lit = match self.slot(lit_w)? {
                    Slot::Scalar(v) => Literal::NatVal(self.arenas.names.intern_str(&v.to_string())),
                    Slot::Ptr(lo) => {
                        let lh = self.region.obj_header(lo)?;
                        match lh.tag {
                            0 => {
                                let s = self.nat_str(self.region.ctor_field(lo, 0)?.0)?;
                                Literal::NatVal(self.arenas.names.intern_str(&s))
                            }
                            1 => {
                                let s = self.string(self.region.ctor_field(lo, 0)?.0)?;
                                Literal::StrVal(self.arenas.names.intern_str(&s))
                            }
                            t => {
                                return Err(Error::DecodeShape {
                                    offset: lo,
                                    reason: format!("unexpected tag {t} in Literal position"),
                                })
                            }
                        }
                    }
                };
                ExprNode::Lit(self.arenas.exprs.intern_lit(lit))
            }
            10 => {
                // mdata: [mdata(KVMap), expr]. In v4.30.0 `KVMap` is a
                // single-field structure `{ entries : List (Name × DataValue) }`
                // whose field is stored directly (unwrapped) as the first
                // object field of the mdata constructor.
                let entries = self.kv_entries(f(0)?.0)?;
                let kv = self.arenas.exprs.intern_kv(entries);
                let inner = self.expr(f(1)?.0)?;
                ExprNode::MData(kv, inner.0)
            }
            11 => {
                let n = self.name(f(0)?.0)?;
                let i = self.nat_u64(f(1)?.0)?;
                let st = self.expr(f(2)?.0)?;
                ExprNode::Proj(n, i, st.0)
            }
            t => {
                return Err(Error::DecodeShape {
                    offset: off,
                    reason: format!("unexpected tag {t} in Expr position"),
                })
            }
        };
        Ok(self.arenas.exprs.intern(node))
    }

    /// Decode the `KVMap` entries of an `mdata` node: a `List` of
    /// `(Name × DataValue)` pairs.
    fn kv_entries(&mut self, w: u64) -> Result<Vec<(Name, DataValue)>> {
        self.list(w, |d, w| d.kv_entry(w))
    }

    fn kv_entry(&mut self, w: u64) -> Result<(Name, DataValue)> {
        let off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("KVMap entry cannot be scalar (got {v})"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let hdr = self.region.obj_header(off)?;
        if hdr.tag != 0 || hdr.other != 2 {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!("expected (Name × DataValue) pair, got tag {} other {}", hdr.tag, hdr.other),
            });
        }
        let key = self.name(self.region.ctor_field(off, 0)?.0)?;
        let value = self.data_value(self.region.ctor_field(off, 1)?.0)?;
        Ok((key, value))
    }

    fn data_value(&mut self, w: u64) -> Result<DataValue> {
        let off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("DataValue cannot be scalar (got {v})"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let hdr = self.region.obj_header(off)?;
        match hdr.tag {
            0 => Ok(DataValue::OfString(self.string(self.region.ctor_field(off, 0)?.0)?)),
            1 => Ok(DataValue::OfBool(self.scalar_byte(off, hdr, 0)? != 0)),
            2 => Ok(DataValue::OfName(self.name(self.region.ctor_field(off, 0)?.0)?)),
            3 => Ok(DataValue::OfNat(self.nat_str(self.region.ctor_field(off, 0)?.0)?)),
            4 => {
                // Int: `ofNat (n : Nat)` (tag 0) | `negSucc (n : Nat)` (tag 1)
                let int_w = self.region.ctor_field(off, 0)?.0;
                let ioff = match self.slot(int_w)? {
                    Slot::Scalar(v) => {
                        return Err(Error::DecodeShape {
                            offset: off,
                            reason: format!("Int value is scalar {v}"),
                        })
                    }
                    Slot::Ptr(o) => o,
                };
                let ih = self.region.obj_header(ioff)?;
                let mag = self.nat_str(self.region.ctor_field(ioff, 0)?.0)?;
                match ih.tag {
                    0 => Ok(DataValue::OfInt(mag)),
                    1 => {
                        // negSucc n = -(n + 1)
                        let n = mag.parse::<u64>().unwrap_or(u64::MAX);
                        Ok(DataValue::OfInt(format!("-{}", n + 1)))
                    }
                    t => Err(Error::DecodeShape {
                        offset: ioff,
                        reason: format!("unexpected Int ctor tag {t}"),
                    }),
                }
            }
            5 => Ok(DataValue::OfSyntax),
            t => Err(Error::DecodeShape {
                offset: off,
                reason: format!("unexpected DataValue tag {t}"),
            }),
        }
    }

    /// `binderInfo` byte of a `lam`/`forallE` ctor: the first byte of the
    /// second scalar slot (after the runtime data word).
    fn binder_info(&mut self, off: u64, hdr: ObjHeader) -> Result<BinderInfo> {
        let b = self.scalar_byte(off, hdr, 8)?;
        Ok(match b {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            3 => BinderInfo::InstImplicit,
            other => {
                return Err(Error::DecodeShape {
                    offset: off,
                    reason: format!("invalid binderInfo byte {other}"),
                })
            }
        })
    }

    // ---- ConstantInfo -----------------------------------------------------

    /// Fields shared by every declaration value: `{ name, levelParams, type }`
    /// as a nested `ConstantVal` subobject.
    fn constant_val(&mut self, off: u64) -> Result<ConstantVal> {
        let hdr = self.region.obj_header(off)?;
        if hdr.tag != 0 || hdr.other != 3 {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!("expected ConstantVal, got tag {} other {}", hdr.tag, hdr.other),
            });
        }
        Ok(ConstantVal {
            name: self.name(self.region.ctor_field(off, 0)?.0)?,
            level_params: self
                .list(self.region.ctor_field(off, 1)?.0, |d, w| d.name(w))?,
            ty: self.expr(self.region.ctor_field(off, 2)?.0)?,
        })
    }

    /// The declaration value object of a `ConstantInfo` (its only field).
    fn val_obj(&mut self, ci_off: u64) -> Result<u64> {
        let hdr = self.region.obj_header(ci_off)?;
        if hdr.other != 1 {
            return Err(Error::DecodeShape {
                offset: ci_off,
                reason: format!("expected ConstantInfo with 1 field, got {}", hdr.other),
            });
        }
        match self.slot(self.region.ctor_field(ci_off, 0)?.0)? {
            Slot::Ptr(off) => Ok(off),
            Slot::Scalar(v) => Err(Error::DecodeShape {
                offset: ci_off,
                reason: format!("ConstantInfo value is scalar {v}"),
            }),
        }
    }

    fn hints(&mut self, w: u64) -> Result<ReducibilityHints> {
        match self.slot(w)? {
            Slot::Scalar(v) => Ok(match v {
                0 => ReducibilityHints::Opaque,
                1 => ReducibilityHints::Abbrev,
                other => {
                    return Err(Error::DecodeShape {
                        offset: 0,
                        reason: format!("invalid ReducibilityHints scalar {other}"),
                    })
                }
            }),
            Slot::Ptr(off) => {
                let hdr = self.region.obj_header(off)?;
                // `ReducibilityHints.regular h` stores the raw `UInt32`
                // height in its scalar section.
                if hdr.tag != 2 {
                    return Err(Error::DecodeShape {
                        offset: off,
                        reason: format!("unexpected tag {} for ReducibilityHints", hdr.tag),
                    });
                }
                let scalar_bytes = u64::from(hdr.cs_sz) - 8 - 8 * u64::from(hdr.other);
                if scalar_bytes < 4 {
                    return Err(Error::DecodeShape {
                        offset: off,
                        reason: "ReducibilityHints.regular missing height".into(),
                    });
                }
                let b = self
                    .region
                    .read_bytes(off + 8 + 8 * u64::from(hdr.other), 4)?;
                let height = u32::from_le_bytes(b.try_into().unwrap());
                Ok(ReducibilityHints::Regular(height))
            }
        }
    }

    /// Decode a `ConstantInfo` value from a word.
    pub fn constant_info(&mut self, w: u64) -> Result<ConstantInfo> {
        let off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("ConstantInfo cannot be scalar (got {v})"),
                })
            }
            Slot::Ptr(off) => off,
        };
        if let Some(c) = self.consts.get(&off) {
            return Ok(c.clone());
        }
        self.enter()?;
        let res = self.constant_info_uncached(off);
        self.leave();
        let c = res?;
        self.consts.insert(off, c.clone());
        Ok(c)
    }

    fn constant_info_uncached(&mut self, off: u64) -> Result<ConstantInfo> {
        let hdr = self.region.obj_header(off)?;
        let val_off = self.val_obj(off)?;
        let vh = self.region.obj_header(val_off)?;
        if vh.tag != 0 {
            return Err(Error::DecodeShape {
                offset: val_off,
                reason: format!("declaration value must be a ctor, got tag {}", vh.tag),
            });
        }
        let cv_w = self.region.ctor_field(val_off, 0)?.0;
        let cv_off = match self.slot(cv_w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: val_off,
                    reason: format!("ConstantVal is scalar {v}"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let cv = self.constant_val(cv_off)?;
        let scalar = |d: &mut Self, idx: u64| d.scalar_byte(val_off, vh, idx);
        match hdr.tag {
            0 => {
                // AxiomVal: [cv] + isUnsafe
                Ok(ConstantInfo::Axiom(AxiomVal {
                    val: cv,
                    is_unsafe: scalar(self, 0)? != 0,
                }))
            }
            1 => {
                // DefinitionVal: [cv, value, hints, all] + safety
                let value = self.expr(self.region.ctor_field(val_off, 1)?.0)?;
                let hints = self.hints(self.region.ctor_field(val_off, 2)?.0)?;
                let all = self.list(self.region.ctor_field(val_off, 3)?.0, |d, w| d.name(w))?;
                let safety = match scalar(self, 0)? {
                    0 => DefinitionSafety::Unsafe,
                    1 => DefinitionSafety::Safe,
                    2 => DefinitionSafety::Partial,
                    other => {
                        return Err(Error::DecodeShape {
                            offset: val_off,
                            reason: format!("invalid DefinitionSafety byte {other}"),
                        })
                    }
                };
                Ok(ConstantInfo::Defn(DefinitionVal {
                    val: cv,
                    value,
                    hints,
                    safety,
                    all,
                }))
            }
            2 => {
                // TheoremVal: [cv, value, all]
                let value = self.expr(self.region.ctor_field(val_off, 1)?.0)?;
                let all = self.list(self.region.ctor_field(val_off, 2)?.0, |d, w| d.name(w))?;
                Ok(ConstantInfo::Thm(TheoremVal { val: cv, value, all }))
            }
            3 => {
                // OpaqueVal: [cv, value, all] + isUnsafe
                let value = self.expr(self.region.ctor_field(val_off, 1)?.0)?;
                let all = self.list(self.region.ctor_field(val_off, 2)?.0, |d, w| d.name(w))?;
                Ok(ConstantInfo::Opaque(OpaqueVal {
                    val: cv,
                    value,
                    is_unsafe: scalar(self, 0)? != 0,
                    all,
                }))
            }
            4 => {
                // QuotVal: [cv] + kind
                let kind = match scalar(self, 0)? {
                    0 => QuotKind::Type,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    other => {
                        return Err(Error::DecodeShape {
                            offset: val_off,
                            reason: format!("invalid QuotKind byte {other}"),
                        })
                    }
                };
                Ok(ConstantInfo::Quot(QuotVal { val: cv, kind }))
            }
            5 => {
                // InductiveVal: [cv, numParams, numIndices, all, ctors,
                // numNested] + isRec, isUnsafe, isReflexive (packed)
                let num_params = self.nat_u64(self.region.ctor_field(val_off, 1)?.0)?;
                let num_indices = self.nat_u64(self.region.ctor_field(val_off, 2)?.0)?;
                let all = self.list(self.region.ctor_field(val_off, 3)?.0, |d, w| d.name(w))?;
                let ctors = self.list(self.region.ctor_field(val_off, 4)?.0, |d, w| d.name(w))?;
                let num_nested = self.nat_u64(self.region.ctor_field(val_off, 5)?.0)?;
                Ok(ConstantInfo::Induct(InductiveVal {
                    val: cv,
                    num_params,
                    num_indices,
                    all,
                    ctors,
                    num_nested,
                    is_rec: scalar(self, 0)? != 0,
                    is_unsafe: scalar(self, 1)? != 0,
                    is_reflexive: scalar(self, 2)? != 0,
                }))
            }
            6 => {
                // ConstructorVal: [cv, induct, cidx, numParams, numFields]
                // + isUnsafe
                let induct = self.name(self.region.ctor_field(val_off, 1)?.0)?;
                let cidx = self.nat_u64(self.region.ctor_field(val_off, 2)?.0)?;
                let num_params = self.nat_u64(self.region.ctor_field(val_off, 3)?.0)?;
                let num_fields = self.nat_u64(self.region.ctor_field(val_off, 4)?.0)?;
                Ok(ConstantInfo::Ctor(ConstructorVal {
                    val: cv,
                    induct,
                    cidx,
                    num_params,
                    num_fields,
                    is_unsafe: scalar(self, 0)? != 0,
                }))
            }
            7 => {
                // RecursorVal: [cv, all, numParams, numIndices, numMotives,
                // numMinors, rules] + k, isUnsafe (packed)
                let all = self.list(self.region.ctor_field(val_off, 1)?.0, |d, w| d.name(w))?;
                let num_params = self.nat_u64(self.region.ctor_field(val_off, 2)?.0)?;
                let num_indices = self.nat_u64(self.region.ctor_field(val_off, 3)?.0)?;
                let num_motives = self.nat_u64(self.region.ctor_field(val_off, 4)?.0)?;
                let num_minors = self.nat_u64(self.region.ctor_field(val_off, 5)?.0)?;
                let rules =
                    self.list(self.region.ctor_field(val_off, 6)?.0, |d, w| d.rec_rule(w))?;
                Ok(ConstantInfo::Rec(RecursorVal {
                    val: cv,
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules,
                    k: scalar(self, 0)? != 0,
                    is_unsafe: scalar(self, 1)? != 0,
                }))
            }
            t => Err(Error::DecodeShape {
                offset: off,
                reason: format!("unexpected ConstantInfo tag {t}"),
            }),
        }
    }

    fn rec_rule(&mut self, w: u64) -> Result<RecursorRule> {
        let off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("RecursorRule cannot be scalar (got {v})"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let hdr = self.region.obj_header(off)?;
        if hdr.tag != 0 || hdr.other != 3 {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!("expected RecursorRule, got tag {} other {}", hdr.tag, hdr.other),
            });
        }
        Ok(RecursorRule {
            ctor: self.name(self.region.ctor_field(off, 0)?.0)?,
            nfields: self.nat_u64(self.region.ctor_field(off, 1)?.0)?,
            rhs: self.expr(self.region.ctor_field(off, 2)?.0)?,
        })
    }

    // ---- ModuleData -------------------------------------------------------

    /// Decode the root `ModuleData` object of segment 0.
    pub fn module_data(&mut self) -> Result<ModuleData> {
        self.module_data_part(0)
    }

    /// Decode the root `ModuleData` object of segment `part`.
    pub fn module_data_part(&mut self, part: usize) -> Result<ModuleData> {
        self.module_data_opt(part, true)
    }

    /// Decode only the fields needed to build an environment (`isModule`,
    /// imports, constants) of segment `part`, skipping `constNames`,
    /// `extraConstNames` and `entries` (persistent-extension state, which
    /// can be very large and is irrelevant to export).
    pub fn module_data_lite(&mut self, part: usize) -> Result<ModuleData> {
        self.module_data_opt(part, false)
    }

    fn module_data_opt(&mut self, part: usize, full: bool) -> Result<ModuleData> {
        let root = self.region.root_ptr_at(part)?;
        let off = self.region.deref(root.0)?;
        let hdr = self.region.obj_header(off)?;
        if hdr.tag != 0 || hdr.other != 5 {
            return Err(Error::DecodeShape {
                offset: off,
                reason: format!("expected ModuleData, got tag {} other {}", hdr.tag, hdr.other),
            });
        }
        let is_module = self.scalar_byte(off, hdr, 0)? != 0;
        if !full {
            let imports = self.imports(self.region.ctor_field(off, 0)?.0)?;
            let constants = self.array_of(off, 2, |d, w| d.constant_info(w))?;
            // `extraConstNames` feeds `numPrivateConsts` in
            // `finalizeImport`, which sizes the `Std.HashMap` backing
            // `env.constants` and thus determines the bucket count (and
            // hence iteration order). Decode it even in lite mode.
            let extra_const_names = self.array_of(off, 3, |d, w| d.name(w))?;
            return Ok(ModuleData {
                is_module,
                imports,
                const_names: Vec::new(),
                constants,
                extra_const_names,
                entries: Vec::new(),
            });
        }
        let imports = self.imports(self.region.ctor_field(off, 0)?.0)?;
        let const_names = self.array_of(off, 1, |d, w| d.name(w))?;
        let constants = self.array_of(off, 2, |d, w| d.constant_info(w))?;
        let extra_const_names = self.array_of(off, 3, |d, w| d.name(w))?;
        let entries = self.entries(self.region.ctor_field(off, 4)?.0)?;
        Ok(ModuleData {
            is_module,
            imports,
            const_names,
            constants,
            extra_const_names,
            entries,
        })
    }

    fn array_of<T>(
        &mut self,
        owner_off: u64,
        field: u8,
        mut elem: impl FnMut(&mut Self, u64) -> Result<T>,
    ) -> Result<Vec<T>> {
        let w = self.region.ctor_field(owner_off, field)?.0;
        let arr_off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("expected Array, got scalar {v}"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let hdr = self.region.obj_header(arr_off)?;
        if hdr.tag != TAG_ARRAY {
            return Err(Error::DecodeShape {
                offset: arr_off,
                reason: format!("expected Array, got tag {}", hdr.tag),
            });
        }
        let (size, _cap) = self.region.array_info(arr_off)?;
        let mut out = Vec::with_capacity(size.min(1 << 20) as usize);
        for i in 0..size {
            out.push(elem(self, self.region.array_elem(arr_off, i)?.0)?);
        }
        Ok(out)
    }

    fn imports(&mut self, w: u64) -> Result<Vec<Import>> {
        let arr_off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("expected imports Array, got scalar {v}"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let hdr = self.region.obj_header(arr_off)?;
        if hdr.tag != TAG_ARRAY {
            return Err(Error::DecodeShape {
                offset: arr_off,
                reason: format!("expected imports Array, got tag {}", hdr.tag),
            });
        }
        let (size, _cap) = self.region.array_info(arr_off)?;
        let mut out = Vec::with_capacity(size.min(1 << 20) as usize);
        for i in 0..size {
            let w = self.region.array_elem(arr_off, i)?.0;
            let imp_off = match self.slot(w)? {
                Slot::Scalar(v) => {
                    return Err(Error::DecodeShape {
                        offset: 0,
                        reason: format!("Import cannot be scalar (got {v})"),
                    })
                }
                Slot::Ptr(off) => off,
            };
            let ih = self.region.obj_header(imp_off)?;
            if ih.tag != 0 || ih.other != 1 {
                return Err(Error::DecodeShape {
                    offset: imp_off,
                    reason: format!(
                        "expected Import ctor, got tag {} other {}",
                        ih.tag, ih.other
                    ),
                });
            }
            out.push(Import {
                module: self.name(self.region.ctor_field(imp_off, 0)?.0)?,
                import_all: self.scalar_byte(imp_off, ih, 0)? != 0,
            });
        }
        Ok(out)
    }

    fn entries(&mut self, w: u64) -> Result<Vec<(Name, u64)>> {
        let arr_off = match self.slot(w)? {
            Slot::Scalar(v) => {
                return Err(Error::DecodeShape {
                    offset: 0,
                    reason: format!("expected entries Array, got scalar {v}"),
                })
            }
            Slot::Ptr(off) => off,
        };
        let hdr = self.region.obj_header(arr_off)?;
        if hdr.tag != TAG_ARRAY {
            return Err(Error::DecodeShape {
                offset: arr_off,
                reason: format!("expected entries Array, got tag {}", hdr.tag),
            });
        }
        let (size, _cap) = self.region.array_info(arr_off)?;
        let mut out = Vec::with_capacity(size.min(1 << 20) as usize);
        for i in 0..size {
            let w = self.region.array_elem(arr_off, i)?.0;
            let e_off = match self.slot(w)? {
                Slot::Scalar(v) => {
                    return Err(Error::DecodeShape {
                        offset: 0,
                        reason: format!("entry cannot be scalar (got {v})"),
                    })
                }
                Slot::Ptr(off) => off,
            };
            let eh = self.region.obj_header(e_off)?;
            if eh.tag != 0 || eh.other != 2 {
                return Err(Error::DecodeShape {
                    offset: e_off,
                    reason: format!("expected entry pair, got tag {} other {}", eh.tag, eh.other),
                });
            }
            let name = self.name(self.region.ctor_field(e_off, 0)?.0)?;
            // Second field: Array EnvExtensionEntry — opaque; count only.
            let arr_w = self.region.ctor_field(e_off, 1)?.0;
            let count = match self.slot(arr_w)? {
                Slot::Scalar(v) => {
                    return Err(Error::DecodeShape {
                        offset: 0,
                        reason: format!("entry array is scalar {v}"),
                    })
                }
                Slot::Ptr(ao) => {
                    let ah = self.region.obj_header(ao)?;
                    if ah.tag != TAG_ARRAY {
                        return Err(Error::DecodeShape {
                            offset: ao,
                            reason: format!("expected entry Array, got tag {}", ah.tag),
                        });
                    }
                    self.region.array_info(ao)?.0
                }
            };
            out.push((name, count));
        }
        Ok(out)
    }
}
