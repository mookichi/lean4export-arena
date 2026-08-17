//! Decoded Lean data model.
//!
//! These mirror the corresponding Lean inductive types.  Field order and
//! constructor indices match the Lean 4 v4.30.0 sources, which is what the
//! compacted region encoding depends on.
//!
//! `Name`, `Level` and `Expr` are *arena handles*: `Copy` `u32` indices
//! into flat node tables owned by an [`Arenas`].  Nodes are interned by
//! structural content at decode time, so index equality *is* structural
//! equality, and identical subterms (the `.olean` region shares them
//! heavily) occupy a single node.  Compared to the previous `Rc`-tree
//! model (40-byte `Expr` + 16-byte `Rc` control block per node, ~56 bytes
//! per node), a node is now a `#[repr(u8)]` tagged enum of 8–24 bytes,
//! stored contiguously with no per-node allocation overhead — a ~4x
//! reduction of the environment's expression memory.

use std::collections::HashMap;

/// Index of a name in the [`NameTable`].
pub type NameIdx = u32;
/// Index of a level in the [`LevelTable`].
pub type LevelIdx = u32;
/// Index of an expression node in the [`ExprTable`] (env nodes and, during
/// export, transient "stripped" nodes share one index space).
pub type NodeIdx = u32;
/// Index of an interned string in the [`NameTable`]'s string table.
pub type StrIdx = u32;
/// Index of an interned [`Literal`] in the [`ExprTable`].
pub type LitIdx = u32;
/// Index of an interned KVMap in the [`ExprTable`].
pub type KVIdx = u32;
/// Index of an interned universe list in the [`ExprTable`].
pub type LevelListIdx = u32;

/// A `Name` handle (interned; index equality == structural equality).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Name(pub NameIdx);

/// A `Level` handle (interned; index equality == structural equality).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Level(pub LevelIdx);

/// An `Expr` handle (interned; index equality == structural equality).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Expr(pub NodeIdx);

/// `Name`: `anonymous | str pre s | num pre i` (tags 0, 1, 2).
///
/// `anonymous` is stored as the index-0 node.  `Num` values are `Nat`,
/// which may exceed `u64`; the decimal string preserves them exactly.
///
/// Every non-anonymous name carries the `UInt64` hash Lean stores in the
/// name object's first scalar slot (`lean_name_hash`, read directly from
/// the `.olean`). It equals `Name.hash`, which drives `NameMap` ordering
/// (`quickCmp` compares hashes first) and the `Std.HashSet` bucket index.
/// The hash is a pure function of the content, so the interning key (see
/// `NameTable`) excludes it; the first interned occurrence's hash wins.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum NameNode {
    /// tag 0
    Anonymous,
    /// tag 1
    Str {
        pre: NameIdx,
        s: StrIdx,
        hash: u64,
    },
    /// tag 2
    Num {
        pre: NameIdx,
        n: StrIdx,
        hash: u64,
    },
}

/// Content key used for name interning (the hash field is excluded: it is
/// a pure function of the content, and synthetic names carry a placeholder
/// hash of 0).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum NameKey {
    Anonymous,
    Str(NameIdx, StrIdx),
    Num(NameIdx, StrIdx),
}

/// `Level`: `zero | succ | max | imax | param | mvar` (tags 0..5).
/// `mvar` holds the mvar id, a `Name`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum LevelNode {
    /// tag 0
    Zero,
    /// tag 1
    Succ(LevelIdx),
    /// tag 2
    Max(LevelIdx, LevelIdx),
    /// tag 3
    Imax(LevelIdx, LevelIdx),
    /// tag 4
    Param(Name),
    /// tag 5
    MVar(Name),
}

/// `Literal`: `natVal | strVal` (tags 0, 1).
/// `natVal` values are `Nat`; the decimal string preserves big values.
/// Strings live in the shared interned string table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
    /// tag 0
    NatVal(StrIdx),
    /// tag 1
    StrVal(StrIdx),
}

/// `BinderInfo`: `default | implicit | strictImplicit | instImplicit`
/// (tags 0..3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// `Expr`: 14 constructors in declaration order (tags 0..13).
///
/// `Name`/`Level`/`Expr` fields are arena handles, so a node is at most
/// 24 bytes and children are shared by construction (interning).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ExprNode {
    /// tag 0
    BVar(u64),
    /// tag 1 (`FVarId` wraps a `Name`; free variables cannot occur in
    /// `.olean` files)
    FVar(Name),
    /// tag 2 (`MVarId` wraps a `Name`; metavariables cannot occur in
    /// `.olean` files)
    MVar(Name),
    /// tag 3
    Sort(Level),
    /// tag 4
    Const(Name, LevelListIdx),
    /// tag 5
    App(NodeIdx, NodeIdx),
    /// tag 6
    Lam(Name, NodeIdx, NodeIdx, BinderInfo),
    /// tag 7
    ForallE(Name, NodeIdx, NodeIdx, BinderInfo),
    /// tag 8
    LetE(Name, NodeIdx, NodeIdx, NodeIdx, bool),
    /// tag 9
    Lit(LitIdx),
    /// tag 10: `MData` = `KVMap` (a list of `(Name × DataValue)` pairs in
    /// v4.30.0) plus the wrapped expression
    MData(KVIdx, NodeIdx),
    /// tag 11
    Proj(Name, u64, NodeIdx),
}

/// `DataValue`: values stored in an `MData` key-value map.
/// `Nat`/`Int` values are kept as decimal strings so big numbers survive.
/// `Syntax` payloads are opaque (full `Syntax` decoding is out of scope;
/// they never occur in the golden export).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Name),
    OfNat(String),
    OfInt(String),
    OfSyntax,
}

impl DataValue {
    /// `reprStr` of the value, matching Lean's derived `Repr` output at
    /// `maxPrec` — the format used by `KVMap.toJson` in the exporter.
    ///
    /// Mirrors `Init/Data/Repr.lean` (`String.quote`, `Char.quoteCore`),
    /// `Init/Meta/Defs.lean` (`Name.reprPrec`) and `Init/Data/Int/Repr.lean`.
    pub fn repr_str(&self, arenas: &Arenas) -> String {
        let ctor = match self {
            DataValue::OfString(_) => "Lean.DataValue.ofString",
            DataValue::OfBool(_) => "Lean.DataValue.ofBool",
            DataValue::OfName(_) => "Lean.DataValue.ofName",
            DataValue::OfNat(_) => "Lean.DataValue.ofNat",
            DataValue::OfInt(_) => "Lean.DataValue.ofInt",
            DataValue::OfSyntax => "Lean.DataValue.ofSyntax",
        };
        match self {
            DataValue::OfString(s) => format!("{ctor} {}", quote_str(s)),
            DataValue::OfBool(b) => format!("{ctor} {b}"),
            DataValue::OfName(n) => format!("{ctor} {}", name_repr(&arenas.names, *n)),
            DataValue::OfNat(n) => format!("{ctor} {n}"),
            DataValue::OfInt(i) => {
                // `Repr Int`: `if i < 0 then Repr.addAppParen i.repr prec else i.repr`
                // — at `maxPrec`, `addAppParen` always adds parentheses.
                let arg = if i.starts_with('-') {
                    format!("({i})")
                } else {
                    i.clone()
                };
                format!("{ctor} {arg}")
            }
            // The real `Syntax` repr is not implemented; flag it clearly
            // instead of emitting wrong bytes.
            DataValue::OfSyntax => "Lean.DataValue.ofSyntax <opaque syntax>".to_string(),
        }
    }
}

/// `String.quote`: the string as a Lean string literal (escaped, quoted).
fn quote_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            c if (c as u32) <= 31 || c == '\u{7f}' => {
                out.push_str(&format!("\\x{:02x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `Name.reprPrec` at `maxPrec` (`Init/Meta/Defs.lean`).
/// `Repr.addAppParen` at `maxPrec` always adds parentheses.
fn name_repr(names: &NameTable, n: Name) -> String {
    match names.node(n) {
        NameNode::Anonymous => "Lean.Name.anonymous".to_string(),
        NameNode::Num { pre, n: i, .. } => {
            format!("(Lean.Name.mkNum {} {})", name_repr(names, Name(pre)), names.str_of(i))
        }
        NameNode::Str { pre, s, .. } => {
            if names.has_num(Name(pre)) {
                format!(
                    "(Lean.Name.mkStr {} {})",
                    name_repr(names, Name(pre)),
                    quote_str(names.str_of(s))
                )
            } else {
                format!("`{}", names.to_lean_string(n))
            }
        }
    }
}

/// Whether a name component must be escaped with `«...»`.
/// Mirrors `display_name_core` in `src/util/name.cpp` (Lean 4 v4.30.0).
fn needs_escape(s: &str) -> bool {
    if s.is_empty() {
        return true;
    }
    let chars: Vec<char> = s.chars().collect();
    let mut esc = !is_id_first(chars[0]);
    // Names produced by `server::display_decl` starting with '?' are not
    // escaped (a quirk kept for parity).
    if esc && chars[0] == '?' {
        esc = false;
    }
    for &c in &chars[1..] {
        if esc {
            break;
        }
        if !is_id_rest(c) {
            esc = true;
        }
    }
    esc
}

fn is_id_first(c: char) -> bool {
    if c.is_ascii_alphabetic() || c == '_' {
        return true;
    }
    c == '\u{ab}' || is_letter_like(c)
}

fn is_id_rest(c: char) -> bool {
    if c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '?' || c == '!' {
        return true;
    }
    is_letter_like(c) || is_sub_script_alnum(c)
}

fn is_letter_like(c: char) -> bool {
    let u = c as u32;
    (0x3b1..=0x3c9).contains(&u) && u != 0x3bb // lower Greek, except lambda
        || (0x391..=0x3a9).contains(&u) && u != 0x3a0 && u != 0x3a3 // upper Greek, except Pi/Sigma
        || (0x3ca..=0x3fb).contains(&u) // Coptic letters
        || (0x1f00..=0x1ffe).contains(&u) // Polytonic Greek
        || (0x2100..=0x214f).contains(&u) // Letter-like block
        || (0x1d49c..=0x1d59f).contains(&u) // Latin script/double-struck/fractur
}

fn is_sub_script_alnum(c: char) -> bool {
    let u = c as u32;
    (0x207f..=0x2089).contains(&u) // n superscript + numeric subscripts
        || (0x2090..=0x209c).contains(&u) // letter-like subscripts
        || (0x1d62..=0x1d6a).contains(&u) // letter-like subscripts
}

/// Interned name table: nodes plus the shared string table (name components
/// and literal strings). Node 0 is `anonymous`.
#[derive(Debug, Default)]
pub struct NameTable {
    nodes: Vec<NameNode>,
    map: HashMap<NameKey, NameIdx>,
    strings: Vec<String>,
    string_map: HashMap<String, StrIdx>,
}

impl NameTable {
    pub fn new() -> NameTable {
        let mut map = HashMap::new();
        map.insert(NameKey::Anonymous, 0);
        NameTable {
            nodes: vec![NameNode::Anonymous],
            map,
            strings: Vec::new(),
            string_map: HashMap::new(),
        }
    }

    /// Intern a string, returning its handle.
    pub fn intern_str(&mut self, s: &str) -> StrIdx {
        if let Some(&i) = self.string_map.get(s) {
            return i;
        }
        let i = self.strings.len() as StrIdx;
        self.strings.push(s.to_string());
        self.string_map.insert(s.to_string(), i);
        i
    }

    /// Intern a name node given its content key and stored hash. Used by
    /// the decoder (real `lean_name_hash`) and for synthetic names (hash 0).
    pub fn intern_key(&mut self, key: NameKey, hash: u64) -> Name {
        if let Some(&i) = self.map.get(&key) {
            return Name(i);
        }
        let i = self.nodes.len() as NameIdx;
        let node = match key {
            NameKey::Anonymous => NameNode::Anonymous,
            NameKey::Str(pre, s) => NameNode::Str { pre, s, hash },
            NameKey::Num(pre, n) => NameNode::Num { pre, n, hash },
        };
        self.nodes.push(node);
        self.map.insert(key, i);
        Name(i)
    }

    /// Intern `pre.s` with a placeholder hash (synthetic lookups).
    pub fn intern_str_name(&mut self, pre: Name, s: &str) -> Name {
        let si = self.intern_str(s);
        self.intern_key(NameKey::Str(pre.0, si), 0)
    }

    /// Intern `pre.n` (decimal numeral) with a placeholder hash.
    pub fn intern_num_name(&mut self, pre: Name, n: &str) -> Name {
        let si = self.intern_str(n);
        self.intern_key(NameKey::Num(pre.0, si), 0)
    }

    /// Intern a dotted path (`["Nat", "add"]` → `Nat.add`), anonymous first.
    pub fn intern_path(&mut self, parts: &[&str]) -> Name {
        let mut n = Name(0);
        for p in parts {
            n = self.intern_str_name(n, p);
        }
        n
    }

    /// The node for a name handle.
    pub fn node(&self, n: Name) -> NameNode {
        self.nodes[n.0 as usize]
    }

    /// The interned string for a string handle.
    pub fn str_of(&self, si: StrIdx) -> &str {
        &self.strings[si as usize]
    }

    pub fn is_anonymous(&self, n: Name) -> bool {
        matches!(self.node(n), NameNode::Anonymous)
    }

    /// `Name.hash`: 1723 for `anonymous`, otherwise the hash stored in the
    /// name object (already read at decode time).
    pub fn hash(&self, n: Name) -> u64 {
        match self.node(n) {
            NameNode::Anonymous => 1723,
            NameNode::Str { hash, .. } | NameNode::Num { hash, .. } => hash,
        }
    }

    /// `Name.isInternal` (`Lean/Data/Name.lean`): any component starting
    /// with `_`, or any numeric component in the prefix.
    pub fn is_internal(&self, n: Name) -> bool {
        match self.node(n) {
            NameNode::Anonymous => false,
            NameNode::Str { pre, s, .. } => {
                self.str_of(s).starts_with('_') || self.is_internal(Name(pre))
            }
            NameNode::Num { pre, .. } => self.is_internal(Name(pre)),
        }
    }

    /// Whether any prefix component is a numeral (drives `Name.reprPrec`).
    pub fn has_num(&self, n: Name) -> bool {
        match self.node(n) {
            NameNode::Anonymous => false,
            NameNode::Num { .. } => true,
            NameNode::Str { pre, .. } => self.has_num(Name(pre)),
        }
    }

    /// Format as a dotted name, escaping components like Lean's `Repr`/
    /// `IO.println` (components containing non-identifier characters are
    /// wrapped in French quotes `«...»`).
    pub fn to_lean_string(&self, n: Name) -> String {
        self.fmt(n, false)
    }

    /// Format without `«...»` escaping, matching `Name.toString` (used for
    /// e.g. KVMap keys in the export).
    pub fn to_string_plain(&self, n: Name) -> String {
        self.fmt(n, true)
    }

    fn fmt(&self, n: Name, plain: bool) -> String {
        match self.node(n) {
            NameNode::Anonymous => String::new(),
            NameNode::Str { pre, s, .. } => {
                let s = self.str_of(s);
                let p = self.fmt(Name(pre), plain);
                let comp = if plain || !needs_escape(s) {
                    s.to_string()
                } else {
                    format!("\u{ab}{s}\u{bb}")
                };
                if p.is_empty() {
                    comp
                } else {
                    format!("{p}.{comp}")
                }
            }
            NameNode::Num { pre, n, .. } => {
                let p = self.fmt(Name(pre), plain);
                let n = self.str_of(n);
                if p.is_empty() {
                    format!(".{n}")
                } else {
                    format!("{p}.{n}")
                }
            }
        }
    }
}

/// Interned level table. Node 0 is `zero`.
#[derive(Debug, Default)]
pub struct LevelTable {
    nodes: Vec<LevelNode>,
    map: HashMap<LevelNode, LevelIdx>,
}

impl LevelTable {
    pub fn new() -> LevelTable {
        let mut map = HashMap::new();
        map.insert(LevelNode::Zero, 0);
        LevelTable {
            nodes: vec![LevelNode::Zero],
            map,
        }
    }

    /// Intern a level node, returning its handle.
    pub fn intern(&mut self, node: LevelNode) -> Level {
        if let Some(&i) = self.map.get(&node) {
            return Level(i);
        }
        let i = self.nodes.len() as LevelIdx;
        self.nodes.push(node);
        self.map.insert(node, i);
        Level(i)
    }

    /// The node for a level handle.
    pub fn node(&self, l: Level) -> LevelNode {
        self.nodes[l.0 as usize]
    }
}

/// Interned expression table.
///
/// Env nodes occupy indices `0..env_len` (never removed). During export,
/// `removeMData`-stripped nodes are appended after `env_len` into
/// `scratch` and **never removed**: handles to them live in the exporter's
/// long-lived maps (`visited_exprs`, `hash_cache`, ...), so truncating per
/// constant would leave stale handles behind (the reference Lean exporter
/// likewise keeps every stripped tree alive in its `visited_exprs` map).
/// `node` resolves both ranges, so env and stripped nodes share one index
/// space with no reuse.
#[derive(Debug, Default)]
pub struct ExprTable {
    nodes: Vec<ExprNode>,
    /// Content interning map (decode time only; dropped after load via
    /// `drop_intern_maps` to free memory before export).
    map: HashMap<ExprNode, NodeIdx>,
    level_lists: Vec<Vec<LevelIdx>>,
    level_list_map: HashMap<Vec<LevelIdx>, LevelListIdx>,
    lits: Vec<Literal>,
    lit_map: HashMap<Literal, LitIdx>,
    kvs: Vec<Vec<(Name, DataValue)>>,
    kv_map: HashMap<Vec<(Name, DataValue)>, KVIdx>,
    scratch: Vec<ExprNode>,
}

impl ExprTable {
    pub fn new() -> ExprTable {
        ExprTable {
            nodes: Vec::new(),
            map: HashMap::new(),
            level_lists: Vec::new(),
            level_list_map: HashMap::new(),
            lits: Vec::new(),
            lit_map: HashMap::new(),
            kvs: Vec::new(),
            kv_map: HashMap::new(),
            scratch: Vec::new(),
        }
    }

    /// Intern an expression node (decode time), returning its handle.
    pub fn intern(&mut self, node: ExprNode) -> Expr {
        if let Some(&i) = self.map.get(&node) {
            return Expr(i);
        }
        let i = self.nodes.len() as NodeIdx;
        self.nodes.push(node);
        self.map.insert(node, i);
        Expr(i)
    }

    /// The node for an expression handle (env or scratch range).
    pub fn node(&self, e: Expr) -> ExprNode {
        let i = e.0 as usize;
        if i < self.nodes.len() {
            self.nodes[i]
        } else {
            self.scratch[i - self.nodes.len()]
        }
    }

    /// Intern a `Const` universe list.
    pub fn intern_level_list(&mut self, list: Vec<LevelIdx>) -> LevelListIdx {
        if let Some(&i) = self.level_list_map.get(&list) {
            return i;
        }
        let i = self.level_lists.len() as LevelListIdx;
        self.level_lists.push(list.clone());
        self.level_list_map.insert(list, i);
        i
    }

    /// The universe list of a `Const` node.
    pub fn level_list(&self, idx: LevelListIdx) -> &[LevelIdx] {
        &self.level_lists[idx as usize]
    }

    /// Intern a literal (its strings are already interned in the string table).
    pub fn intern_lit(&mut self, lit: Literal) -> LitIdx {
        if let Some(&i) = self.lit_map.get(&lit) {
            return i;
        }
        let i = self.lits.len() as LitIdx;
        self.lits.push(lit);
        self.lit_map.insert(lit, i);
        i
    }

    /// The literal of a `Lit` node.
    pub fn lit(&self, idx: LitIdx) -> Literal {
        self.lits[idx as usize]
    }

    /// Intern an `MData` KVMap.
    pub fn intern_kv(&mut self, kv: Vec<(Name, DataValue)>) -> KVIdx {
        if let Some(&i) = self.kv_map.get(&kv) {
            return i;
        }
        let i = self.kvs.len() as KVIdx;
        self.kvs.push(kv.clone());
        self.kv_map.insert(kv, i);
        i
    }

    /// The KVMap entries of an `MData` node.
    pub fn kv(&self, idx: KVIdx) -> &[(Name, DataValue)] {
        &self.kvs[idx as usize]
    }

    /// Append a stripped node to the scratch section (export time),
    /// returning its handle. Never interned and never removed: handles to
    /// scratch nodes live in the exporter's long-lived maps.
    pub fn push_scratch(&mut self, node: ExprNode) -> NodeIdx {
        let i = (self.nodes.len() + self.scratch.len()) as NodeIdx;
        self.scratch.push(node);
        i
    }

    /// Number of env nodes (excludes scratch).
    pub fn env_len(&self) -> usize {
        self.nodes.len()
    }

    /// Free the decode-time interning maps. Called after the environment is
    /// fully loaded; the exporter never interns expressions, so the maps
    /// are dead weight from here on (they are the largest single allocation
    /// during load).
    pub fn drop_intern_maps(&mut self) {
        self.map.clear();
        self.map.shrink_to_fit();
        self.level_list_map.clear();
        self.level_list_map.shrink_to_fit();
        self.lit_map.clear();
        self.lit_map.shrink_to_fit();
        self.kv_map.clear();
        self.kv_map.shrink_to_fit();
    }

    /// Total node count including scratch.
    pub fn len(&self) -> usize {
        self.nodes.len() + self.scratch.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.scratch.is_empty()
    }
}

/// The arena set: every decoded `Name`/`Level`/`Expr` handle refers into
/// one of these tables.
#[derive(Debug, Default)]
pub struct Arenas {
    pub names: NameTable,
    pub levels: LevelTable,
    pub exprs: ExprTable,
}

impl Arenas {
    pub fn new() -> Arenas {
        Arenas {
            names: NameTable::new(),
            levels: LevelTable::new(),
            exprs: ExprTable::new(),
        }
    }

    /// Compact structural description of an expression (debug tooling).
    pub fn expr_debug(&self, e: Expr) -> String {
        match self.exprs.node(e) {
            ExprNode::BVar(i) => format!("bvar {i}"),
            ExprNode::FVar(n) => format!("fvar {}", self.names.to_string_plain(n)),
            ExprNode::MVar(n) => format!("mvar {}", self.names.to_string_plain(n)),
            ExprNode::Sort(l) => format!("sort({})", self.level_debug(l)),
            ExprNode::Const(n, us) => format!(
                "const {} [{}]",
                self.names.to_string_plain(n),
                self.exprs
                    .level_list(us)
                    .iter()
                    .map(|&u| self.level_debug(Level(u)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ExprNode::App(f, a) => format!("app({}, {})", self.expr_debug(Expr(f)), self.expr_debug(Expr(a))),
            ExprNode::Lam(n, t, b, _) => format!(
                "lam {} {} {}",
                self.names.to_string_plain(n),
                self.expr_debug(Expr(t)),
                self.expr_debug(Expr(b))
            ),
            ExprNode::ForallE(n, t, b, _) => format!(
                "forallE {} {} {}",
                self.names.to_string_plain(n),
                self.expr_debug(Expr(t)),
                self.expr_debug(Expr(b))
            ),
            ExprNode::LetE(n, t, v, b, nd) => format!(
                "letE {} {} {} {} {nd}",
                self.names.to_string_plain(n),
                self.expr_debug(Expr(t)),
                self.expr_debug(Expr(v)),
                self.expr_debug(Expr(b))
            ),
            ExprNode::Lit(l) => match self.exprs.lit(l) {
                Literal::NatVal(si) => format!("natVal {}", self.names.str_of(si)),
                Literal::StrVal(si) => format!("strVal {}", self.names.str_of(si)),
            },
            ExprNode::MData(kv, inner) => format!(
                "mdata({:?}, {})",
                self.exprs
                    .kv(kv)
                    .iter()
                    .map(|(k, _)| self.names.to_string_plain(*k))
                    .collect::<Vec<_>>(),
                self.expr_debug(Expr(inner))
            ),
            ExprNode::Proj(s, i, st) => format!(
                "proj {} {i} {}",
                self.names.to_string_plain(s),
                self.expr_debug(Expr(st))
            ),
        }
    }

    fn level_debug(&self, l: Level) -> String {
        match self.levels.node(l) {
            LevelNode::Zero => "0".to_string(),
            LevelNode::Succ(x) => format!("succ({})", self.level_debug(Level(x))),
            LevelNode::Max(a, b) => format!("max({}, {})", self.level_debug(Level(a)), self.level_debug(Level(b))),
            LevelNode::Imax(a, b) => format!("imax({}, {})", self.level_debug(Level(a)), self.level_debug(Level(b))),
            LevelNode::Param(n) => format!("param {}", self.names.to_string_plain(n)),
            LevelNode::MVar(n) => format!("mvar {}", self.names.to_string_plain(n)),
        }
    }
}

/// `ReducibilityHints`: `opaque | abbrev | regular h` (tags 0, 1, 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

/// `DefinitionSafety`: `«unsafe» | safe | «partial»` (tags 0, 1, 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// `QuotKind`: `type | ctor | lift | ind` (tags 0..3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// Fields common to every `ConstantInfo` variant (`ConstantVal`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstantVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
}

/// `AxiomVal` (ConstantInfo tag 0).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AxiomVal {
    pub val: ConstantVal,
    pub is_unsafe: bool,
}

/// `DefinitionVal` (ConstantInfo tag 1).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefinitionVal {
    pub val: ConstantVal,
    pub value: Expr,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    pub all: Vec<Name>,
}

/// `TheoremVal` (ConstantInfo tag 2).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TheoremVal {
    pub val: ConstantVal,
    pub value: Expr,
    pub all: Vec<Name>,
}

/// `OpaqueVal` (ConstantInfo tag 3).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OpaqueVal {
    pub val: ConstantVal,
    pub value: Expr,
    pub is_unsafe: bool,
    pub all: Vec<Name>,
}

/// `QuotVal` (ConstantInfo tag 4).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuotVal {
    pub val: ConstantVal,
    pub kind: QuotKind,
}

/// `InductiveVal` (ConstantInfo tag 5).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InductiveVal {
    pub val: ConstantVal,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<Name>,
    pub ctors: Vec<Name>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// `ConstructorVal` (ConstantInfo tag 6).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorVal {
    pub val: ConstantVal,
    pub induct: Name,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
    pub is_unsafe: bool,
}

/// `RecursorRule`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecursorRule {
    pub ctor: Name,
    pub nfields: u64,
    pub rhs: Expr,
}

/// `RecursorVal` (ConstantInfo tag 7).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecursorVal {
    pub val: ConstantVal,
    pub all: Vec<Name>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// `ConstantInfo`: 8 constructors, tags 0..7.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantInfo {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Opaque(OpaqueVal),
    Quot(QuotVal),
    Induct(InductiveVal),
    Ctor(ConstructorVal),
    Rec(RecursorVal),
}

impl ConstantInfo {
    pub fn name(&self) -> Name {
        match self {
            ConstantInfo::Axiom(v) => v.val.name,
            ConstantInfo::Defn(v) => v.val.name,
            ConstantInfo::Thm(v) => v.val.name,
            ConstantInfo::Opaque(v) => v.val.name,
            ConstantInfo::Quot(v) => v.val.name,
            ConstantInfo::Induct(v) => v.val.name,
            ConstantInfo::Ctor(v) => v.val.name,
            ConstantInfo::Rec(v) => v.val.name,
        }
    }

    /// The declaration's type expression (`ConstantVal.type`).
    pub fn ty_expr(&self) -> Expr {
        match self {
            ConstantInfo::Axiom(v) => v.val.ty,
            ConstantInfo::Defn(v) => v.val.ty,
            ConstantInfo::Thm(v) => v.val.ty,
            ConstantInfo::Opaque(v) => v.val.ty,
            ConstantInfo::Quot(v) => v.val.ty,
            ConstantInfo::Induct(v) => v.val.ty,
            ConstantInfo::Ctor(v) => v.val.ty,
            ConstantInfo::Rec(v) => v.val.ty,
        }
    }

    /// The declaration's universe parameters (`ConstantVal.levelParams`).
    pub fn level_params(&self) -> &[Name] {
        match self {
            ConstantInfo::Axiom(v) => &v.val.level_params,
            ConstantInfo::Defn(v) => &v.val.level_params,
            ConstantInfo::Thm(v) => &v.val.level_params,
            ConstantInfo::Opaque(v) => &v.val.level_params,
            ConstantInfo::Quot(v) => &v.val.level_params,
            ConstantInfo::Induct(v) => &v.val.level_params,
            ConstantInfo::Ctor(v) => &v.val.level_params,
            ConstantInfo::Rec(v) => &v.val.level_params,
        }
    }

    /// The declaration's value expression, if it has one
    /// (`defn`/`thm`/`opaque`).
    pub fn value_expr(&self) -> Option<Expr> {
        match self {
            ConstantInfo::Defn(v) => Some(v.value),
            ConstantInfo::Thm(v) => Some(v.value),
            ConstantInfo::Opaque(v) => Some(v.value),
            _ => None,
        }
    }
}

/// `Import`: `{ module : Name, importAll : Bool }`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import {
    pub module: Name,
    pub import_all: bool,
}

/// `ModuleData` (root object of a `.olean`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<Name>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<Name>,
    /// `entries : Array (Name × Array EnvExtensionEntry)`.
    /// The payloads are opaque to us; only names and counts are decoded.
    pub entries: Vec<(Name, u64)>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_interning_is_structural() {
        let mut names = NameTable::new();
        // `anonymous` is index 0.
        assert_eq!(names.node(Name(0)), NameNode::Anonymous);
        assert!(names.is_anonymous(Name(0)));

        // Same content, same handle (and no duplicates inserted).
        let a = names.intern_str_name(Name(0), "Nat");
        let b = names.intern_str_name(Name(0), "Nat");
        assert_eq!(a, b);
        let add1 = names.intern_str_name(a, "add");
        let add2 = names.intern_str_name(b, "add");
        assert_eq!(add1, add2);

        // Different content, different handle.
        let sub = names.intern_str_name(a, "sub");
        assert_ne!(add1, sub);

        // Numeral components are distinct from string components.
        let n1 = names.intern_num_name(Name(0), "1");
        let s1 = names.intern_str_name(Name(0), "1");
        assert_ne!(n1, s1);

        // Dotted-path interning gives the same handle as stepwise interning.
        let path = names.intern_path(&["Nat", "add"]);
        assert_eq!(path, add1);
    }

    #[test]
    fn name_formatting_and_predicates() {
        let mut names = NameTable::new();
        let nat_add = names.intern_path(&["Nat", "add"]);
        assert_eq!(names.to_lean_string(nat_add), "Nat.add");
        assert_eq!(names.to_string_plain(nat_add), "Nat.add");
        assert!(!names.is_internal(nat_add));
        assert!(!names.has_num(nat_add));

        // Anonymous formats as empty.
        assert_eq!(names.to_lean_string(Name(0)), "");
        assert_eq!(names.hash(Name(0)), 1723);

        // Internal: `_private` prefix.
        let priv_ = names.intern_path(&["_private", "X"]);
        assert!(names.is_internal(priv_));
        // `Name.isInternal` on a bare numeral checks only the prefix
        // (Lean parity: `(anonymous).5` is not internal).
        let num = names.intern_num_name(Name(0), "5");
        assert!(!names.is_internal(num));
        assert!(names.has_num(num));
        // ... but a numeral under an internal prefix is internal.
        let priv_num = names.intern_num_name(priv_, "5");
        assert!(names.is_internal(priv_num));

        // Component needing `«...»` escaping.
        let esc = names.intern_path(&["foo bar"]);
        assert_eq!(names.to_lean_string(esc), "\u{ab}foo bar\u{bb}");
        assert_eq!(names.to_string_plain(esc), "foo bar");

        // `?` prefix is not escaped (display quirk kept for parity).
        let q = names.intern_path(&["?x"]);
        assert_eq!(names.to_lean_string(q), "?x");
    }

    #[test]
    fn name_hash_and_num_format() {
        let mut names = NameTable::new();
        // Synthetic names carry hash 0; `hash()` returns the stored hash.
        let n = names.intern_str_name(Name(0), "foo");
        assert_eq!(names.hash(n), 0);

        // Numeral names format as `.5` with no prefix, `A.5` with one.
        let bare = names.intern_num_name(Name(0), "5");
        assert_eq!(names.to_lean_string(bare), ".5");
        let a = names.intern_path(&["A"]);
        let pref = names.intern_num_name(a, "5");
        assert_eq!(names.to_lean_string(pref), "A.5");
    }

    #[test]
    fn level_interning_is_structural() {
        let mut levels = LevelTable::new();
        // Node 0 is `zero`.
        assert_eq!(levels.node(Level(0)), LevelNode::Zero);

        let u = levels.intern(LevelNode::Param(Name(0)));
        let v = levels.intern(LevelNode::Param(Name(0)));
        assert_eq!(u, v);
        let max1 = levels.intern(LevelNode::Max(u.0, v.0));
        let max2 = levels.intern(LevelNode::Max(v.0, u.0));
        assert_eq!(max1, max2);

        // Different levels get different handles.
        let other = levels.intern(LevelNode::Param(Name(0)));
        assert_eq!(other, u); // same content again
        let succ = levels.intern(LevelNode::Succ(u.0));
        assert_ne!(succ, u);
    }

    #[test]
    fn expr_interning_and_scratch() {
        let mut arenas = Arenas::new();
        let nat = arenas.names.intern_path(&["Nat"]);

        // Structurally equal nodes share one handle.
        let ty = arenas.exprs.intern(ExprNode::Sort(Level(0)));
        let c1 = arenas.exprs.intern(ExprNode::Const(nat, 0));
        let c2 = arenas.exprs.intern(ExprNode::Const(nat, 0));
        assert_eq!(c1, c2);
        assert_eq!(arenas.exprs.node(c1), ExprNode::Const(nat, 0));

        let app1 = arenas.exprs.intern(ExprNode::App(c1.0, ty.0));
        let app2 = arenas.exprs.intern(ExprNode::App(c2.0, ty.0));
        assert_eq!(app1, app2);
        let env_len = arenas.exprs.env_len();
        assert!(env_len > 0);

        // Scratch nodes live after env nodes and resolve via `node`.
        let s = arenas.exprs.push_scratch(ExprNode::BVar(7));
        let sh = Expr(s);
        assert!(sh.0 >= env_len as u32);
        assert_eq!(arenas.exprs.node(Expr(s)), ExprNode::BVar(7));
        // Env nodes are still resolvable.
        assert_eq!(arenas.exprs.node(ty), ExprNode::Sort(Level(0)));
        // `env_len` excludes scratch; `len` includes it.
        assert_eq!(arenas.exprs.env_len(), env_len);
        assert_eq!(arenas.exprs.len(), env_len + 1);
    }

    #[test]
    fn literals_level_lists_and_kv_maps() {
        let mut arenas = Arenas::new();
        let si = arenas.names.intern_str("hello");

        let l1 = arenas.exprs.intern_lit(Literal::StrVal(si));
        let l2 = arenas.exprs.intern_lit(Literal::StrVal(si));
        assert_eq!(l1, l2);
        assert_eq!(arenas.exprs.lit(l1), Literal::StrVal(si));

        let ul1 = arenas.exprs.intern_level_list(vec![0, 1, 2]);
        let ul2 = arenas.exprs.intern_level_list(vec![0, 1, 2]);
        assert_eq!(ul1, ul2);
        assert_eq!(arenas.exprs.level_list(ul1), &[0, 1, 2]);

        let key = arenas.names.intern_str_name(Name(0), "k");
        let kv1 = arenas.exprs.intern_kv(vec![(key, DataValue::OfBool(true))]);
        let kv2 = arenas.exprs.intern_kv(vec![(key, DataValue::OfBool(true))]);
        assert_eq!(kv1, kv2);
        assert_eq!(arenas.exprs.kv(kv1), &[(key, DataValue::OfBool(true))]);
    }

    #[test]
    fn drop_intern_maps_keeps_nodes_resolvable() {
        let mut arenas = Arenas::new();
        let nat = arenas.names.intern_path(&["Nat"]);
        let c = arenas.exprs.intern(ExprNode::Const(nat, 0));
        let l = arenas.levels.intern(LevelNode::Param(nat));
        let si = arenas.names.intern_str("x");
        let lit = arenas.exprs.intern_lit(Literal::StrVal(si));
        let ul = arenas.exprs.intern_level_list(vec![l.0]);
        let kv = arenas.exprs.intern_kv(vec![(nat, DataValue::OfString("v".to_string()))]);

        arenas.exprs.drop_intern_maps();

        // All handles still resolve after the interning maps are freed.
        assert_eq!(arenas.exprs.node(c), ExprNode::Const(nat, 0));
        assert_eq!(arenas.levels.node(l), LevelNode::Param(nat));
        assert_eq!(arenas.exprs.lit(lit), Literal::StrVal(si));
        assert_eq!(arenas.exprs.level_list(ul), &[l.0]);
        assert_eq!(arenas.exprs.kv(kv), &[(nat, DataValue::OfString("v".to_string()))]);
        assert_eq!(arenas.names.to_lean_string(nat), "Nat");
    }

    #[test]
    fn data_value_repr_str() {
        let mut arenas = Arenas::new();
        let name = arenas.names.intern_path(&["Foo", "Bar"]);

        assert_eq!(
            DataValue::OfString("a\"b".to_string()).repr_str(&arenas),
            "Lean.DataValue.ofString \"a\\\"b\""
        );
        assert_eq!(
            DataValue::OfBool(true).repr_str(&arenas),
            "Lean.DataValue.ofBool true"
        );
        assert_eq!(
            DataValue::OfNat("12345678901234567890".to_string()).repr_str(&arenas),
            "Lean.DataValue.ofNat 12345678901234567890"
        );
        // Negative ints are parenthesized at maxPrec.
        assert_eq!(
            DataValue::OfInt("-42".to_string()).repr_str(&arenas),
            "Lean.DataValue.ofInt (-42)"
        );
        assert_eq!(
            DataValue::OfName(name).repr_str(&arenas),
            "Lean.DataValue.ofName `Foo.Bar"
        );
    }

    #[test]
    fn constant_info_accessors() {
        let mut arenas = Arenas::new();
        let name = arenas.names.intern_path(&["M", "f"]);
        let ty = arenas.exprs.intern(ExprNode::Sort(Level(0)));
        let val = arenas.exprs.intern(ExprNode::BVar(0));
        let lvl = arenas.names.intern_path(&["u"]);

        let defn = ConstantInfo::Defn(DefinitionVal {
            val: ConstantVal {
                name,
                level_params: vec![lvl],
                ty,
            },
            value: val,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![],
        });
        assert_eq!(defn.name(), name);
        assert_eq!(defn.ty_expr(), ty);
        assert_eq!(defn.level_params(), &[lvl]);
        assert_eq!(defn.value_expr(), Some(val));

        let axiom = ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal {
                name,
                level_params: vec![],
                ty,
            },
            is_unsafe: false,
        });
        assert_eq!(axiom.name(), name);
        assert_eq!(axiom.value_expr(), None);
    }

    #[test]
    fn expr_debug_formatting() {
        let mut arenas = Arenas::new();
        let nat = arenas.names.intern_path(&["Nat"]);
        // Index 0 of the level-list table must exist before `Const` refs it.
        arenas.exprs.intern_level_list(vec![]);
        let nat_ty = arenas.exprs.intern(ExprNode::Const(nat, 0));
        let zero_str = arenas.names.intern_str("0");
        let zero_lit = arenas.exprs.intern_lit(Literal::NatVal(zero_str));
        let zero = arenas.exprs.intern(ExprNode::Lit(zero_lit));
        let app = arenas.exprs.intern(ExprNode::App(nat_ty.0, zero.0));
        assert_eq!(arenas.expr_debug(app), "app(const Nat [], natVal 0)");
    }
}
