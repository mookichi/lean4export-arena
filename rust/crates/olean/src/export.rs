//! NDJSON export: a faithful port of `Export.lean` (lean4export v3.1.0).
//!
//! Reads a decoded [`Env`] (the constants of a module plus all its
//! transitive imports) and reproduces byte-for-byte the NDJSON stream the
//! Lean exporter writes: one JSON object per line, with `in`/`il`/`ie`
//! index definitions for names, levels and expressions, and constant
//! dumps in `env.constants` (NameMap) order.
//!
//! Key details verified against Lean 4 v4.30.0 + the golden files:
//! - `Json` objects are `Std.TreeMap`s: keys are always emitted sorted
//!   (byte-wise `String` order).
//! - `getIdx` assigns an index *after* the children of a node have been
//!   dumped (`idx := m.size`), so index allocation order matters.
//! - `bvar` expressions are cached like any other node (upstream
//!   behavior): repeated occurrences become back-references, so no
//!   duplicate content lines are emitted (external checkers such as
//!   nanoda reject them). Expressions deeper than 1000 nodes are emitted
//!   without caching (`isDeepExpr`).
//! - `env.constants` iterates in `Name.quickCmp` order: by `Name.hash`
//!   first, then structurally. The hash is read from the `.olean` name
//!   objects (their first scalar slot).
//! - `NameSet` (Std.HashSet) iteration order is reproduced with the same
//!   separate-chaining table Std uses (power-of-two buckets, `cons` on
//!   insert, `scrambleHash & (n-1)` bucket index, doubling when
//!   `size*4/3 > buckets`).
//!
//! Expressions are arena handles ([`crate::value::Expr`]); the memo caches
//! (`hash_cache`, `deep_cache`, `size_cache`, `no_mdata`) are dense arrays
//! keyed by node index instead of `HashMap`s — with content interning,
//! identical nodes share one index, so a single slot covers every
//! occurrence, lookups are O(1) direct-indexed (no hashing, no buckets),
//! and the arrays can later be shared across threads as write-once atomic
//! slots (each node's memo value is a pure function of its index).

use std::collections::HashMap;
use std::io::Write;

use crate::value::{
    Arenas, BinderInfo, ConstantInfo, DefinitionSafety, Expr, ExprNode, KVIdx, Level, LevelIdx,
    LevelNode, Literal, Name, NameNode, NodeIdx, QuotKind, ReducibilityHints,
};

// ---------------------------------------------------------------------------
// JSON
// ---------------------------------------------------------------------------

/// A JSON value. Objects keep their fields sorted by key, mirroring Lean's
/// `Json` (backed by `Std.TreeMap`).
#[derive(Debug, Clone)]
pub enum Json {
    Bool(bool),
    Num(String),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    fn num(n: u64) -> Json {
        Json::Num(n.to_string())
    }

    /// Build an object, sorting the fields by key (byte order).
    fn obj(mut fields: Vec<(String, Json)>) -> Json {
        fields.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        Json::Obj(fields)
    }

    /// `Json.compress` — compact single-line rendering.
    pub fn compress(&self) -> String {
        let mut out = String::new();
        self.render(&mut out);
        out
    }

    fn render(&self, out: &mut String) {
        match self {
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Num(n) => out.push_str(n),
            Json::Str(s) => render_string(s, out),
            Json::Arr(elems) => {
                out.push('[');
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    e.render(out);
                }
                out.push(']');
            }
            Json::Obj(fields) => {
                out.push('{');
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    render_string(k, out);
                    out.push(':');
                    v.render(out);
                }
                out.push('}');
            }
        }
    }
}

/// `Json.renderString` / `escape` (Lean/Data/Json/Printer.lean): escape
/// `"`, `\`, `\n`, `\r`; emit all other chars >= 0x20 raw; render chars
/// below 0x20 as `\uXXXX`.
fn render_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        let v = c as u32;
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c if v >= 0x20 => out.push(c),
            c => {
                out.push_str("\\u");
                for shift in [12u32, 8, 4, 0] {
                    out.push(std::char::from_digit((v >> shift) & 0xf, 16).unwrap());
                }
                let _ = c;
            }
        }
    }
    out.push('"');
}

// ---------------------------------------------------------------------------
// Name ordering (NameMap / Std.HashMap bucket order)
// ---------------------------------------------------------------------------

/// `Nat.nextPowerOfTwo` (`Init/Data/Nat/Power2/Basic.lean`): the smallest
/// power of two ≥ `n` (1 for `n = 0`).
fn next_power_of_two(n: usize) -> usize {
    let mut p = 1usize;
    while p < n {
        p *= 2;
    }
    p
}

/// `DHashMap.Internal.numBucketsForCapacity` (`Defs.lean`): `capacity * 4 / 3`.
fn num_buckets_for_capacity(capacity: usize) -> usize {
    capacity * 4 / 3
}

/// `Std.DHashMap.Internal.scrambleHash` (`Index.lean`): xor-fold the hash
/// so all entropy lands in the low bits before masking to a bucket index.
fn scramble_hash(h: u64) -> u64 {
    let fold = h ^ (h >> 32);
    fold ^ (fold >> 16)
}

// ---------------------------------------------------------------------------
// NameSet simulation (`Std.TreeSet Name Name.quickCmp` iteration order)
// ---------------------------------------------------------------------------

/// `Name.quickCmp` (`Lean/Data/Name.lean`): compare by `Name.hash` (the
/// `m_hash` stored in the `.olean`), breaking ties with `quickCmpAux`
/// (components compared from the last backwards; numeric components sort
/// before string components).
fn quick_cmp(names: &crate::value::NameTable, a: Name, b: Name) -> std::cmp::Ordering {
    match names.hash(a).cmp(&names.hash(b)) {
        std::cmp::Ordering::Equal => quick_cmp_aux(names, a, b),
        ord => ord,
    }
}

fn quick_cmp_aux(names: &crate::value::NameTable, a: Name, b: Name) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    match (names.node(a), names.node(b)) {
        (NameNode::Anonymous, NameNode::Anonymous) => Equal,
        (NameNode::Anonymous, _) => Less,
        (_, NameNode::Anonymous) => Greater,
        (NameNode::Num { pre: pa, n: va, .. }, NameNode::Num { pre: pb, n: vb, .. }) => {
            match cmp_nat_str(names.str_of(va), names.str_of(vb)) {
                Equal => quick_cmp_aux(names, Name(pa), Name(pb)),
                ord => ord,
            }
        }
        (NameNode::Num { .. }, NameNode::Str { .. }) => Less,
        (NameNode::Str { .. }, NameNode::Num { .. }) => Greater,
        (NameNode::Str { pre: pa, s: sa, .. }, NameNode::Str { pre: pb, s: sb, .. }) => {
            match names.str_of(sa).cmp(names.str_of(sb)) {
                Equal => quick_cmp_aux(names, Name(pa), Name(pb)),
                ord => ord,
            }
        }
    }
}

/// Numeric comparison of the decimal string form of a `Name.num` value
/// (Lean's `compare v v'` on `Nat`).
fn cmp_nat_str(a: &str, b: &str) -> std::cmp::Ordering {
    let a = a.trim_start_matches('0');
    let b = b.trim_start_matches('0');
    let a = if a.is_empty() { "0" } else { a };
    let b = if b.is_empty() { "0" } else { b };
    match a.len().cmp(&b.len()) {
        std::cmp::Ordering::Equal => a.cmp(b),
        ord => ord,
    }
}

/// A `Lean.NameSet` (`Std.TreeSet Name Name.quickCmp`): a red-black tree
/// keyed by `Name.quickCmp`, whose in-order iteration the exporter relies
/// on for the recursor sets in `recursorMap` / `dump_inductive`.
struct LeanNameSet {
    names: Vec<Name>,
}

impl LeanNameSet {
    fn new() -> LeanNameSet {
        LeanNameSet { names: Vec::new() }
    }

    fn contains(&self, n: Name) -> bool {
        self.names.contains(&n)
    }

    fn insert(&mut self, n: Name) {
        if !self.contains(n) {
            self.names.push(n);
        }
    }

    /// In-order (`quickCmp`-sorted) iteration.
    fn to_vec(&self, names: &crate::value::NameTable) -> Vec<Name> {
        let mut v = self.names.clone();
        v.sort_by(|&a, &b| quick_cmp(names, a, b));
        v
    }
}

// ---------------------------------------------------------------------------
// Env
// ---------------------------------------------------------------------------

/// The environment: every constant of a module plus its transitive imports,
/// in `env.constants` (NameMap) order.
///
/// Constants are owned values (not `Rc`s): expression nodes live in the
/// [`Arenas`] and are referenced by `Copy` handles, so no per-constant heap
/// indirection is needed.
#[derive(Debug, Default)]
pub struct Env {
    /// Constants in insertion order (the order `importModules` would add
    /// them). `finalize` reorders this into `env.constants.toList` order
    /// (the `Std.HashMap` bucket order, reversed — see below).
    pub constants: Vec<(Name, ConstantInfo)>,
    by_name: HashMap<Name, usize>,
    /// `numPrivateConsts` from `importModules` (`finalizeImport`): the sum
    /// of `data.constants.size` over all imported modules, including
    /// duplicates. This sizes the `Std.HashMap` backing `env.constants`,
    /// so the bucket count depends on it even when duplicates are dropped.
    num_private_consts: usize,
}

impl Env {
    pub fn new() -> Env {
        Env {
            constants: Vec::new(),
            by_name: HashMap::new(),
            num_private_consts: 0,
        }
    }

    /// Insert one constant (later duplicates win, matching `env.constants`
    /// insertion). Caller must call `finalize` before iterating.
    pub fn insert_constant(&mut self, ci: ConstantInfo) {
        let name = ci.name();
        match self.by_name.get(&name) {
            Some(&idx) => self.constants[idx] = (name, ci),
            None => {
                self.by_name.insert(name, self.constants.len());
                self.constants.push((name, ci));
            }
        }
    }

    /// Record one imported module's raw constant count (for `numPrivateConsts`).
    pub fn add_module_constants(&mut self, n: usize) {
        self.num_private_consts += n;
    }

    /// Reorder `constants` into `env.constants.toList` order and rebuild
    /// the lookup table.
    ///
    /// Lean's `Environment.constants` is an `SMap` wrapping a
    /// `Std.HashMap` (separate chaining; the bucket count is always a power
    /// of two). `SMap.toList` is `m.fold (init := []) (a,b)::es`, i.e. the
    /// **reverse** of the HashMap's fold order. `Std.HashMap`'s fold visits
    /// buckets `0..sz-1` ascending, and within each bucket the `AssocList`
    /// from the head — and since `insert` conses to the head, a bucket's
    /// list is in reverse insertion order. So the final `toList` order is
    /// buckets descending, each bucket in insertion order.
    ///
    /// The bucket count is `nextPowerOfTwo(numBucketsForCapacity capacity)`
    /// with `capacity = numPrivateConsts + numPublicConsts` (here
    /// `numPublicConsts = 0`), and since the map is pre-sized to the full
    /// constant count, `expandIfNecessary` never fires.
    /// Reorder `constants` into `env.constants.toList` order. `names`
    /// provides the stored `Name.hash` values driving the bucket order.
    pub fn finalize(&mut self, names: &crate::value::NameTable) {
        let n = self.constants.len();
        if n == 0 {
            return;
        }
        let capacity = self.num_private_consts.max(n);
        let sz = next_power_of_two(num_buckets_for_capacity(capacity)).max(1);
        // Buckets hold indices into `constants` in insertion order.
        let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); sz];
        for (i, (name, _)) in self.constants.iter().enumerate() {
            let idx = (scramble_hash(names.hash(*name)) & (sz as u64 - 1)) as usize;
            buckets[idx].push(i);
        }
        let mut order = Vec::with_capacity(n);
        for b in buckets.iter().rev() {
            order.extend_from_slice(b);
        }
        let old = std::mem::take(&mut self.constants);
        self.constants = order.into_iter().map(|i| old[i].clone()).collect();
        self.by_name.clear();
        for (i, (n, _)) in self.constants.iter().enumerate() {
            self.by_name.insert(*n, i);
        }
    }

    pub fn find(&self, n: &Name) -> Option<&ConstantInfo> {
        self.by_name.get(n).map(|&i| &self.constants[i].1)
    }

    /// Iterate constants in NameMap order.
    pub fn iter(&self) -> impl Iterator<Item = (&Name, &ConstantInfo)> {
        self.constants.iter().map(|(n, ci)| (n, ci))
    }

    pub fn find_index(&self, n: &Name) -> Option<usize> {
        self.by_name.get(n).copied()
    }
}

// ---------------------------------------------------------------------------
// Exporter
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, Default)]
pub struct ExportOptions {
    pub export_mdata: bool,
    pub export_unsafe: bool,
}

/// Depth at which `isDeepExpr` gives up on caching (`> 1000`).
const DEEP_EXPR_THRESHOLD: u32 = 1000;

/// Alpha-equivalence mirroring Lean's `Expr.eqv` (`expr_eq_fn<false>`):
/// binder names and annotations are ignored for `lam`/`forallE`; the
/// `letE` binder name is ignored but `nondep` is compared; `mdata`
/// compares the wrapped expr and the KVMap; `proj`/`const`/`sort` are
/// structural on their non-expr fields.
///
/// Handles make identity comparison O(1) (`a == b`): with content
/// interning, the same node index means the same subtree.
pub fn expr_alpha_eq(arenas: &Arenas, a: Expr, b: Expr) -> bool {
    fn go(arenas: &Arenas, a: Expr, b: Expr) -> bool {
        // Interning fast-path: same index == structurally identical.
        if a == b {
            return true;
        }
        match (arenas.exprs.node(a), arenas.exprs.node(b)) {
            (ExprNode::BVar(i), ExprNode::BVar(j)) => i == j,
            (ExprNode::FVar(n1), ExprNode::FVar(n2)) => n1 == n2,
            (ExprNode::MVar(n1), ExprNode::MVar(n2)) => n1 == n2,
            (ExprNode::Sort(l1), ExprNode::Sort(l2)) => l1 == l2,
            (ExprNode::Const(n1, us1), ExprNode::Const(n2, us2)) => {
                n1 == n2 && us1 == us2
            }
            (ExprNode::App(f1, a1), ExprNode::App(f2, a2)) => {
                go(arenas, Expr(f1), Expr(f2)) && go(arenas, Expr(a1), Expr(a2))
            }
            (ExprNode::Lam(_, t1, b1, _), ExprNode::Lam(_, t2, b2, _)) => {
                go(arenas, Expr(t1), Expr(t2)) && go(arenas, Expr(b1), Expr(b2))
            }
            (ExprNode::ForallE(_, t1, b1, _), ExprNode::ForallE(_, t2, b2, _)) => {
                go(arenas, Expr(t1), Expr(t2)) && go(arenas, Expr(b1), Expr(b2))
            }
            (ExprNode::LetE(_, t1, v1, b1, nd1), ExprNode::LetE(_, t2, v2, b2, nd2)) => {
                nd1 == nd2
                    && go(arenas, Expr(t1), Expr(t2))
                    && go(arenas, Expr(v1), Expr(v2))
                    && go(arenas, Expr(b1), Expr(b2))
            }
            (ExprNode::Lit(l1), ExprNode::Lit(l2)) => l1 == l2,
            (ExprNode::MData(k1, e1), ExprNode::MData(k2, e2)) => {
                k1 == k2 && go(arenas, Expr(e1), Expr(e2))
            }
            (ExprNode::Proj(s1, i1, e1), ExprNode::Proj(s2, i2, e2)) => {
                s1 == s2 && i1 == i2 && go(arenas, Expr(e1), Expr(e2))
            }
            _ => false,
        }
    }
    go(arenas, a, b)
}

/// Mix two u32 hash values (FNV-style avalanche, good enough for buckets;
/// collisions are resolved by `expr_alpha_eq`).
fn mix_hash(a: u32, b: u32) -> u32 {
    a.wrapping_mul(0x0100_0193).rotate_left(13) ^ b.wrapping_mul(0x85eb_ca6b)
}

/// A cheap deterministic u32 hash of any `Hash` value (used for `Name`,
/// `Level`, `Literal`, `KVMap` in the memoized alpha-hash). Interning makes
/// handle hashing consistent: equal content ⟺ equal handle.
fn hash_u32<T: std::hash::Hash>(x: &T) -> u32 {
    use std::hash::Hasher;
    let mut s = std::collections::hash_map::DefaultHasher::new();
    x.hash(&mut s);
    s.finish() as u32
}

/// One entry of the `visited_exprs` alpha-dedup map: an emitted expression
/// (`node`), its subtree size (cheap pre-filter) and the index it got.
/// The map is keyed by the (memoized) alpha-hash; `eq` is done by the
/// exporter, which holds the arenas.
type VisitedExpr = (u32, Expr, u64);

pub struct Exporter<'a, W: Write> {
    env: &'a Env,
    arenas: &'a mut Arenas,
    opts: ExportOptions,
    out: W,
    /// Output index per name, dense array keyed by name index (`u64::MAX`
    /// = not yet dumped). `name_count` is the next index to assign.
    visited_names: Vec<u64>,
    /// Output index per level, dense array keyed by level index.
    visited_levels: Vec<u64>,
    /// `expr index` dedup table: `hash → (size, expr, idx)` for the first
    /// node with each alpha-hash, plus an overflow map for the rare
    /// hash-colliding buckets. ~99.6% of buckets hold a single entry
    /// (33.68M of 33.81M entries at 5K Mathlib constants), so the
    /// per-bucket `Vec` of the previous `HashMap<u32, Vec<..>>` wasted a
    /// 24-byte header + malloc rounding per entry (~1.8GB). The map is
    /// shardable by hash bits for multi-threaded export.
    visited_exprs: HashMap<u32, VisitedExpr>,
    visited_overflow: HashMap<u32, Vec<VisitedExpr>>,
    expr_count: u64,
    visited_constants: std::collections::HashSet<Name>,
    recursor_map: HashMap<Name, LeanNameSet>,
    /// Memoized alpha-hash per node index, dense array (stored as
    /// `hash + 1`, `0` = uncomputed; Lean's cached `Expr.Data.hash`).
    /// Nodes are interned and immutable, so the hash is a pure function of
    /// the index — direct-indexed O(1), no hashing, MT-ready as atomic
    /// write-once slots.
    hash_cache: Vec<u32>,
    /// Memoized `removeMData` results keyed by original env node index
    /// (Lean's `noMDataExprs`), dense array (`u32::MAX` = uncomputed). The
    /// stripped tree of an env node is a pure function of the node, so the
    /// memo is **global** (never cleared per constant): stripping once per
    /// env node — instead of once per (constant, node) pair — removes the
    /// per-constant re-strip work and bounds the scratch section by the
    /// distinct stripped subtrees.
    no_mdata: Vec<u32>,
    /// Memoized max `lam`/`forallE` nesting depth per node index, dense
    /// array (stored as `depth + 1`, `0` = uncomputed). See `hash_cache`.
    deep_cache: Vec<u32>,
    /// Memoized subtree node count per node index, dense array (`0` =
    /// uncomputed; sizes are always ≥ 1). See `hash_cache`.
    size_cache: Vec<u32>,
    /// Next output index for names/levels (the dense arrays' `.len()` is
    /// the largest interned index + 1, not the count of dumped entries).
    name_count: u64,
    level_count: u64,
    /// Precomputed `needs_strip` flags: for every env node, whether its
    /// subtree contains an `mdata` node or a `nondep`-`letE`. Computed once
    /// in a single bottom-up pass (`ExprTable` guarantees children have
    /// smaller indices than their parents). `needs_strip` is called for
    /// every constant's type/value root and for every node inside
    /// `strip_mdata`; the previous unmemoized recursive walk re-visited
    /// shared interned subtrees along every path — for the heavily-shared
    /// DAGs of tactic-generated proofs this is exponential (a single
    /// `needs_strip` call ran for 10+ minutes on Mathlib).
    has_mdata: Vec<bool>,
}

impl<'a, W: Write> Exporter<'a, W> {
    pub fn new(env: &'a Env, arenas: &'a mut Arenas, opts: ExportOptions, out: W) -> Exporter<'a, W> {
        // `initState`: map each inductive to the set of recursors that
        // recurse on it. It iterates `for (_, constInfo) in env.constants`,
        // whose `ForIn` is `SMap.forM` = `map₁.forM` — the raw
        // `Std.HashMap` fold order (buckets ascending, newest-first within
        // each bucket), i.e. the **reverse** of `env.constants.toList`
        // (which is what the main export loop uses). `env.constants` here
        // is stored in `toList` order, so iterate it in reverse.
        let mut recursor_map: HashMap<Name, LeanNameSet> = HashMap::new();
        for (name, ci) in env.constants.iter().rev() {
            if let ConstantInfo::Rec(rec) = ci {
                for &ind in &rec.all {
                    recursor_map
                        .entry(ind)
                        .or_insert_with(LeanNameSet::new)
                        .insert(*name);
                }
            }
        }
        // Bottom-up mdata-presence flags: children always have smaller
        // indices than their parents (decode interns children first;
        // `push_scratch` appends after), so one pass over index order is a
        // valid topological order. `Vec<bool>` is bit-packed (~1 bit per
        // node).
        let n_env = arenas.exprs.env_len();
        let mut has_mdata = vec![false; n_env];
        for i in 0..n_env {
            has_mdata[i] = match arenas.exprs.node(Expr(i as NodeIdx)) {
                ExprNode::MData(_, _) => true,
                ExprNode::App(f, a) => has_mdata[f as usize] || has_mdata[a as usize],
                ExprNode::Lam(_, t, b, _) => has_mdata[t as usize] || has_mdata[b as usize],
                ExprNode::ForallE(_, t, b, _) => has_mdata[t as usize] || has_mdata[b as usize],
                ExprNode::LetE(_, t, v, b, nd) => {
                    nd || has_mdata[t as usize] || has_mdata[v as usize] || has_mdata[b as usize]
                }
                ExprNode::Proj(_, _, st) => has_mdata[st as usize],
                _ => false,
            };
        }
        Exporter {
            env,
            arenas,
            opts,
            out,
            visited_names: vec![0u64],
            visited_levels: vec![0u64],
            visited_exprs: HashMap::new(),
            visited_overflow: HashMap::new(),
            deep_cache: Vec::new(),
            size_cache: Vec::new(),
            has_mdata,
            name_count: 1,
            level_count: 1,
            expr_count: 0,
            visited_constants: std::collections::HashSet::new(),
            recursor_map,
            hash_cache: Vec::new(),
            no_mdata: Vec::new(),
        }
    }

    fn emit(&mut self, line: &str) {
        let _ = self.out.write_all(line.as_bytes());
        let _ = self.out.write_all(b"\n");
    }

    /// Copy an expression node out of the arena (handles are `Copy`, so
    /// the borrow ends immediately — required before any `&mut self` call).
    fn node(&self, e: Expr) -> ExprNode {
        self.arenas.exprs.node(e)
    }

    /// Grow a dense memo array to cover `idx`. Children are interned
    /// before parents and scratch nodes are appended, so the arrays only
    /// ever extend; `fill` is the "uncomputed" sentinel.
    fn grow<T: Copy>(v: &mut Vec<T>, idx: usize, fill: T) {
        if idx >= v.len() {
            v.resize(idx + 1, fill);
        }
    }

    // ---- dumpName / dumpLevel --------------------------------------------

    fn dump_name(&mut self, n: Name) -> Result<u64, String> {
        let key = n.0 as usize;
        Self::grow(&mut self.visited_names, key, u64::MAX);
        let v = self.visited_names[key];
        if v != u64::MAX {
            return Ok(v);
        }
        let body = self.name_json(n)?;
        let idx = self.name_count;
        self.name_count += 1;
        let line = Json::obj(vec![
            ("in".to_string(), Json::num(idx)),
            (body.0, body.1),
        ])
        .compress();
        self.emit(&line);
        self.visited_names[key] = idx;
        Ok(idx)
    }

    /// The body of a name definition (without the `in` index).
    fn name_json(&mut self, n: Name) -> Result<(String, Json), String> {
        match self.arenas.names.node(n) {
            NameNode::Anonymous => Err("dumpName: anonymous is pre-cached".to_string()),
            NameNode::Str { pre, s, .. } => {
                let pre_idx = self.dump_name(Name(pre))?;
                Ok((
                    "str".to_string(),
                    Json::obj(vec![
                        ("pre".to_string(), Json::num(pre_idx)),
                        ("str".to_string(), Json::Str(self.arenas.names.str_of(s).to_string())),
                    ]),
                ))
            }
            NameNode::Num { pre, n, .. } => {
                let pre_idx = self.dump_name(Name(pre))?;
                Ok((
                    "num".to_string(),
                    Json::obj(vec![
                        ("pre".to_string(), Json::num(pre_idx)),
                        ("i".to_string(), Json::Num(self.arenas.names.str_of(n).to_string())),
                    ]),
                ))
            }
        }
    }

    fn dump_level(&mut self, l: Level) -> Result<u64, String> {
        let key = l.0 as usize;
        Self::grow(&mut self.visited_levels, key, u64::MAX);
        let v = self.visited_levels[key];
        if v != u64::MAX {
            return Ok(v);
        }
        let body = self.level_json(l)?;
        let idx = self.level_count;
        self.level_count += 1;
        let line = Json::obj(vec![
            ("il".to_string(), Json::num(idx)),
            (body.0, body.1),
        ])
        .compress();
        self.emit(&line);
        self.visited_levels[key] = idx;
        Ok(idx)
    }

    fn level_json(&mut self, l: Level) -> Result<(String, Json), String> {
        match self.arenas.levels.node(l) {
            LevelNode::Zero | LevelNode::MVar(_) => {
                Err("dumpLevel: zero/mvar are pre-cached or unreachable".to_string())
            }
            LevelNode::Succ(x) => Ok(("succ".to_string(), Json::num(self.dump_level(Level(x))?))),
            LevelNode::Max(a, b) => Ok((
                "max".to_string(),
                Json::Arr(vec![
                    Json::num(self.dump_level(Level(a))?),
                    Json::num(self.dump_level(Level(b))?),
                ]),
            )),
            LevelNode::Imax(a, b) => Ok((
                "imax".to_string(),
                Json::Arr(vec![
                    Json::num(self.dump_level(Level(a))?),
                    Json::num(self.dump_level(Level(b))?),
                ]),
            )),
            LevelNode::Param(n) => Ok(("param".to_string(), Json::num(self.dump_name(n)?))),
        }
    }

    // ---- dumpExpr ---------------------------------------------------------

    fn dump_expr(&mut self, e: Expr) -> Result<u64, String> {
        if self.opts.export_mdata || !self.needs_strip(e) {
            // `--export-mdata`, or the tree contains no `mdata` and no
            // `letE` with `nondep := true`, so `removeMData` would be a
            // no-op. Dump the original `e` directly.
            self.dump_expr_aux(e)
        } else {
            // Memoized `removeMData` (Lean's `noMDataExprs`), keyed by the
            // env node's own index — stable, and the memo map is cleared
            // per constant (like `Main.lean`'s `noMDataExprs := {}`).
            let stripped = self.strip_mdata(e);
            self.dump_expr_aux(stripped)
        }
    }

    /// Memoized subtree node count (bottom-up, like `lam_depth_memo`), so
    /// `visited_exprs` can reject hash-colliding candidates of different
    /// sizes without a structural comparison.
    fn size_memo(&mut self, e: Expr) -> u32 {
        let key = e.0 as usize;
        Self::grow(&mut self.size_cache, key, 0);
        let v = self.size_cache[key];
        if v != 0 {
            return v;
        }
        let s = match self.node(e) {
            ExprNode::App(f, a) => {
                self.size_memo(Expr(f)).saturating_add(self.size_memo(Expr(a))).saturating_add(1)
            }
            ExprNode::Lam(_, t, b, _) | ExprNode::ForallE(_, t, b, _) => self
                .size_memo(Expr(t))
                .saturating_add(self.size_memo(Expr(b)))
                .saturating_add(1),
            ExprNode::LetE(_, t, v, b, _) => self
                .size_memo(Expr(t))
                .saturating_add(self.size_memo(Expr(v)))
                .saturating_add(self.size_memo(Expr(b)))
                .saturating_add(1),
            ExprNode::Proj(_, _, st) => self.size_memo(Expr(st)).saturating_add(1),
            ExprNode::MData(_, inner) => self.size_memo(Expr(inner)).saturating_add(1),
            _ => 1,
        };
        self.size_cache[key] = s;
        s
    }

    /// Memoized maximum `lam`/`forallE` nesting depth, keyed by node index.
    /// Cleared together with `no_mdata` via `clear_no_mdata`, which already
    /// drops the stripped nodes whose indices are reused.
    ///
    /// The previous `is_deep_expr` re-walked the whole subtree on every
    /// call: for the ~2e5-deep `app` spines of tactic-generated proofs this
    /// is O(spine) per node (O(n^2) per tree) — ~2e10 node visits on the
    /// full Lean export. Only `lam`/`forallE` increase the depth counter,
    /// so the depth is a pure property of the subtree, memoizable bottom-up
    /// (children are looked up in the memo, so the whole export is O(total
    /// env nodes)).
    fn lam_depth_memo(&mut self, e: Expr) -> u32 {
        let key = e.0 as usize;
        Self::grow(&mut self.deep_cache, key, 0);
        let v = self.deep_cache[key];
        if v != 0 {
            return v.wrapping_sub(1);
        }
        let d = match self.node(e) {
            ExprNode::Lam(_, _, b, _) | ExprNode::ForallE(_, _, b, _) => 1 + self.lam_depth_memo(Expr(b)),
            ExprNode::App(f, a) => self.lam_depth_memo(Expr(f)).max(self.lam_depth_memo(Expr(a))),
            ExprNode::LetE(_, _, _, b, _) => self.lam_depth_memo(Expr(b)),
            ExprNode::Proj(_, _, e2) => self.lam_depth_memo(Expr(e2)),
            ExprNode::MData(_, e2) => self.lam_depth_memo(Expr(e2)),
            _ => 0,
        };
        self.deep_cache[key] = d.wrapping_add(1);
        d
    }

    /// Whether `removeMData` can change `e`: true iff the subtree contains
    /// an `mdata` node, or a `letE` with `nondep := true` (which
    /// `removeMData` rewrites to `false`). Mirrors the parts of
    /// `Export.lean`'s `removeMData` that actually transform the tree.
    ///
    /// O(1): precomputed in `Exporter::new` (see `has_mdata`).
    fn needs_strip(&self, e: Expr) -> bool {
        let i = e.0 as usize;
        if i < self.has_mdata.len() {
            return self.has_mdata[i];
        }
        // Defensive fallback for out-of-range handles. Never hit in
        // practice: `dump_expr` (roots) and `strip_mdata` (recursion) only
        // query env nodes; scratch nodes are only ever produced by
        // `strip_mdata`, never walked.
        self.needs_strip_walk(e)
    }

    /// Unmemoized recursive `needs_strip` (defensive fallback only).
    fn needs_strip_walk(&self, e: Expr) -> bool {
        match self.node(e) {
            ExprNode::MData(_, _) => true,
            ExprNode::App(f, a) => self.needs_strip(Expr(f)) || self.needs_strip(Expr(a)),
            ExprNode::Lam(_, t, b, _) => self.needs_strip(Expr(t)) || self.needs_strip(Expr(b)),
            ExprNode::ForallE(_, t, b, _) => self.needs_strip(Expr(t)) || self.needs_strip(Expr(b)),
            ExprNode::LetE(_, t, v, b, nd) => {
                nd || self.needs_strip(Expr(t)) || self.needs_strip(Expr(v)) || self.needs_strip(Expr(b))
            }
            ExprNode::Proj(_, _, st) => self.needs_strip(Expr(st)),
            _ => false,
        }
    }

    /// Memoized `removeMData`: returns the stripped subtree for `e`, keyed
    /// by the **env node's own index** (stable for the whole export).
    /// Mirrors `Export.lean`'s `noMDataExprs` cache, including the `letE`
    /// rewrite `nondep := false`.
    ///
    /// Subtrees that `removeMData` would not change (no `mdata`, no
    /// `nondep`-`letE`) are returned as the original env node itself;
    /// changed subtrees get fresh scratch nodes (appended after the env
    /// nodes). Every result — changed or not — is stored in the dense
    /// `no_mdata` under the stable env index, so repeated strips of the
    /// same env node return the same handle. The memo is global (not
    /// cleared per constant): a stripped env subtree is a pure function of
    /// the node, so stripping once per node is both faster and bounds the
    /// scratch section by the distinct stripped subtrees.
    fn strip_mdata(&mut self, e: Expr) -> Expr {
        let key = e.0 as usize;
        Self::grow(&mut self.no_mdata, key, u32::MAX);
        let v = self.no_mdata[key];
        if v != u32::MAX {
            return Expr(v);
        }
        let stripped: Expr = if !self.needs_strip(e) {
            e
        } else {
            match self.node(e) {
                ExprNode::MData(_, inner) => self.strip_mdata(Expr(inner)),
                ExprNode::App(f, a) => {
                    let sf = self.strip_mdata(Expr(f));
                    let sa = self.strip_mdata(Expr(a));
                    Expr(self.arenas.exprs.push_scratch(ExprNode::App(sf.0, sa.0)))
                }
                ExprNode::Lam(n, t, b, bi) => {
                    let st = self.strip_mdata(Expr(t));
                    let sb = self.strip_mdata(Expr(b));
                    Expr(self.arenas.exprs.push_scratch(ExprNode::Lam(n, st.0, sb.0, bi)))
                }
                ExprNode::ForallE(n, t, b, bi) => {
                    let st = self.strip_mdata(Expr(t));
                    let sb = self.strip_mdata(Expr(b));
                    Expr(self.arenas.exprs.push_scratch(ExprNode::ForallE(n, st.0, sb.0, bi)))
                }
                // `removeMData` (Export.lean) rewrites every `letE` with
                // `nondep := false` (via `updateLet! ... false`).
                ExprNode::LetE(n, t, v, b, _nd) => {
                    let st = self.strip_mdata(Expr(t));
                    let sv = self.strip_mdata(Expr(v));
                    let sb = self.strip_mdata(Expr(b));
                    Expr(self
                        .arenas
                        .exprs
                        .push_scratch(ExprNode::LetE(n, st.0, sv.0, sb.0, false)))
                }
                ExprNode::Proj(s, i, st) => {
                    let ss = self.strip_mdata(Expr(st));
                    Expr(self.arenas.exprs.push_scratch(ExprNode::Proj(s, i, ss.0)))
                }
                other => Expr(self.arenas.exprs.push_scratch(other)),
            }
        };
        self.no_mdata[key] = stripped.0;
        stripped
    }

    fn visited_expr_lookup(&self, hash: u32, size: u32, e: Expr) -> Option<u64> {
        if let Some(&(s, x, idx)) = self.visited_exprs.get(&hash) {
            if s == size && expr_alpha_eq(&*self.arenas, e, x) {
                return Some(idx);
            }
        }
        self.visited_overflow
            .get(&hash)?
            .iter()
            .find(|(s, x, _)| *s == size && expr_alpha_eq(&*self.arenas, e, *x))
            .map(|(_, _, idx)| *idx)
    }

    fn visited_expr_insert(&mut self, hash: u32, size: u32, e: Expr, idx: u64) {
        // Only called on a lookup miss, so a present main entry is a
        // different structure sharing the hash → overflow bucket.
        match self.visited_exprs.entry(hash) {
            std::collections::hash_map::Entry::Occupied(_) => {
                self.visited_overflow.entry(hash).or_default().push((size, e, idx));
            }
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert((size, e, idx));
            }
        }
    }

    fn dump_expr_aux(&mut self, e: Expr) -> Result<u64, String> {
        // `bvar` nodes go through the normal cached path like every other
        // expression (matching upstream lean4export and Lean's own kernel,
        // where a de Bruijn index is a shared value): repeated occurrences
        // of `bvar N` become back-references, so the export never contains
        // duplicate content lines (external checkers such as nanoda reject
        // them).
        if self.lam_depth_memo(e) > DEEP_EXPR_THRESHOLD {
            // Deep expressions are emitted without caching (matching the
            // Lean exporter's `isDeepExpr`), but the index must be
            // assigned *after* the children are dumped — like the cached
            // path — so the stream stays index-continuous (children first,
            // parent last). Reserving the parent's index before dumping
            // the children emits the children's lines with *larger*
            // indices before the parent's line, which external checkers
            // reject as a back-reference mismatch (e.g. a 500-deep
            // `forallE` chain in Phase0Test produced a 500-index gap).
            let body = self.expr_body_json(e)?;
            let idx = self.expr_count;
            self.expr_count += 1;
            let line = Json::obj(vec![
                (body.0, body.1),
                ("ie".to_string(), Json::num(idx)),
            ])
            .compress();
            self.emit(&line);
            return Ok(idx);
        }
        let hash = self.alpha_hash(e);
        let size = self.size_memo(e);
        if let Some(idx) = self.visited_expr_lookup(hash, size, e) {
            return Ok(idx);
        }
        let body = self.expr_body_json(e)?;
        let idx = self.expr_count;
        self.expr_count += 1;
        let line = Json::obj(vec![
            (body.0, body.1),
            ("ie".to_string(), Json::num(idx)),
        ])
        .compress();
        self.emit(&line);
        self.visited_expr_insert(hash, size, e, idx);
        Ok(idx)
    }

    /// Memoized alpha-hash of a node, keyed by node index. Since nodes are
    /// immutable and interned, the hash never changes and is computed at
    /// most once per unique node — mirroring Lean's cached `Expr.Data.hash`.
    /// `u32` matches Lean's 32-bit hash field.
    fn alpha_hash(&mut self, e: Expr) -> u32 {
        let key = e.0 as usize;
        Self::grow(&mut self.hash_cache, key, 0);
        let v = self.hash_cache[key];
        if v != 0 {
            return v.wrapping_sub(1);
        }
        let h = self.alpha_hash_uncached(e);
        self.hash_cache[key] = h.wrapping_add(1);
        h
    }

    fn alpha_hash_uncached(&mut self, e: Expr) -> u32 {
        // Mix a per-constructor tag with the (memoized) hashes of the
        // compared fields; equivalent to Lean's `Expr.hash` modulo
        // collisions. Binder names/info are deliberately NOT hashed for
        // `lam`/`forallE`/`letE`, matching `expr_alpha_eq`.
        let tag = match self.node(e) {
            ExprNode::BVar(_) => 0u32,
            ExprNode::FVar(_) => 1,
            ExprNode::MVar(_) => 2,
            ExprNode::Sort(_) => 3,
            ExprNode::Const(_, _) => 4,
            ExprNode::App(_, _) => 5,
            ExprNode::Lam(_, _, _, _) => 6,
            ExprNode::ForallE(_, _, _, _) => 7,
            ExprNode::LetE(_, _, _, _, _) => 8,
            ExprNode::Lit(_) => 9,
            ExprNode::MData(_, _) => 10,
            ExprNode::Proj(_, _, _) => 11,
        };
        let mut h = tag;
        match self.node(e) {
            ExprNode::BVar(i) => h = mix_hash(h, i as u32),
            ExprNode::FVar(n) => h = mix_hash(h, hash_u32(&n)),
            ExprNode::MVar(n) => h = mix_hash(h, hash_u32(&n)),
            ExprNode::Sort(l) => h = mix_hash(h, hash_u32(&l)),
            ExprNode::Const(n, us) => {
                h = mix_hash(h, hash_u32(&n));
                for &u in self.arenas.exprs.level_list(us) {
                    h = mix_hash(h, hash_u32(&Level(u)));
                }
            }
            ExprNode::App(f, a) => {
                h = mix_hash(h, self.alpha_hash(Expr(f)));
                h = mix_hash(h, self.alpha_hash(Expr(a)));
            }
            ExprNode::Lam(_, t, b, _) | ExprNode::ForallE(_, t, b, _) => {
                h = mix_hash(h, self.alpha_hash(Expr(t)));
                h = mix_hash(h, self.alpha_hash(Expr(b)));
            }
            ExprNode::LetE(_, t, v, b, nd) => {
                h = mix_hash(h, u32::from(nd));
                h = mix_hash(h, self.alpha_hash(Expr(t)));
                h = mix_hash(h, self.alpha_hash(Expr(v)));
                h = mix_hash(h, self.alpha_hash(Expr(b)));
            }
            ExprNode::Lit(l) => h = mix_hash(h, hash_u32(&l)),
            ExprNode::MData(k, e2) => {
                h = mix_hash(h, hash_u32(&k));
                h = mix_hash(h, self.alpha_hash(Expr(e2)));
            }
            ExprNode::Proj(s, i, e2) => {
                h = mix_hash(h, hash_u32(&s));
                h = mix_hash(h, i as u32);
                h = mix_hash(h, self.alpha_hash(Expr(e2)));
            }
        }
        h
    }

    fn expr_body_json(&mut self, e: Expr) -> Result<(String, Json), String> {
        match self.node(e) {
            ExprNode::BVar(i) => Ok(("bvar".to_string(), Json::num(i))),
            ExprNode::FVar(_) | ExprNode::MVar(_) => {
                Err("cannot export free variables or metavariables".to_string())
            }
            ExprNode::MData(kv, inner) => {
                let data = self.kvmap_json(kv)?;
                let inner_idx = self.dump_expr_aux(Expr(inner))?;
                Ok((
                    "mdata".to_string(),
                    Json::obj(vec![
                        ("data".to_string(), data),
                        ("expr".to_string(), Json::num(inner_idx)),
                    ]),
                ))
            }
            ExprNode::Lit(l) => match self.arenas.exprs.lit(l) {
                Literal::NatVal(si) => {
                    self.dump_nat_deps()?;
                    Ok(("natVal".to_string(), Json::Str(self.arenas.names.str_of(si).to_string())))
                }
                Literal::StrVal(si) => {
                    self.dump_str_deps()?;
                    Ok(("strVal".to_string(), Json::Str(self.arenas.names.str_of(si).to_string())))
                }
            },
            ExprNode::Sort(l) => Ok(("sort".to_string(), Json::num(self.dump_level(l)?))),
            ExprNode::Const(n, us) => {
                let ni = self.dump_name(n)?;
                let us_list: Vec<LevelIdx> = self.arenas.exprs.level_list(us).to_vec();
                let mut us_arr = Vec::with_capacity(us_list.len());
                for u in us_list {
                    us_arr.push(Json::num(self.dump_level(Level(u))?));
                }
                Ok((
                    "const".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), Json::num(ni)),
                        ("us".to_string(), Json::Arr(us_arr)),
                    ]),
                ))
            }
            ExprNode::App(f, a) => {
                let fi = self.dump_expr_aux(Expr(f))?;
                let ai = self.dump_expr_aux(Expr(a))?;
                Ok((
                    "app".to_string(),
                    Json::obj(vec![
                        ("fn".to_string(), Json::num(fi)),
                        ("arg".to_string(), Json::num(ai)),
                    ]),
                ))
            }
            ExprNode::Lam(n, t, b, bi) => {
                let ni = self.dump_name(n)?;
                let ti = self.dump_expr_aux(Expr(t))?;
                let bi_idx = self.dump_expr_aux(Expr(b))?;
                Ok((
                    "lam".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), Json::num(ni)),
                        ("type".to_string(), Json::num(ti)),
                        ("body".to_string(), Json::num(bi_idx)),
                        ("binderInfo".to_string(), binder_info_json(bi)),
                    ]),
                ))
            }
            ExprNode::ForallE(n, t, b, bi) => {
                let ni = self.dump_name(n)?;
                let ti = self.dump_expr_aux(Expr(t))?;
                let bi_idx = self.dump_expr_aux(Expr(b))?;
                Ok((
                    "forallE".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), Json::num(ni)),
                        ("type".to_string(), Json::num(ti)),
                        ("body".to_string(), Json::num(bi_idx)),
                        ("binderInfo".to_string(), binder_info_json(bi)),
                    ]),
                ))
            }
            ExprNode::LetE(n, t, v, b, nondep) => {
                let ni = self.dump_name(n)?;
                let ti = self.dump_expr_aux(Expr(t))?;
                let vi = self.dump_expr_aux(Expr(v))?;
                let bi_idx = self.dump_expr_aux(Expr(b))?;
                Ok((
                    "letE".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), Json::num(ni)),
                        ("type".to_string(), Json::num(ti)),
                        ("value".to_string(), Json::num(vi)),
                        ("body".to_string(), Json::num(bi_idx)),
                        ("nondep".to_string(), Json::Bool(nondep)),
                    ]),
                ))
            }
            ExprNode::Proj(s, i, st) => {
                let si = self.dump_name(s)?;
                let sti = self.dump_expr_aux(Expr(st))?;
                Ok((
                    "proj".to_string(),
                    Json::obj(vec![
                        ("typeName".to_string(), Json::num(si)),
                        ("idx".to_string(), Json::num(i)),
                        ("struct".to_string(), Json::num(sti)),
                    ]),
                ))
            }
        }
    }

    fn kvmap_json(&mut self, kv: KVIdx) -> Result<Json, String> {
        let mut fields = Vec::with_capacity(self.arenas.exprs.kv(kv).len());
        for (k, v) in self.arenas.exprs.kv(kv) {
            // `KVMap.toJson`: keys use `Name.toString` (no `«»` escaping);
            // values use `reprStr`.
            fields.push((
                self.arenas.names.to_string_plain(*k),
                Json::Str(v.repr_str(self.arenas)),
            ));
        }
        Ok(Json::obj(fields))
    }

    fn dump_nat_deps(&mut self) -> Result<(), String> {
        let nat = self.arenas.names.intern_path(&["Nat"]);
        if !self.visited_constants.contains(&nat) && self.env.find(&nat).is_some() {
            self.dump_constant(nat)?;
        }
        Ok(())
    }

    fn dump_str_deps(&mut self) -> Result<(), String> {
        let char_of_nat = self.arenas.names.intern_path(&["Char", "ofNat"]);
        if !self.visited_constants.contains(&char_of_nat) && self.env.find(&char_of_nat).is_some() {
            self.dump_constant(char_of_nat)?;
        }
        let string_of_byte_array = self.arenas.names.intern_path(&["String", "ofByteArray"]);
        if !self.visited_constants.contains(&string_of_byte_array)
            && self.env.find(&string_of_byte_array).is_some()
        {
            self.dump_constant(string_of_byte_array)?;
        }
        Ok(())
    }

    // ---- constants --------------------------------------------------------

    fn dump_constant(&mut self, c: Name) -> Result<(), String> {
        let ci = self
            .env
            .find(&c)
            .ok_or_else(|| format!("constant {} not found in environment", self.arenas.names.to_lean_string(c)))?;
        let is_unsafe = ci_is_unsafe(ci);
        if (is_unsafe && !self.opts.export_unsafe) || self.visited_constants.contains(&c) {
            return Ok(());
        }
        self.visited_constants.insert(c);
        match ci {
            ConstantInfo::Axiom(v) => {
                self.dump_deps(v.val.ty)?;
                let name = Json::num(self.dump_name(v.val.name)?);
                let level_params = self.dump_uparams(&v.val.level_params)?;
                let ty = Json::num(self.dump_expr(v.val.ty)?);
                self.dump_obj(vec![(
                    "axiom".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), name),
                        ("levelParams".to_string(), level_params),
                        ("type".to_string(), ty),
                        ("isUnsafe".to_string(), Json::Bool(v.is_unsafe)),
                    ]),
                )])?;
            }
            ConstantInfo::Defn(v) => {
                self.dump_deps(v.val.ty)?;
                self.dump_deps(v.value)?;
                let name = Json::num(self.dump_name(v.val.name)?);
                let level_params = self.dump_uparams(&v.val.level_params)?;
                let ty = Json::num(self.dump_expr(v.val.ty)?);
                let value = Json::num(self.dump_expr(v.value)?);
                let all = self.dump_names(&v.all)?;
                self.dump_obj(vec![(
                    "def".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), name),
                        ("levelParams".to_string(), level_params),
                        ("type".to_string(), ty),
                        ("value".to_string(), value),
                        ("hints".to_string(), hints_json(v.hints)),
                        ("safety".to_string(), safety_json(v.safety)),
                        ("all".to_string(), all),
                    ]),
                )])?;
            }
            ConstantInfo::Thm(v) => {
                self.dump_deps(v.val.ty)?;
                self.dump_deps(v.value)?;
                let name = Json::num(self.dump_name(v.val.name)?);
                let level_params = self.dump_uparams(&v.val.level_params)?;
                let ty = Json::num(self.dump_expr(v.val.ty)?);
                let value = Json::num(self.dump_expr(v.value)?);
                let all = self.dump_names(&v.all)?;
                self.dump_obj(vec![(
                    "thm".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), name),
                        ("levelParams".to_string(), level_params),
                        ("type".to_string(), ty),
                        ("value".to_string(), value),
                        ("all".to_string(), all),
                    ]),
                )])?;
            }
            ConstantInfo::Opaque(v) => {
                self.dump_deps(v.val.ty)?;
                self.dump_deps(v.value)?;
                let name = Json::num(self.dump_name(v.val.name)?);
                let level_params = self.dump_uparams(&v.val.level_params)?;
                let ty = Json::num(self.dump_expr(v.val.ty)?);
                let value = Json::num(self.dump_expr(v.value)?);
                let all = self.dump_names(&v.all)?;
                self.dump_obj(vec![(
                    "opaque".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), name),
                        ("levelParams".to_string(), level_params),
                        ("type".to_string(), ty),
                        ("value".to_string(), value),
                        ("all".to_string(), all),
                        ("isUnsafe".to_string(), Json::Bool(v.is_unsafe)),
                    ]),
                )])?;
            }
            ConstantInfo::Quot(_) => {
                // Always dump the full Quot package in the sensible order.
                let eq = self.arenas.names.intern_path(&["Eq"]);
                self.dump_constant(eq)?;
                for c in [
                    &["Quot"][..],
                    &["Quot", "mk"][..],
                    &["Quot", "lift"][..],
                    &["Quot", "ind"][..],
                ] {
                    let q = self.arenas.names.intern_path(c);
                    let qv = self
                        .env
                        .find(&q)
                        .ok_or_else(|| format!("constant {} not found in environment", self.arenas.names.to_lean_string(q)))?;
                    let (name, level_params, ty, kind) = match qv {
                        ConstantInfo::Quot(v) => {
                            (v.val.name, &v.val.level_params, v.val.ty, v.kind)
                        }
                        _ => return Err(format!("expected Quot constant, got {}", self.arenas.names.to_lean_string(q))),
                    };
                    self.visited_constants.insert(q);
                    let name = Json::num(self.dump_name(name)?);
                    let level_params = self.dump_uparams(level_params)?;
                    let ty = Json::num(self.dump_expr(ty)?);
                    self.dump_obj(vec![
                        ("quot".to_string(),
                        Json::obj(vec![
                            ("name".to_string(), name),
                            ("levelParams".to_string(), level_params),
                            ("type".to_string(), ty),
                            ("kind".to_string(), quot_kind_json(kind)),
                        ])),
                    ])?;
                }
            }
            ConstantInfo::Induct(base) => {
                self.dump_inductive(base)?;
            }
            ConstantInfo::Ctor(v) => {
                self.dump_constant(v.induct)?;
            }
            ConstantInfo::Rec(v) => {
                for &ind in &v.all {
                    self.dump_constant(ind)?;
                }
            }
        }
        Ok(())
    }

    fn dump_inductive(&mut self, base: &'a crate::value::InductiveVal) -> Result<(), String> {
        let env: &'a Env = self.env;
        let mut ind_vals: Vec<&'a crate::value::InductiveVal> = Vec::new();
        let mut ctor_vals: Vec<&'a crate::value::ConstructorVal> = Vec::new();
        let mut recursor_names = LeanNameSet::new();
        for &ind_name in &base.all {
            let ind = match env.find(&ind_name) {
                Some(ConstantInfo::Induct(v)) => v,
                _ => {
                    return Err(format!(
                        "expected inductive, got {}",
                        self.arenas.names.to_lean_string(ind_name)
                    ))
                }
            };
            ind_vals.push(ind);
            for &ctor in &ind.ctors {
                match env.find(&ctor) {
                    Some(ConstantInfo::Ctor(v)) => ctor_vals.push(v),
                    _ => {
                        return Err(format!(
                            "expected constructor, got {}",
                            self.arenas.names.to_lean_string(ctor)
                        ))
                    }
                }
            }
            self.visited_constants.insert(ind_name);
            self.dump_deps(ind.val.ty)?;
            match self.recursor_map.get(&base.val.name) {
                Some(names) => {
                    for n in names.to_vec(&self.arenas.names) {
                        recursor_names.insert(n);
                    }
                }
                None => {
                    if !ctor_vals.is_empty() {
                        return Err("inductive without recursor but with constructors".to_string());
                    }
                }
            }
        }

        // Constructor deps first (inductives in this block are already
        // marked visited, so their deps precede the block in the file).
        for ctor_val in &ctor_vals {
            self.visited_constants.insert(ctor_val.val.name);
            self.dump_deps(ctor_val.val.ty)?;
        }

        let mut recursor_vals: Vec<&'a crate::value::RecursorVal> = Vec::new();
        for rec_name in recursor_names.to_vec(&self.arenas.names) {
            match env.find(&rec_name) {
                Some(ConstantInfo::Rec(v)) => recursor_vals.push(v),
                _ => {
                    return Err(format!(
                        "expected recursor, got {}",
                        self.arenas.names.to_lean_string(rec_name)
                    ))
                }
            }
        }
        for rec_val in &recursor_vals {
            self.visited_constants.insert(rec_val.val.name);
            self.dump_deps(rec_val.val.ty)?;
        }
        for rec_val in &recursor_vals {
            for rule in &rec_val.rules {
                self.dump_deps(rule.rhs)?;
            }
        }

        let mut types_json = Vec::with_capacity(ind_vals.len());
        for v in &ind_vals {
            types_json.push(Json::obj(vec![
                ("name".to_string(), Json::num(self.dump_name(v.val.name)?)),
                ("levelParams".to_string(), self.dump_uparams(&v.val.level_params)?),
                ("type".to_string(), Json::num(self.dump_expr(v.val.ty)?)),
                ("numParams".to_string(), Json::num(v.num_params)),
                ("numIndices".to_string(), Json::num(v.num_indices)),
                ("all".to_string(), self.dump_names(&v.all)?),
                ("ctors".to_string(), self.dump_names(&v.ctors)?),
                ("numNested".to_string(), Json::num(v.num_nested)),
                ("isRec".to_string(), Json::Bool(v.is_rec)),
                ("isReflexive".to_string(), Json::Bool(v.is_reflexive)),
                ("isUnsafe".to_string(), Json::Bool(v.is_unsafe)),
            ]));
        }
        let mut ctors_json = Vec::with_capacity(ctor_vals.len());
        for v in &ctor_vals {
            ctors_json.push(Json::obj(vec![
                ("name".to_string(), Json::num(self.dump_name(v.val.name)?)),
                ("levelParams".to_string(), self.dump_uparams(&v.val.level_params)?),
                ("type".to_string(), Json::num(self.dump_expr(v.val.ty)?)),
                ("induct".to_string(), Json::num(self.dump_name(v.induct)?)),
                ("cidx".to_string(), Json::num(v.cidx)),
                ("numParams".to_string(), Json::num(v.num_params)),
                ("numFields".to_string(), Json::num(v.num_fields)),
                ("isUnsafe".to_string(), Json::Bool(v.is_unsafe)),
            ]));
        }
        let mut recs_json = Vec::with_capacity(recursor_vals.len());
        for v in &recursor_vals {
            // Dump order matters: the golden dumps the fields of each
            // recursor in the order `name`, `levelParams`, `type`, ...,
            // and only then the rules (see `Export.lean`), because the
            // `getIdx` index assigned to each node depends on it.
            let name = Json::num(self.dump_name(v.val.name)?);
            let level_params = self.dump_uparams(&v.val.level_params)?;
            let ty = Json::num(self.dump_expr(v.val.ty)?);
            let all = self.dump_names(&v.all)?;
            let mut rules_json = Vec::with_capacity(v.rules.len());
            for rule in &v.rules {
                rules_json.push(Json::obj(vec![
                    ("ctor".to_string(), Json::num(self.dump_name(rule.ctor)?)),
                    ("nfields".to_string(), Json::num(rule.nfields)),
                    ("rhs".to_string(), Json::num(self.dump_expr(rule.rhs)?)),
                ]));
            }
            recs_json.push(Json::obj(vec![
                ("name".to_string(), name),
                ("levelParams".to_string(), level_params),
                ("type".to_string(), ty),
                ("all".to_string(), all),
                ("numParams".to_string(), Json::num(v.num_params)),
                ("numIndices".to_string(), Json::num(v.num_indices)),
                ("numMotives".to_string(), Json::num(v.num_motives)),
                ("numMinors".to_string(), Json::num(v.num_minors)),
                ("rules".to_string(), Json::Arr(rules_json)),
                ("k".to_string(), Json::Bool(v.k)),
                ("isUnsafe".to_string(), Json::Bool(v.is_unsafe)),
            ]));
        }
        self.dump_obj(vec![(
            "inductive".to_string(),
            Json::obj(vec![
                ("types".to_string(), Json::Arr(types_json)),
                ("ctors".to_string(), Json::Arr(ctors_json)),
                ("recs".to_string(), Json::Arr(recs_json)),
            ]),
        )])?;
        Ok(())
    }

    fn dump_deps(&mut self, e: Expr) -> Result<(), String> {
        let used = get_used_constants(&*self.arenas, e);
        for c in used {
            self.dump_constant(c)?;
        }
        Ok(())
    }

    fn dump_uparams(&mut self, uparams: &[Name]) -> Result<Json, String> {
        let mut name_idxs = Vec::with_capacity(uparams.len());
        for &n in uparams {
            name_idxs.push(Json::num(self.dump_name(n)?));
        }
        for &n in uparams {
            let l = self.arenas.levels.intern(LevelNode::Param(n));
            let _ = self.dump_level(l)?;
        }
        Ok(Json::Arr(name_idxs))
    }

    fn dump_names(&mut self, ns: &[Name]) -> Result<Json, String> {
        let mut idxs = Vec::with_capacity(ns.len());
        for &n in ns {
            idxs.push(Json::num(self.dump_name(n)?));
        }
        Ok(Json::Arr(idxs))
    }

    fn dump_obj(&mut self, fields: Vec<(String, Json)>) -> Result<(), String> {
        let line = Json::obj(fields).compress();
        self.emit(&line);
        Ok(())
    }

    // ---- top level --------------------------------------------------------

    /// Dump the metadata line, then every non-internal constant in
    /// `env.constants` order (matching `Main.lean`'s default), or only the
    /// explicitly named constants when `only` is `Some` (matching
    /// `Main.lean` with a `-- name ...` list).
    pub fn export_all(
        &mut self,
        lean_version: &str,
        githash: &str,
        only: Option<&[Name]>,
        limit: Option<usize>,
    ) -> Result<(), String> {
        let meta = Json::obj(vec![(
            "meta".to_string(),
            Json::obj(vec![
                (
                    "exporter".to_string(),
                    Json::obj(vec![
                        ("name".to_string(), Json::Str("lean4export".to_string())),
                        ("version".to_string(), Json::Str("3.1.0".to_string())),
                    ]),
                ),
                (
                    "format".to_string(),
                    Json::obj(vec![("version".to_string(), Json::Str("3.1.0".to_string()))]),
                ),
                (
                    "lean".to_string(),
                    Json::obj(vec![
                        ("githash".to_string(), Json::Str(githash.to_string())),
                        ("version".to_string(), Json::Str(lean_version.to_string())),
                    ]),
                ),
            ]),
        )]);
        self.emit(&meta.compress());
        let mut n_done = 0usize;
        let mut next_report = 5000usize;
        match only {
            Some(list) => {
                for &n in list {
                    self.dump_constant(n)?;
                    n_done += 1;
                    if n_done >= next_report {
                        self.report_mem(n_done);
                        next_report += 5000;
                    }
                }
            }
            None => {
                let names: Vec<Name> = self.env.constants.iter().map(|(n, _)| *n).collect();
                for &n in &names {
                    if self.arenas.names.is_internal(n) {
                        continue;
                    }
                    self.dump_constant(n)?;
                    n_done += 1;
                    if let Some(l) = limit {
                        if n_done >= l {
                            break;
                        }
                    }
                    if n_done >= next_report {
                        self.report_mem(n_done);
                        next_report += 5000;
                    }
                    if std::env::var("LEAN4EXPORT_TRACE").is_ok() && n_done.is_multiple_of(500) {
                        let rss = self.report_rss();
                        eprintln!(
                            "[trace] constants={n_done} name={} rss={rss}MB names={} exprs={} hash_cache={} no_mdata={}",
                            self.arenas.names.to_lean_string(n),
                            self.name_count,
                            self.visited_exprs.len(),
                            self.hash_cache.len(),
                            self.no_mdata.len()
                        );
                    }
                }
            }
        }
        Ok(())
    }

    /// Periodic memory diagnostic: map sizes + RSS (stderr).
    fn report_mem(&self, n_done: usize) {
        let rss = std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with("VmRSS:"))
                    .and_then(|l| l.split_whitespace().nth(1))
                    .and_then(|v| v.parse::<u64>().ok())
            })
            .unwrap_or(0);
        let n_buckets = self.visited_exprs.len();
        let n_overflow = self.visited_overflow.values().map(|v| v.len()).sum::<usize>();
        let n_entries = n_buckets + n_overflow;
        let visited_bytes = n_buckets * 24 + n_overflow * 40 + n_entries * 16;
        let dense_bytes =
            (self.hash_cache.len() + self.size_cache.len() + self.deep_cache.len()) * 4
                + self.no_mdata.len() * 4
                + self.visited_names.len() * 8
                + self.visited_levels.len() * 8;
        eprintln!(
            "[mem] constants={n_done} exprs={n_entries} buckets={n_buckets} visited_MB={} dense_MB={} scratch={} rss={}MB",
            visited_bytes / (1024 * 1024),
            dense_bytes / (1024 * 1024),
            self.arenas.exprs.len() - self.arenas.exprs.env_len(),
            rss / 1024
        );
    }

    /// Current RSS in MB.
    fn report_rss(&self) -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with("VmRSS:"))
                    .and_then(|l| l.split_whitespace().nth(1))
                    .and_then(|v| v.parse::<u64>().ok())
            })
            .unwrap_or(0)
            / 1024
    }
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn ci_is_unsafe(ci: &ConstantInfo) -> bool {
    match ci {
        ConstantInfo::Axiom(v) => v.is_unsafe,
        ConstantInfo::Defn(v) => v.safety == DefinitionSafety::Unsafe,
        ConstantInfo::Thm(_) => false,
        ConstantInfo::Opaque(v) => v.is_unsafe,
        ConstantInfo::Quot(_) => false,
        ConstantInfo::Induct(v) => v.is_unsafe,
        ConstantInfo::Ctor(v) => v.is_unsafe,
        ConstantInfo::Rec(v) => v.is_unsafe,
    }
}

fn binder_info_json(bi: BinderInfo) -> Json {
    Json::Str(
        match bi {
            BinderInfo::Default => "default",
            BinderInfo::Implicit => "implicit",
            BinderInfo::StrictImplicit => "strictImplicit",
            BinderInfo::InstImplicit => "instImplicit",
        }
        .to_string(),
    )
}

fn hints_json(h: ReducibilityHints) -> Json {
    match h {
        ReducibilityHints::Opaque => Json::Str("opaque".to_string()),
        ReducibilityHints::Abbrev => Json::Str("abbrev".to_string()),
        ReducibilityHints::Regular(n) => Json::obj(vec![("regular".to_string(), Json::Num(n.to_string()))]),
    }
}

fn safety_json(s: DefinitionSafety) -> Json {
    Json::Str(
        match s {
            DefinitionSafety::Unsafe => "unsafe",
            DefinitionSafety::Safe => "safe",
            DefinitionSafety::Partial => "partial",
        }
        .to_string(),
    )
}

fn quot_kind_json(k: QuotKind) -> Json {
    Json::Str(
        match k {
            QuotKind::Type => "type",
            QuotKind::Ctor => "ctor",
            QuotKind::Lift => "lift",
            QuotKind::Ind => "ind",
        }
        .to_string(),
    )
}

/// `getUsedConstants` (foldConsts): pre-order DFS collecting `Const` names,
/// deduplicated by node index. The reference (`Export.lean`) collects into
/// a `NameSet`; the pre-order *first-seen* order is unchanged, and
/// `dump_deps` re-visits are no-ops (the constant is already marked
/// visited), so the output is byte-identical.
pub fn get_used_constants(arenas: &Arenas, e: Expr) -> Vec<Name> {
    let mut out = Vec::new();
    let mut seen = std::collections::HashSet::new();
    fn go(arenas: &Arenas, e: Expr, out: &mut Vec<Name>, seen: &mut std::collections::HashSet<NodeIdx>) {
        if !seen.insert(e.0) {
            return;
        }
        match arenas.exprs.node(e) {
            ExprNode::Const(n, _) => out.push(n),
            ExprNode::App(f, a) => {
                go(arenas, Expr(f), out, seen);
                go(arenas, Expr(a), out, seen);
            }
            ExprNode::Lam(_, t, b, _) => {
                go(arenas, Expr(t), out, seen);
                go(arenas, Expr(b), out, seen);
            }
            ExprNode::ForallE(_, t, b, _) => {
                go(arenas, Expr(t), out, seen);
                go(arenas, Expr(b), out, seen);
            }
            ExprNode::LetE(_, t, v, b, _) => {
                go(arenas, Expr(t), out, seen);
                go(arenas, Expr(v), out, seen);
                go(arenas, Expr(b), out, seen);
            }
            ExprNode::MData(_, inner) => go(arenas, Expr(inner), out, seen),
            ExprNode::Proj(_, _, st) => go(arenas, Expr(st), out, seen),
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::MVar(_) | ExprNode::Sort(_)
            | ExprNode::Lit(_) => {}
        }
    }
    go(arenas, e, &mut out, &mut seen);
    out
}

/// The dotted string form of a module name (`Init.Prelude`), for loading.
pub fn module_display(names: &crate::value::NameTable, n: Name) -> String {
    names.to_string_plain(n)
}

// ---------------------------------------------------------------------------
// Env loading (module + transitive imports)
// ---------------------------------------------------------------------------

/// Resolve a module name like `Init.Prelude` to `<root>/Init/Prelude.olean`.
pub fn module_path(name: &str, root: &std::path::Path) -> std::path::PathBuf {
    let mut p = root.to_path_buf();
    let mut parts = name.split('.').peekable();
    while let Some(part) = parts.next() {
        if parts.peek().is_some() {
            p.push(part);
        } else {
            p.push(format!("{part}.olean"));
        }
    }
    p
}

/// Decode a single `.olean` file into its `ModuleData` (into `arenas`).
pub fn decode_module(bytes: &[u8], arenas: &mut Arenas) -> Result<crate::value::ModuleData, String> {
    let olean = crate::OLean::parse(bytes).map_err(|e| format!("bad header: {e}"))?;
    olean
        .decode_part(0, arenas)
        .map_err(|e| format!("decode failed: {e}"))
}

/// The `.ir` file of a module (`findOLean m |> withExtension "ir"`, i.e.
/// `Init/Prelude.olean` -> `Init/Prelude.ir`), in the first root where the
/// module's `.olean` exists, if the `.ir` file itself exists.
fn ir_module_path(name: &str, roots: &[std::path::PathBuf]) -> Option<std::path::PathBuf> {
    for root in roots {
        let p = module_path(name, root);
        if p.is_file() {
            let ir = p.with_extension("ir");
            if ir.is_file() {
                return Some(ir);
            }
            return None;
        }
    }
    None
}

/// The `extraConstNames.size` Lean's `finalizeImport` adds to
/// `numPrivateConsts` for one module (`irData.foldl` over
/// `ImportedModule.interpData? .private`). For module-system modules the
/// IR data (`.ir`, which lists *all* declaration names,
/// `includeDecls := true`) is used; for old-style modules the main data's
/// `extraConstNames` is used; a module-system module without an `.ir` file
/// contributes nothing.
fn ir_extra_const_names_count(
    name: &str,
    roots: &[std::path::PathBuf],
    is_module: bool,
    main_extra: usize,
    arenas: &mut Arenas,
) -> Option<usize> {
    if !is_module {
        return Some(main_extra);
    }
    let path = ir_module_path(name, roots)?;
    let bytes = std::fs::read(&path).ok()?;
    let olean = crate::OLean::parse(&bytes).ok()?;
    let md = olean.decode_part_lite(0, arenas).ok()?;
    Some(md.extra_const_names.len())
}

/// The part files of a module, in the order Lean's `findOLeanParts`
/// produces them: `.olean` (exported), `.olean.server`, `.olean.private`.
/// Only existing parts are returned; the server part exists whenever the
/// private part does (both are written by `writeModule`).
fn module_part_paths(name: &str, roots: &[std::path::PathBuf]) -> Option<Vec<std::path::PathBuf>> {
    for root in roots {
        let base = module_path(name, root);
        let base = base.with_extension(""); // strip `.olean`
        let mut parts = Vec::new();
        let exported = base.with_extension("olean");
        let server = base.with_extension("olean.server");
        let private = base.with_extension("olean.private");
        if exported.is_file() {
            parts.push(exported);
            if server.is_file() {
                parts.push(server);
                if private.is_file() {
                    parts.push(private);
                }
            }
        }
        if !parts.is_empty() {
            return Some(parts);
        }
    }
    None
}

/// Decode the `ModuleData` Lean's `importModules` would use for `module`
/// with the default `globalLevel := .private` (so `importAll` is true for
/// every module): if the module's *exported* data says it is a
/// module-system module, the private part is used; otherwise the exported
/// part. Returns the selected `ModuleData` together with the exported
/// part's `isModule` flag. All decoded values are interned into `arenas`.
pub fn decode_module_selected(
    name: &str,
    roots: &[std::path::PathBuf],
    arenas: &mut Arenas,
) -> Result<(crate::value::ModuleData, bool), String> {
    let paths = module_part_paths(name, roots)
        .ok_or_else(|| format!("module {name} not found in search path"))?;
    let mut bytes = Vec::with_capacity(paths.len());
    for p in &paths {
        bytes.push(std::fs::read(p).map_err(|e| format!("cannot read {}: {e}", p.display()))?);
    }
    let olean = crate::OLean::parse_parts(bytes).map_err(|e| format!("bad header: {e}"))?;
    // Only the fields needed for env construction are decoded (skipping
    // the persistent-extension `entries`, which can be very large).
    let exported = olean
        .decode_part_lite(0, arenas)
        .map_err(|e| format!("decode failed ({name} exported): {e}"))?;
    let is_module = exported.is_module;
    eprintln!("  [dbg] {name}: is_module={is_module}");
    // Segment indices: 0 = exported, 1 = server, 2 = private.
    let idx = if is_module { 2 } else { 0 };
    if name == "Init.BinderNameHint" {
        let md0 = olean
            .decode_part_lite(0, arenas)
            .map_err(|e| format!("decode failed ({name} exported): {e}"))?;
        eprintln!(
            "  [dbg] exported constants: {}",
            md0.constants
                .iter()
                .map(|c| arenas.names.to_lean_string(c.name()))
                .collect::<Vec<_>>()
                .join(", ")
        );
        if let Ok(md2) = olean.decode_part_lite(2, arenas) {
            eprintln!(
                "  [dbg] private constants: {}",
                md2.constants
                    .iter()
                    .map(|c| arenas.names.to_lean_string(c.name()))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }
    let md = if idx == 0 {
        exported
    } else {
        olean
            .decode_part_lite(idx, arenas)
            .map_err(|e| format!("decode failed ({name} part {idx}): {e}"))?
    };
    Ok((md, is_module))
}

/// Load the environment of `module` (its constants plus those of every
/// transitive import), searching `roots` in order. Returns the env and the
/// arena set its handles refer into.
pub fn load_env(
    module: &str,
    roots: &[std::path::PathBuf],
) -> Result<(Env, Arenas), String> {
    let mut loaded: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut arenas = Arenas::new();
    let mut env = Env::new();
    load_module_rec(module, roots, &mut loaded, &mut env, &mut arenas)?;
    env.finalize(&arenas.names);
    // The decode-time content interning maps are the largest single
    // allocation during load; the exporter never interns expressions, so
    // drop them before exporting.
    arenas.exprs.drop_intern_maps();
    Ok((env, arenas))
}

/// `Lean.Environment.isPropCheap`: a cheap approximation of `Meta.isProp`.
/// `ty = ∀ ..., p xs...` where `p : ∀ ..., Prop`.
fn is_prop_cheap(env: &Env, arenas: &Arenas, ty: Expr) -> bool {
    let mut ty = ty;
    while let ExprNode::ForallE(_, _, b, _) = arenas.exprs.node(ty) {
        ty = Expr(b);
    }
    let mut f = ty;
    let mut nargs = 0usize;
    while let ExprNode::App(fn_, _) = arenas.exprs.node(f) {
        f = Expr(fn_);
        nargs += 1;
    }
    let ExprNode::Const(n, _) = arenas.exprs.node(f) else {
        return false;
    };
    let Some(decl) = env.find(&n) else {
        return false;
    };
    let mut p = decl.ty_expr();
    for _ in 0..nargs {
        let ExprNode::ForallE(_, _, b, _) = arenas.exprs.node(p) else {
            return false;
        };
        p = Expr(b);
    }
    matches!(arenas.exprs.node(p), ExprNode::Sort(l) if matches!(arenas.levels.node(l), LevelNode::Zero))
}

/// `Lean.Environment.subsumesInfo` (`Environment.lean`): whether `a` is a
/// richer representation of `b` (same name/type/levelParams, and compatible
/// kind), so that `a` may replace `b` when both are imported from different
/// modules. The equation compiler may regenerate the same on-demand theorem
/// (e.g. `List.foldl.eq_def`) in several modules; the last imported version
/// wins.
///
/// Expression handles are interned, so handle equality is structural
/// equality.
fn subsumes_info(env: &Env, arenas: &Arenas, a: &ConstantInfo, b: &ConstantInfo) -> bool {
    // `Expr.BEq` (== on types) is `lean_expr_equal`, which ignores binder
    // names: two modules defining the same instance with different
    // `_hygCtx` binder names are alpha-equal and subsume each other.
    if a.name() != b.name()
        || !expr_alpha_eq(arenas, a.ty_expr(), b.ty_expr())
        || a.level_params() != b.level_params()
    {
        return false;
    }
    match (a, b) {
        (ConstantInfo::Thm(ta), ConstantInfo::Thm(tb)) => ta.all == tb.all,
        (ConstantInfo::Thm(ta), ConstantInfo::Axiom(ab)) => {
            ta.all.len() == 1 && ta.all[0] == ab.val.name && !ab.is_unsafe
        }
        (ConstantInfo::Axiom(aa), ConstantInfo::Axiom(ab)) => {
            aa.is_unsafe == ab.is_unsafe && is_prop_cheap(env, arenas, aa.val.ty)
        }
        _ => false,
    }
}

fn load_module_rec(
    name: &str,
    roots: &[std::path::PathBuf],
    loaded: &mut std::collections::HashSet<String>,
    env: &mut Env,
    arenas: &mut Arenas,
) -> Result<(), String> {
    if !loaded.insert(name.to_string()) {
        return Ok(());
    }
    eprintln!("loading module {name}");
    let t0 = std::time::Instant::now();
    let (md, is_module) = decode_module_selected(name, roots, arenas)?;
    eprintln!("  decoded {name} (isModule={is_module}, {} constants, {} imports) in {:?}", md.constants.len(), md.imports.len(), t0.elapsed());
    // Take what we need, then drop the rest before recursing so only one
    // module's decoded data is alive at a time (the whole closure would
    // otherwise exhaust memory).
    let crate::value::ModuleData {
        imports,
        constants,
        extra_const_names,
        ..
    } = md;
    let imports: Vec<Name> = imports.iter().map(|i| i.module).collect();
    // `importModules` visits modules in post-order DFS: the imports of a
    // module are processed (and their constants added to `env.constants`)
    // before the module's own constants, matching `ImportState.moduleNames`.
    // The raw constant count of every module feeds `numPrivateConsts`, which
    // sizes the `Std.HashMap` backing `env.constants`. Lean's
    // `finalizeImport` adds `extraConstNames.size` (from the module's IR
    // data) on top of `constants.size`, and this total determines the
    // bucket count (and hence iteration order) of `env.constants`.
    let extra = ir_extra_const_names_count(name, roots, is_module, extra_const_names.len(), arenas)
        .unwrap_or(0);
    env.add_module_constants(constants.len() + extra);
    for imp in imports {
        let imp_name = module_display(&arenas.names, imp);
        load_module_rec(&imp_name, roots, loaded, env, arenas)?;
    }
    let t1 = std::time::Instant::now();
    let mut n_added = 0usize;
    for ci in constants {
        let n = ci.name();
        match env.by_name.get(&n) {
            None => {
                env.insert_constant(ci);
                n_added += 1;
            }
            Some(_) => {
                // Duplicate name from another module. Lean's
                // `finalizeImport` merges these via `subsumesInfo`: the new
                // constant replaces the old one iff it subsumes it, the old
                // is kept iff it subsumes the new, and otherwise importing
                // fails ("already imported").
                let old = env.find(&n).expect("by_name lookup");
                if subsumes_info(env, arenas, &ci, old) {
                    env.insert_constant(ci);
                    n_added += 1;
                } else if !subsumes_info(env, arenas, old, &ci) {
                    return Err(format!(
                        "constant {} already imported (incompatible versions)",
                        arenas.names.to_lean_string(n)
                    ));
                }
                // else: old subsumes new, keep the existing entry
            }
        }
    }
    eprintln!("  inserted {n_added} constants in {:?}", t1.elapsed());
    Ok(())
}
