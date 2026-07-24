# Fix: bvar deduplication in lean4export

## Problem

`lean4export` caches all `Expr` nodes via `getIdx`/`visitedExprs`, including
`.bvar` nodes.  Two `.bvar i` expressions with the same de Bruijn index `i`
are structurally equal → `getIdx` returns the same exported index for both,
even if they occur at *different binder depths* (different `forallE`/`lam`
nesting levels).

Downstream consumers (e.g. DAG‑based proof search engines) that read `bvar`
values from the exported JSON and evaluate them in a *leaf* scope (after
additional binder introductions) will resolve both references to the same
binder, producing incorrect results.

## Fix (two locations)

### 1. Lean 4 exporter (`Export.lean`)

In `dumpExprAux`, handle `.bvar` **before** calling `getIdx`.  Emit a fresh
JSON entry with a sequential `ie` index (from `visitedExprs.size`) and
reserve the slot with a unique dummy key `.bvar(idx)` to keep index
assignment consistent.

**Before (lines 160–171):**

```lean
partial def dumpExprAux (e : Expr) : M Nat := do
  getIdx e "ie" (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    ...
    | .bvar i => return .mkObj [("bvar", i)]
```

**After:**

```lean
partial def dumpExprAux (e : Expr) : M Nat := do
  -- bvar indices are meaningful only relative to their binder context.
  -- Caching them via visitedExprs would share the same {"bvar": N} JSON
  -- across different binder depths, producing wrong de Bruijn values.
  -- We still allocate a sequential slot (keyed by a unique dummy) to
  -- keep index assignment consistent, but each bvar occurrence gets its
  -- own entry — no deduplication.
  if let .bvar i := e then
    let st ← get
    let idx := st.visitedExprs.size
    let json : Json := .mkObj [("bvar", i)]
    IO.println <| json.setObjVal! "ie" idx |>.compress
    -- Use a dummy key .bvar(idx) that can never collide with a real bvar
    -- (real bvar indices are tiny, idx is the expression count).
    modify fun st => { st with visitedExprs := st.visitedExprs.insert (.bvar idx) idx }
    return idx
  getIdx e "ie" (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    ...
    | .bvar i => return .mkObj [("bvar", i)]
```

The `.bvar` case inside `getIdx` becomes dead code after this change but
is left in place for safety.

### 2. Downstream parser (`nanoda/src/parser.rs` in proof-db)

The parser's `push_expr` also deduplicates expressions by hash via
`exprs_lookup`.  For `Expr::Var` this reverses the exporter fix — identical
`Var` nodes get collapsed back to a single DAG entry.

**Before:**

```rust
fn push_expr(&mut self, expr: Expr<'a>) -> usize {
    let hash = expr_hash(&expr);
    if let Some(&idx) = self.exprs_lookup.get(&hash) {
        return idx;
    }
    let idx = self.exprs.len();
    self.exprs_lookup.insert(hash, idx);
    self.exprs.push(expr);
    idx
}
```

**After:**

```rust
fn push_expr(&mut self, expr: Expr<'a>) -> usize {
    let hash = expr_hash(&expr);
    // bvar expressions (Var) are meaningful only relative to their binder
    // context.  Deduplicating by hash would collapse occurrences at
    // different binder depths into a single DAG node, causing down‑
    // stream scope‑sensitive analyses to resolve them to the wrong
    // binder.  Always insert a fresh node.
    if let Expr::Var { .. } = &expr {
        let idx = self.exprs.len();
        self.exprs.push(expr);
        return idx;
    }
    if let Some(&idx) = self.exprs_lookup.get(&hash) {
        return idx;
    }
    let idx = self.exprs.len();
    self.exprs_lookup.insert(hash, idx);
    self.exprs.push(expr);
    idx
}
```

## To apply to a new version of lean4export

1. Locate `dumpExprAux` in `Export.lean` (search for `partial def dumpExprAux`).
2. Insert the `if let .bvar i := e` block **before** the `getIdx` call.
3. Rebuild with `lake build`.
4. Re-export the target library:
   ```
   lake env lean4export LibraryName > out.ndjson
   ```

