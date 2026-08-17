# Kernel verification with nanoda

Every exported module is type-checked by
[nanoda](https://github.com/ammkrn/nanoda_lib) (v0.4.13), an independent
external kernel checker for Lean 4, using an **unmodified** nanoda binary.
This is the primary correctness check for the Rust exporter's output;
the golden files in `golden/phase0/` are regression references
(regenerated from this implementation, see below).

## Why this works

The export never contains duplicate content lines, which nanoda's parser
rejects:

- `bvar` nodes are cached like any other expression (upstream lean4export
  behavior): repeated `bvar N` occurrences become back-references, so the
  stream is free of duplicate `{"bvar":N,...}` definitions.
- The deep-expression path (`isDeepExpr`, >1000 nested binders) assigns
  each expression's index *after* dumping its children, so the `ie`
  indices are continuous in emission order (external checkers reject
  out-of-order indices as back-reference mismatches).

## Config

```json
{
    "use_stdin": true,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true,
    "print_axioms": false
}
```

`unpermitted_axiom_hard_error: false` skips declared-but-unused axioms
(`sorryAx`, `Lean.ofReduceNat`, `Lean.ofReduceBool`, and Phase0Test's own
test axioms); the README of nanoda recommends this for the prelude's
`sorryAx`.

## Running

Stream the exporter directly into nanoda:

```bash
lean4export-rs --export Init --lean-path <sysroot>/lib/lean \
  | nanoda_bin nanoda-config.json
```

or point `export_file_path` at a saved export file with `use_stdin: false`.

## Results (August 2026, Lean v4.30.0)

| Module | Declarations | Result | Time |
|---|---|---|---|
| Init | 57,422 | no errors | ~41 s |
| Lean | 163,505 | no errors | ~1 m 48 s |
| Test | 163,728 | no errors | ~1 m 48 s |
| Phase0Test | 163,607 | no errors | ~1 m 22 s |
| Mathlib (full, 104M lines) | 697,646 | no errors | ~26 min |

All runs exit 0 and print `Checked N declarations with no errors`.

## Golden files

`golden/phase0/*.ndjson` and `golden/phase0/const/*.ndjson` are
regenerated from the Rust exporter (this implementation), and serve as
regression references. The byte-identical-with-the-Lean-implementation
property no longer holds: the local Lean exporter retains its
bvar-never-cached behavior (see `bvar_dedup_fix.md`), which external
checkers reject. Semantic correctness is instead enforced by nanoda and
any other external kernel checker.
