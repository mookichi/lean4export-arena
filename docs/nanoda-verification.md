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

Stream the exporter directly into nanoda, without ever writing the
NDJSON to disk:

```bash
lean4export-rs --export Init --lean-path <sysroot>/lib/lean \
  | nanoda_bin nanoda-config.json
```

or point `export_file_path` at a saved export file with `use_stdin: false`.

The exporter writes the NDJSON stream to stdout (progress goes to
stderr), and nanoda reads it from stdin when `use_stdin: true`, so the
pipe is a true streaming pipeline — the export is consumed incrementally
as it is produced, and no intermediate file is created. Verified with a
full Init export piped directly into the unmodified nanoda binary
using the whitelist config above:
`Checked 57422 declarations with no errors, skipping exported but
unpermitted axioms ["Lean.ofReduceNat", "sorryAx", "Lean.ofReduceBool"]`
(exit 0) — identical to the file-based run.

Axioms are checked against the `permitted_axioms` whitelist (the
semi-official `Quot.sound`, `Classical.choice`, `propext`, plus
`Lean.trustCompiler`); do **not** use `unsafe_permit_all_axioms` for
verification — it admits every axiom to the environment unchecked. The
three skipped axioms above are declared for metaprograms only and never
used by other declarations, so skipping them is safe (nanoda's README
recommends this for the prelude's `sorryAx`).

Note: the pipeline's exit status is nanoda's (the last command); the
exporter reports `Broken pipe` on stderr only when nanoda exits early
(e.g. on a hard error), which is expected. If you want the exporter's
status too, run with `set -o pipefail`.

The pipe also saves disk: a full Mathlib export (5.9 GB as a file)
streams straight through without touching disk.

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
