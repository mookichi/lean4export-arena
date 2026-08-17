#!/usr/bin/env bash
# Resolve the --lean-path roots for a Mathlib checkout.
# Usage: mathlib_roots.sh <mathlib-dir> [extra dirs...]
# Prints one --lean-path flag per found build directory, followed by the
# main Mathlib build dir last (so it is searched first is NOT guaranteed —
# roots are searched in order, main dir should come first for Mathlib.olean).
set -euo pipefail

ML="${1:?usage: mathlib_roots.sh <mathlib-dir>}"
shift

# Main Mathlib build output first (highest priority).
MAIN="$ML/.lake/build/lib/lean"
if [ -d "$MAIN" ]; then
  echo "--lean-path $MAIN"
fi

# Every dependency package's build output.
for p in "$ML"/.lake/packages/*/; do
  d="$p.lake/build/lib/lean"
  if [ -d "$d" ]; then
    echo "--lean-path $d"
  fi
done

# Extra dirs (optional) after the discovered ones.
for d in "$@"; do
  if [ -d "$d" ]; then
    echo "--lean-path $d"
  fi
done
