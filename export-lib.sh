#!/usr/bin/env bash
set -euo pipefail

WITH_MATHLIB=false
SKIP_BUILD=false

args=()
while [ $# -gt 0 ]; do
  case "$1" in
    --with-mathlib) WITH_MATHLIB=true; shift ;;
    --no-build) SKIP_BUILD=true; shift ;;
    -*) echo "Unknown option: $1" >&2; exit 1 ;;
    *) args+=("$1"); shift ;;
  esac
done
set -- "${args[@]}"

if [ $# -lt 1 ]; then
  echo "Usage: $0 [--with-mathlib] [--no-build] <library-directory>" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN4EXPORT_BIN="$SCRIPT_DIR/.lake/build/bin/lean4export"
LIB_DIR="$(cd "$1" && pwd)"

# Build lean4export itself if needed
if [ ! -f "$LEAN4EXPORT_BIN" ]; then
  echo "Building lean4export..." >&2
  (cd "$SCRIPT_DIR" && lake build)
fi

TOOLCHAIN_FILE="$LIB_DIR/lean-toolchain"
if [ ! -f "$TOOLCHAIN_FILE" ]; then
  echo "Error: lean-toolchain not found in $LIB_DIR" >&2
  exit 1
fi
TOOLCHAIN=$(cat "$TOOLCHAIN_FILE")

# Install the required toolchain
elan toolchain install "$TOOLCHAIN" >/dev/null 2>&1 || true

# Determine library module name to export
LIB_NAME=""
if [ -f "$LIB_DIR/lakefile.toml" ]; then
  LIB_NAME=$(sed -n '/^\[\[lean_lib\]\]/,/^\[/{/^name\s*=\s*"\(.*\)"/s//\1/p}' "$LIB_DIR/lakefile.toml" | head -1)
fi
if [ -z "$LIB_NAME" ] && [ -f "$LIB_DIR/lakefile.lean" ]; then
  LIB_NAME=$(grep -E '^\s*lean_lib\s+' "$LIB_DIR/lakefile.lean" | head -1 | sed 's/.*lean_lib\s\+\([a-zA-Z0-9_]\+\).*/\1/')
fi
if [ -z "$LIB_NAME" ]; then
  if [ -f "$LIB_DIR/lakefile.toml" ]; then
    LIB_NAME=$(grep '^name\s*=' "$LIB_DIR/lakefile.toml" | head -1 | sed 's/.*=\s*"\(.*\)"/\1/')
  elif [ -f "$LIB_DIR/lakefile.lean" ]; then
    LIB_NAME=$(grep -E '^\s*package\s+' "$LIB_DIR/lakefile.lean" | head -1 | sed 's/.*package\s\+\([a-zA-Z0-9_]\+\).*/\1/')
  fi
fi
if [ -z "$LIB_NAME" ]; then
  echo "Error: Could not determine library name from lakefile" >&2
  exit 1
fi

# Try to download mathlib's pre-built olean cache (if mathlib4 is a dependency)
if ! $SKIP_BUILD; then
  echo "Downloading mathlib cache (if available)..." >&2
  elan run "$TOOLCHAIN" -- bash -c "
    cd '$LIB_DIR'
    lake build @mathlib/cache 2>/dev/null && lake exe @mathlib/cache get || true
  " >&2 2>/dev/null || true
fi

# Build the target library (including dependencies like mathlib)
if ! $SKIP_BUILD; then
  echo "Building $LIB_NAME..." >&2
  elan run "$TOOLCHAIN" -- bash -c "cd '$LIB_DIR' && lake build" >&2
fi

VERSION=$(echo "$TOOLCHAIN" | sed 's/.*://')
OUTPUT_FILE="$LIB_DIR/$LIB_NAME-$VERSION.ndjson"

# Export the library
echo "Exporting $LIB_NAME to $OUTPUT_FILE ..." >&2
elan run "$TOOLCHAIN" -- bash -c "cd '$LIB_DIR' && lake env '$LEAN4EXPORT_BIN' '$LIB_NAME'" > "$OUTPUT_FILE"
echo "Done: $OUTPUT_FILE" >&2

# Optionally export mathlib
if $WITH_MATHLIB; then
  if [ -f "$LIB_DIR/.lake/build/lib/Mathlib.olean" ]; then
    MATHLIB_OUTPUT="$LIB_DIR/Mathlib-$VERSION.ndjson"
    echo "Exporting Mathlib to $MATHLIB_OUTPUT ..." >&2
    elan run "$TOOLCHAIN" -- bash -c "cd '$LIB_DIR' && lake env '$LEAN4EXPORT_BIN' Mathlib" > "$MATHLIB_OUTPUT"
    echo "Done: $MATHLIB_OUTPUT" >&2
  else
    echo "Warning: Mathlib.olean not found; skipping mathlib export" >&2
  fi
fi
