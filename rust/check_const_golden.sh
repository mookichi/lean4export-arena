#!/usr/bin/env bash
# Regression check: for each golden per-constant NDJSON, run the Rust exporter
# with the matching --only flag (plus --export-unsafe / --export-mdata where
# the golden file name indicates it) and diff byte-for-byte. Runs in parallel
# (each run reloads the full environment, ~4-7GB of RAM per process, so keep
# -P modest — the machine must fit P * peak_RSS in RAM).
#
# Every worker is wrapped in `timeout` and the script kills its whole process
# group on exit, so a timed-out run can never leave orphaned exporter
# processes behind (several orphaned ~7GB processes are what caused the OOM
# that crashed the machine).
set -u
cd "$(dirname "$0")/.."
ROOT=$(pwd)
BIN="$ROOT/rust/target/release/lean4export-rs"
GOLDEN="$ROOT/golden/phase0/const"
LEAN_PATH="$ROOT/.lake/build/lib/lean"
MOD=Phase0Test
WORK="$ROOT/rust/target/const_check"
PER_RUN_TIMEOUT=180          # seconds per constant
JOBS=${PARALLELISM:-4}       # override with PARALLELISM=n if more RAM
mkdir -p "$WORK"
rm -f "$WORK"/*.out "$WORK"/*.err "$WORK"/*.result "$WORK"/summary

# Kill any worker still running when this script is interrupted (the whole
# process group of each worker, so grandchildren die too).
cleanup() {
  pkill -P $$ 2>/dev/null
  pkill -f "lean4export-rs --export $MOD" 2>/dev/null
  exit "${1:-1}"
}
trap 'cleanup 130' INT TERM

run_one() {
  local base=$1
  local name=${base%.ndjson}
  local const=$name
  local extra=""
  case "$name" in
    *.unsafe) const=${name%.unsafe}; extra="--export-unsafe";;
    *.mdata)  const=${name%.mdata};  extra="--export-mdata";;
  esac
  if ! timeout "$PER_RUN_TIMEOUT" "$BIN" --export "$MOD" --lean-path "$LEAN_PATH" $extra --only "$MOD.$const" \
      >"$WORK/$base.out" 2>"$WORK/$base.err"; then
    echo "FAIL $base: exporter errored/timed out" >"$WORK/$base.result"
    return
  fi
  if diff -q "$GOLDEN/$base" "$WORK/$base.out" >/dev/null 2>&1; then
    echo "ok   $base" >"$WORK/$base.result"
  else
    { echo "FAIL $base: diff"; diff "$GOLDEN/$base" "$WORK/$base.out" | head -10; } >"$WORK/$base.result"
  fi
}
export -f run_one
export BIN GOLDEN LEAN_PATH MOD WORK PER_RUN_TIMEOUT

ls "$GOLDEN"/*.ndjson | xargs -n1 basename | xargs -P "$JOBS" -n1 bash -c 'run_one "$0"' >/dev/null

pass=0
fail=0
: > "$WORK/summary"
for r in "$WORK"/*.result; do
  cat "$r" >> "$WORK/summary"
  if grep -q '^ok ' "$r"; then pass=$((pass+1)); else fail=$((fail+1)); fi
done
sort "$WORK/summary"
echo "----------------------------------------"
echo "pass=$pass fail=$fail (parallelism=$JOBS, per-run timeout=${PER_RUN_TIMEOUT}s)"
[ "$fail" -eq 0 ]
