#!/usr/bin/env bash
# check_symbols.sh - Find all unresolved symbols in the lean binary

set -euo pipefail

PROJECT="$HOME/projects/lean4"
LEAN_BIN="$PROJECT/build/release/stage1/bin/lean"
LLS="$PROJECT/build/release/stage1/lib/lean/libleanshared.so"

normalize() {
  sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//'
}

if [ ! -f "$LEAN_BIN" ]; then
  echo "Error: Lean binary not found at $LEAN_BIN"
  exit 1
fi

echo "--- Analyzing: $LEAN_BIN ---"

echo
echo "=== 1. Undefined Symbols (via nm) ==="

nm -u "$LEAN_BIN" |
  grep ' U ' |
  sed \
    -e "s|$PROJECT/||g" \
    -e 's|bin/\.\./||g' |
  normalize

echo
echo "=== 2. Resolution Failures (via ldd -r) (LLS means build/release/stage1/lib/lean/libleanshared.so) ==="

ldd -r "$LEAN_BIN" 2>&1 |
  grep 'undefined symbol' |
  sed \
    -e 's|bin/\.\./||g' \
    -e "s|$LLS|LLS|g" \
    -e "s|$PROJECT/||g" \
    -e 's/^undefined symbol: //' |
  sort -u |
  normalize
