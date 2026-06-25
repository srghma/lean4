#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 output-path" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
template="$repo_root/src/include/lean/lean_header.template"
types_tmp="$(mktemp)"
types_block_tmp="$(mktemp)"
generated_tmp="$(mktemp)"
output="$1"

cleanup() {
  rm -f "$types_tmp" "$types_block_tmp" "$generated_tmp"
}
trap cleanup EXIT

cbindgen "$repo_root/src/rust/lean_ffi_types" \
  --config "$repo_root/src/rust/lean_ffi_types/cbindgen.toml" \
  --output "$generated_tmp"

awk '
  /^typedef struct lean_object \{/ { capture = 1 }
  capture { print }
  /^#endif  \/\* LEAN_H \*\/$/ { exit }
' "$generated_tmp" > "$types_tmp"

sed 's/\[0\]/[]/g' "$types_tmp" > "$types_block_tmp"

mkdir -p "$(dirname "$output")"

awk -v types_file="$types_block_tmp" '
  BEGIN {
    while ((getline line < types_file) > 0) {
      types = types line "\n";
    }
    close(types_file);
  }
  /\/\* BEGIN GENERATED LEAN C ABI TYPES \*\// {
    print;
    printf "%s", types;
    skip = 1;
    next;
  }
  /\/\* END GENERATED LEAN C ABI TYPES \*\// {
    skip = 0;
    print;
    next;
  }
  skip { next }
  { print }
' "$template" > "$output"
