#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 output-path" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
template="$repo_root/origin-master-src/include/lean/lean.h"
types_tmp="$(mktemp)"
types_renamed_tmp="$(mktemp)"
types_block_tmp="$(mktemp)"
generated_tmp="$(mktemp)"
output="$1"

cleanup() {
  rm -f "$types_tmp" "$types_renamed_tmp" "$types_block_tmp" "$generated_tmp"
}
trap cleanup EXIT

cbindgen "$repo_root/src/rust/lean_ffi_types" \
  --config "$repo_root/src/rust/lean_ffi_types/cbindgen.toml" \
  --output "$generated_tmp"

awk '
  /^typedef struct LeanObject \{/ { capture = 1 }
  capture && !/^#endif  \/\* LEAN_H \*\/$/ { print }
  /^#endif  \/\* LEAN_H \*\/$/ { exit }
' "$generated_tmp" > "$types_tmp"

sed -e 's/\[0\]/[]/g' \
    -e 's/typedef struct LeanObject {/typedef struct lean_object {/' \
    -e 's/} LeanObject;/} lean_object;/' \
    -e 's/struct LeanObject/lean_object/g' \
    "$types_tmp" > "$types_renamed_tmp"

awk '
  /^typedef struct lean_thunk_object \{/ { in_thunk = 1 }
  /^typedef struct lean_task_object \{/ { in_task = 1 }
  /^typedef struct lean_once_cell_t \{/ { in_once = 1 }
  in_thunk && /lean_object \*m_value;/ {
    sub(/lean_object \*m_value;/, "_Atomic(lean_object *) m_value;");
  }
  in_thunk && /lean_object \*m_closure;/ {
    sub(/lean_object \*m_closure;/, "_Atomic(lean_object *) m_closure;");
  }
  in_task && /lean_object \*m_value;/ {
    sub(/lean_object \*m_value;/, "_Atomic(lean_object *) m_value;");
  }
  in_once && /int32_t state;/ {
    sub(/int32_t state;/, "_Atomic(int) state;");
  }
  in_once && /int32_t lock;/ {
    sub(/int32_t lock;/, "_Atomic(int) lock;");
  }
  { print }
  in_thunk && /^\} lean_thunk_object;/ { in_thunk = 0 }
  in_task && /^\} lean_task_object;/ { in_task = 0 }
  in_once && /^\} lean_once_cell_t;/ { in_once = 0 }
' "$types_renamed_tmp" > "$types_block_tmp"

mkdir -p "$(dirname "$output")"

awk -v types_file="$types_block_tmp" '
  BEGIN {
    while ((getline line < types_file) > 0) {
      types = types line "\n";
    }
    close(types_file);
  }
  /^typedef lean_object \* b_lean_obj_res;/ {
    print;
    printf "\n/* BEGIN GENERATED LEAN C ABI TYPES */\n";
    printf "%s", types;
    printf "/* END GENERATED LEAN C ABI TYPES */\n\n";
    skip_types = 1;
    next;
  }
  skip_types && /^typedef void \(\*lean_external_finalize_proc\)\(void \*\);$/ {
    skip_types = 0;
    print;
    next;
  }
  skip_types { next }
  /^#ifdef LEAN_MIMALLOC$/ { skip_mimalloc = 1; next }
  skip_mimalloc && /^#endif$/ { skip_mimalloc = 0; next }
  skip_mimalloc { next }
  { print }
' "$template" > "$output"
