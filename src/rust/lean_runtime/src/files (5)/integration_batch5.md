# Batch 5 integration — library/max_sharing, replace_visitor, num, util

## Files

| Rust file | Destination |
|-----------|-------------|
| `library_max_sharing.rs` | `src/rust/lean_runtime/src/library_max_sharing.rs` |
| `library_replace_visitor.rs` | `src/rust/lean_runtime/src/library_replace_visitor.rs` |
| `library_num.rs` | `src/rust/lean_runtime/src/library_num.rs` |
| `library_util.rs` | `src/rust/lean_runtime/src/library_util.rs` |

| C++ shim | Destination |
|----------|-------------|
| `num_shims.cpp` | `src/library/num_shims.cpp` |
| `util_shims.cpp` | `src/library/util_shims.cpp` |

No shims needed for max_sharing or replace_visitor (no LEAN_EXPORT symbols).

## CMakeLists (`src/library/CMakeLists.txt`)

Add to the library target:
```cmake
num_shims.cpp
util_shims.cpp
```

Keep `max_sharing.cpp`, `replace_visitor.cpp`, `num.cpp`, `util.cpp` —
the shims call through to their C++ implementations.

## Symbols to guard/remove from C++ sources

**num.cpp** — remove or guard with `#ifndef LEAN_RUST_RUNTIME`:
- `initialize_num`
- `finalize_num`

**util.cpp** — remove or guard:
- `initialize_library_util`
- `finalize_library_util`
- `initialize_bool`
- `finalize_bool`

## lib.rs additions

```rust
include!("library_max_sharing.rs");
include!("library_replace_visitor.rs");
include!("library_num.rs");
include!("library_util.rs");
```

## Run tests

```sh
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
  make -C build/release -j "$(nproc)" test ARGS='--rerun-failed'
```

## Note on naming

Per the agreed convention, all library/* ports use the `library_` prefix
(not `runtime_`).  The files in `files (4)/` that used `runtime_time_task.rs`
etc. will be renamed in a cleanup pass at the end of porting.
