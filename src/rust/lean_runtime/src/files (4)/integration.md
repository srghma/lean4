# Integration instructions

## Files generated

### runtime/exception

| File | Destination |
|------|-------------|
| `runtime_exception.rs` | `src/rust/lean_runtime/src/runtime_exception.rs` |
| `exception_shims.cpp` | `src/runtime/exception_shims.cpp` |

**CMakeLists** (`src/runtime/CMakeLists.txt`): add `exception_shims.cpp` to `RUNTIME_OBJS`.
Remove `exception.cpp` from `RUNTIME_OBJS` (or delete the file after gutting its `extern "C"` bodies).

**lib.rs**: confirm `include!("runtime_exception.rs");` is present.

The bodies to remove from `exception.cpp`:
- `throw_get_stack_size_failed`
- `throw_stack_space_exception`
- `throw_heartbeat_exception`
- `throw_memory_exception`
- `lean_throw_interrupted`
- `lean_uncaught_exceptions`

---

### library/time_task

| File | Destination |
|------|-------------|
| `runtime_time_task.rs` | `src/rust/lean_runtime/src/runtime_time_task.rs` |
| `time_task_shims.cpp` | `src/library/time_task_shims.cpp` |

**CMakeLists** (`src/library/CMakeLists.txt`): add `time_task_shims.cpp`.
Keep `time_task.cpp` — the shims call through to its C++ implementations.

**lib.rs**: add `include!("runtime_time_task.rs");`

The bodies moved to Rust (delegating via shims):
- `lean_display_cumulative_profiling_times` (the `BaseIO Unit` version)
- `lean_profileit`
- `initialize_time_task` / `finalize_time_task`

---

### library/annotation

| File | Destination |
|------|-------------|
| `runtime_annotation.rs` | `src/rust/lean_runtime/src/runtime_annotation.rs` |
| `annotation_shims.cpp` | `src/library/annotation_shims.cpp` |

**CMakeLists**: add `annotation_shims.cpp`.
Keep `annotation.cpp`.

**lib.rs**: add `include!("runtime_annotation.rs");`

---

### library/expr_lt

| File | Destination |
|------|-------------|
| `runtime_expr_lt.rs` | `src/rust/lean_runtime/src/runtime_expr_lt.rs` |
| `expr_lt_shims.cpp` | `src/library/expr_lt_shims.cpp` |

**CMakeLists**: add `expr_lt_shims.cpp`.
Remove `lean_expr_quick_lt` / `lean_expr_lt` bodies from `expr_lt.cpp`.

**lib.rs**: add `include!("runtime_expr_lt.rs");`

---

### library/formatter

| File | Destination |
|------|-------------|
| `runtime_formatter.rs` | `src/rust/lean_runtime/src/runtime_formatter.rs` |
| `formatter_shims.cpp` | `src/library/formatter_shims.cpp` |

**CMakeLists**: add `formatter_shims.cpp`.
Keep `formatter.cpp` (owns `g_print`, `operator<<`, `set_print_fn`).

**lib.rs**: add `include!("runtime_formatter.rs");`

---

## lib.rs include order (add after existing includes)

```rust
include!("runtime_exception.rs");
include!("runtime_time_task.rs");
include!("runtime_annotation.rs");
include!("runtime_expr_lt.rs");
include!("runtime_formatter.rs");
```

## Run tests

```sh
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
  make -C build/release -j "$(nproc)" test ARGS='--rerun-failed'
```
