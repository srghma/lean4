# Integration — kernel batch (level, expr_eq_fn, expr_cache, replace_fn, for_each_fn)

## Files generated

### Rust (→ src/rust/lean_runtime/src/)
- kernel_level.rs
- kernel_expr_eq_fn.rs
- kernel_expr_cache.rs      ← empty stub; expr_cache.cpp stays in C++ (no LEAN_EXPORT)
- kernel_replace_fn.rs
- kernel_for_each_fn.rs

### C++ shims (→ src/kernel/)
- level_shims.cpp
- expr_eq_fn_shims.cpp
- replace_fn_shims.cpp
- for_each_fn_shims.cpp
(no shim needed for expr_cache — it has no LEAN_EXPORT symbols)

## CMakeLists changes

### src/kernel/CMakeLists.txt — ADD shim files to KERNEL_OBJS:
```cmake
level_shims.cpp
expr_eq_fn_shims.cpp
replace_fn_shims.cpp
for_each_fn_shims.cpp
```

Keep level.cpp, expr_eq_fn.cpp, replace_fn.cpp, for_each_fn.cpp in KERNEL_OBJS — they
contain C++ class logic that the shims call into.

### What to remove from C++ files
From kernel/level.cpp — remove (Rust now owns them):
  - lean_level_mk_data
  - lean_level_eqv
  - lean_level_eq
  - initialize_level  (body moved to lean_cxx_initialize_level shim)
  - finalize_level    (body moved to lean_cxx_finalize_level shim)

From kernel/expr_eq_fn.cpp — remove:
  - lean_expr_eqv     (body moved to lean_cxx_expr_eqv shim)
  - lean_expr_equal   (body moved to lean_cxx_expr_equal shim)

From kernel/replace_fn.cpp — remove:
  - lean_replace_expr (body moved to lean_cxx_replace_expr shim)

From kernel/for_each_fn.cpp — remove:
  - lean_find_expr     (body moved to lean_cxx_find_expr shim)
  - lean_find_ext_expr (body moved to lean_cxx_find_ext_expr shim)

## lib.rs additions

Add after the existing kernel/library include! lines:
```rust
include!("kernel_level.rs");
include!("kernel_expr_eq_fn.rs");
include!("kernel_expr_cache.rs");
include!("kernel_replace_fn.rs");
include!("kernel_for_each_fn.rs");
```

## Notes

**lean_level_mk_data** is the only function in this batch with purely numeric
logic portable to Rust.  The shim design ensures lean_cxx_initialize_level still
calls the real C++ initialize_level() (which allocates g_level_zero/g_level_one
as persistent Lean objects) — if you try to move that logic to Rust you would
need to replicate lean_level_mk_zero() which is itself Lean-generated code.

**expr_cache.cpp** has zero LEAN_EXPORT symbols.  Its class is used internally
by replace_fn, instantiate, etc.  Leave it in C++ entirely; the stub .rs file
is documentation only.

**replace_fn.cpp** has two internal classes (replace_rec_fn, replace_fn) plus
one LEAN_EXPORT.  The shim simply calls `replace_fn(f)(e)` which is the same
code path the original extern "C" body used — no observable difference.
