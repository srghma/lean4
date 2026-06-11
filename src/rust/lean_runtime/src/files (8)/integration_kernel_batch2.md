# Integration — kernel batch 2
# (abstract, instantiate, local_ctx, declaration, environment, equiv_manager)

## Files generated

### Rust (→ src/rust/lean_runtime/src/)
- kernel_abstract.rs
- kernel_instantiate.rs
- kernel_local_ctx.rs
- kernel_declaration.rs
- kernel_environment.rs
- kernel_equiv_manager.rs   ← empty stub; no LEAN_EXPORT symbols

### C++ shims (→ src/kernel/)
- abstract_shims.cpp
- instantiate_shims.cpp
- kernel_misc_shims.cpp     ← covers local_ctx + declaration + environment

## CMakeLists changes

### src/kernel/CMakeLists.txt — ADD to KERNEL_OBJS:
```cmake
abstract_shims.cpp
instantiate_shims.cpp
kernel_misc_shims.cpp
```

Keep the original .cpp files in KERNEL_OBJS — they contain the C++ class
logic that the shims call.

### What to remove from C++ files

**kernel/abstract.cpp** — remove:
  - lean_expr_abstract_range   (now lean_cxx_expr_abstract_range in shim)
  - lean_expr_abstract         (now lean_cxx_expr_abstract in shim)

**kernel/instantiate.cpp** — remove (Rust now re-exports these):
  - lean_expr_instantiate1
  - lean_expr_instantiate
  - lean_expr_instantiate_range
  - lean_expr_instantiate_rev
  - lean_expr_instantiate_rev_range

  NOTE: instantiate_shims.cpp calls the original lean_expr_* functions which
  are still compiled from instantiate.cpp. The Rust wrappers just forward.
  Alternatively you can keep the originals as-is in instantiate.cpp and not
  remove them — the Rust #[no_mangle] symbols will shadow them at link time
  only if they are in the same link group. To avoid duplicate symbol errors,
  either:
  a) Guard the originals with `#ifndef LEAN_RUST_RUNTIME`, or
  b) Rename the C++ originals to `lean_cxx_*` in instantiate.cpp and call
     those from the shim (preferred — consistent with the rest of the codebase).

**kernel/local_ctx.cpp** — remove:
  - initialize_local_ctx body (moved to lean_cxx_initialize_local_ctx)
  - finalize_local_ctx body   (moved to lean_cxx_finalize_local_ctx)

**kernel/declaration.cpp** — remove:
  - initialize_declaration body
  - finalize_declaration body

**kernel/environment.cpp** — remove:
  - lean_add_decl body
  - lean_add_decl_without_checking body
  - initialize_environment body
  - finalize_environment body

**kernel/equiv_manager.cpp** — leave entirely in C++ (no LEAN_EXPORT symbols).

## lib.rs additions

Add after the previous kernel includes:
```rust
include!("kernel_abstract.rs");
include!("kernel_instantiate.rs");
include!("kernel_local_ctx.rs");
include!("kernel_declaration.rs");
include!("kernel_environment.rs");
include!("kernel_equiv_manager.rs");
```

## Notes on instantiate_shims.cpp

The shim currently calls `lean_expr_instantiate` etc. which are the original
`extern "C" LEAN_EXPORT` functions in instantiate.cpp. This creates a circular
dependency if Rust re-exports them with the same name. The cleanest fix is to
rename the C++ originals to `lean_cxx_expr_instantiate_*` (drop the `LEAN_EXPORT`
macro) and call those from the shim. The Rust #[no_mangle] functions then become
the only symbols with the public `lean_expr_*` names.
