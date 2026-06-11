# Integration — kernel batch 3
# (quot, type_checker, inductive, expr, trace)

## Files generated

### Rust (→ src/rust/lean_runtime/src/)
- kernel_quot.rs
- kernel_type_checker.rs
- kernel_inductive.rs
- kernel_expr.rs             ← contains portable lean_expr_mk_data / lean_expr_mk_app_data
- kernel_trace.rs            ← initialize_trace / finalize_trace are no-ops

### C++ shims (→ src/kernel/)
- kernel_batch3_shims.cpp    ← covers all five files

## CMakeLists changes

### src/kernel/CMakeLists.txt — ADD to KERNEL_OBJS:
```cmake
kernel_batch3_shims.cpp
```

Keep quot.cpp, type_checker.cpp, inductive.cpp, expr.cpp, trace.cpp in KERNEL_OBJS.

### What to remove from C++ files

**kernel/quot.cpp** — remove (Rust now exports these):
  - initialize_quot (rename C++ body to lean_cxx_initialize_quot)
  - finalize_quot   (rename C++ body to lean_cxx_finalize_quot)

**kernel/type_checker.cpp** — remove:
  - initialize_type_checker
  - finalize_type_checker

**kernel/inductive.cpp** — remove:
  - initialize_inductive
  - finalize_inductive

**kernel/expr.cpp** — remove (Rust now exports these):
  - lean_expr_mk_data           (pure Rust)
  - lean_expr_mk_app_data       (pure Rust)
  - lean_expr_has_loose_bvar    (delegates to lean_cxx_expr_has_loose_bvar)
  - lean_expr_lower_loose_bvars (delegates to lean_cxx_expr_lower_loose_bvars)
  - lean_expr_lift_loose_bvars  (delegates to lean_cxx_expr_lift_loose_bvars)
  - initialize_expr             (delegates to lean_cxx_initialize_expr)
  - finalize_expr               (delegates to lean_cxx_finalize_expr)

**kernel/trace.cpp** — remove:
  - initialize_trace  (was a no-op, Rust version is also no-op)
  - finalize_trace    (was a no-op, Rust version is also no-op)

## lib.rs additions

Add after the kernel batch 2 includes:
```rust
include!("kernel_quot.rs");
include!("kernel_type_checker.rs");
include!("kernel_inductive.rs");
include!("kernel_expr.rs");
include!("kernel_trace.rs");
```

## Notes on lean_expr_mk_data / lean_expr_mk_app_data

These are the two functions in expr.cpp with purely numeric logic.
The Rust implementations match the C++ exactly:

lean_expr_mk_data:
  - Clamps approxDepth to 255
  - Panics if bvarRange is not a scalar or exceeds 1_048_575 (20-bit)
  - Packs: hash[31:0] | depth[39:32] | hasFVar[40] | hasExprMVar[41] |
           hasLevelMVar[42] | hasLevelParam[43] | bvarRange[63:44]

lean_expr_mk_app_data:
  - depth = max(depth_f, depth_a) + 1, clamped to 255
  - range = max(range_f, range_a)
  - hash = hash32(f_data as u32, a_data as u32) using the same mix as runtime/hash.h
  - flags = (f_data | a_data) & (0xF << 40)  [union of the four flag bits]

The hash mix in Rust uses the same polynomial as C++ hash(size_t a, size_t b):
  v = (a + b + seed) ^ (v >> 16); v *= magic; v ^= (v >> 16)
  where seed = 0xA3B195DB and magic = 0x45D9F3B3.

lean_expr_has_loose_bvar, lean_expr_lower_loose_bvars, lean_expr_lift_loose_bvars
all delegate to C++ because they call replace() / for_each() with C++ lambdas
over lean::expr.
