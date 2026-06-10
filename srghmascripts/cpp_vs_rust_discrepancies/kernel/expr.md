# Comparison: expr

## Files

- C++ Implementation: `kernel/expr.cpp`
- C++ Header: `kernel/expr.h`
- Rust Implementation: `src/rust/lean_runtime/src/kernel_expr.rs`

## Overview of C++ Implementation

Defines the core `expr` (expression) class and its C++ runtime API (e.g., memory layout helpers `lean_expr_mk_data`, application tracking `lean_expr_mk_app_data`, shifting variables `lower_loose_bvars`, `lift_loose_bvars`, constructors `mk_app`, `mk_bvar`, and various accessors). This is the backbone of Lean's expression tree representation in the C++ kernel.

## Corresponding Rust Implementation

The Rust translation (`kernel_expr.rs`) directly ports the pure numeric bit-packing functions (`lean_expr_mk_data`, `lean_expr_mk_app_data`) and hash mixing algorithms, allowing these critical path allocations to run without crossing the FFI boundary. However, complex tree manipulations such as loose bound variable lifting/lowering (`lean_expr_lower_loose_bvars`, `lean_expr_lift_loose_bvars`) and initialization are delegated to C++ shims (`lean_cxx_expr_lower_loose_bvars`) because they rely on C++ internal traversers (`replace`, `for_each`).

### Dependencies (Third-party vs Native Rust)

- The bitwise packing constants and hashes (like `0xA3B1_95DB` and `0x45D9F3B3`) are exactly mirrored from C++ to ensure `expr` object hashes are deterministic across boundaries.
