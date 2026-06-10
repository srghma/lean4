# Comparison: expr_eq_fn

## Files

- C++ Implementation: `kernel/expr_eq_fn.cpp`
- C++ Header: `kernel/expr_eq_fn.h`
- Rust Implementation: `rust/lean_runtime/src/kernel_expr.rs` (Partial)

## Overview of C++ Implementation

Provided deep structural equality checks (`is_equal`, `is_bi_equal`) for expressions. `is_equal` checks physical equality then traverses expressions ignoring binder information (like binder names), while `is_bi_equal` includes binder info.

## Corresponding Rust Implementation

Expression equality is exposed in `kernel_expr.rs` using FFI stubs (`lean_expr_eqv` or structural equality through pointer checks). However, deep semantic equality and structural traversal are heavily implemented in Lean 4 itself (`Expr.lean`). The runtime provides fast pointer equality and basic structural properties for core operations.
