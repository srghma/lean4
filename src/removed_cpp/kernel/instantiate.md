# Comparison: instantiate

## Files

- C++ Implementation: `kernel/instantiate.cpp`
- C++ Header: `kernel/instantiate.h`
- Rust Implementation: `src/rust/lean_runtime/src/kernel_instantiate.rs`

## Overview of C++ Implementation

Provides utilities to instantiate bound variables in Lean expressions (i.e., replacing loose bound variables with specific expressions) as well as functions for beta-reduction (`head_beta_reduce`, `cheap_beta_reduce`). It exports standard instantiation entry points to the Lean runtime (`lean_expr_instantiate`, `lean_expr_instantiate_rev`, etc.).

## Corresponding Rust Implementation

The Rust translation (`kernel_instantiate.rs`) exposes the `#[no_mangle]` FFI bindings for instantiation operations. Since instantiation operates by structurally traversing expressions using the internal `replace` logic, the Rust implementation delegates entirely to C++ shims (`lean_cxx_expr_instantiate`, etc.). No traversal logic has been ported.

### Dependencies (Third-party vs Native Rust)

- The implementation remains firmly on the C++ side.
