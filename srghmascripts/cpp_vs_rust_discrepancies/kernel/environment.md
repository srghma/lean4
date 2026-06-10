# Comparison: environment

## Files

- C++ Implementation: `kernel/environment.cpp`
- C++ Header: `kernel/environment.h`
- Rust Implementation: `src/rust/lean_runtime/src/kernel_environment.rs`

## Overview of C++ Implementation

The environment manages the set of declarations (axioms, definitions, theorems, inductives, etc.) that have been validated and added to the Lean kernel. It performs top-level checks when new declarations are added, invokes the type checker to ensure correctness, and records diagnostic information.

## Corresponding Rust Implementation

The Rust translation (`kernel_environment.rs`) exposes `#[no_mangle]` FFI bindings for `lean_add_decl` and `lean_add_decl_without_checking`. It correctly manages the thread-local state (`max_heartbeat` and cancellation tokens) before delegating to the generated Lean kernel implementation functions or C++ shims (`lean_kernel_add_decl_impl_extern`).
