# Comparison: replace_fn

## Files

- C++ Implementation: `kernel/replace_fn.cpp`
- C++ Header: `kernel/replace_fn.h`
- Rust Implementation: `src/rust/lean_runtime/src/kernel_replace_fn.rs`

## Overview of C++ Implementation

Provides utilities (`replace` and `replace_rec_fn`) for structurally traversing and optionally replacing subexpressions within a Lean expression. It implements internal caching mechanisms (using `lean::unordered_map`) to ensure subexpressions are visited at most once and memory is conserved via sharing.

## Corresponding Rust Implementation

The Rust translation (`kernel_replace_fn.rs`) exposes the `lean_replace_expr` FFI endpoint to Lean. However, much like `for_each_fn`, the heavy recursive tree traversal logic and pattern-matching on C++ expression sum types remains in C++. Rust delegates the actual execution to a C++ shim (`lean_cxx_replace_expr`) to avoid rewriting the intricate C++ lambda logic and caching mechanisms in Rust.

### Dependencies (Third-party vs Native Rust)

- Relies completely on C++ for the traversal logic.
