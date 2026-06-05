# Comparison: for_each_fn

## Files

- C++ Implementation: `kernel/for_each_fn.cpp`
- C++ Header: `kernel/for_each_fn.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a visitor pattern (`for_each`) to traverse Lean expressions recursively. It tracked binder depth (`offset`) and avoided redundant traversals by using a visited set (`expr_set`).

## Corresponding Rust Implementation

No direct Rust port. Deep expression traversal (`Expr.forEach`, `Expr.foldl`, etc.) is fully implemented in Lean 4 standard library and compiler. The runtime layer does not need to traverse expressions except for garbage collection or FFI boundary checks, which use different mechanisms.
