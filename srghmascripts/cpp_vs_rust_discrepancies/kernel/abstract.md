# Comparison: abstract

## Files

- C++ Implementation: `kernel/abstract.cpp`
- C++ Header: `kernel/abstract.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided utilities for "abstracting" free variables in Lean expressions into bound variables (De Bruijn indices). This is a fundamental operation when constructing lambda or pi expressions in the kernel.

## Corresponding Rust Implementation

No direct Rust equivalent exists in the `lean_runtime` core FFI. The abstraction algorithm is fully implemented in Lean 4's standard library (`Expr.abstract`). The runtime only handles fast binding operations through the native Lean code compilation rather than exporting a C++ abstraction routine.
