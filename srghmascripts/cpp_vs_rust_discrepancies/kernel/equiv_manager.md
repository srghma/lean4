# Comparison: equiv_manager

## Files

- C++ Implementation: `kernel/equiv_manager.cpp`
- C++ Header: `kernel/equiv_manager.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a union-find data structure (`equiv_manager`) over expressions (`expr`) to track equivalence classes during unification or type checking in the old C++ kernel.

## Corresponding Rust Implementation

No direct Rust port exists in `lean_runtime`. Unification and equivalence checking logic, along with union-find data structures (`UnionFind.lean`), are now implemented natively in Lean 4.
