# Comparison: expr_cache

## Files

- C++ Implementation: `kernel/expr_cache.cpp`
- C++ Header: `kernel/expr_cache.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a simple, fixed-capacity cache (`expr_cache`) for mapping `expr` to `expr` in the C++ kernel. It was essentially an array acting as a hash table with collision overwrites, used for memoization in operations like substitution and abstraction.

## Corresponding Rust Implementation

Memoization maps in the Lean 4 compiler are now largely implemented in Lean itself via `HashMap Expr Expr` or specialized `StateM` structures in the Lean runtime. There is no direct Rust port for `expr_cache` because the kernel algorithms it served have been moved to Lean.
