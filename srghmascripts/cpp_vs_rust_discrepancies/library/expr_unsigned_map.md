# Comparison: expr_unsigned_map

## Files

- C++ Header: `library/expr_unsigned_map.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A templated wrapper over `std::unordered_map` that mapped pairs of `(expr, unsigned)` to values. It explicitly cached the hash of the pair to optimize lookups. This was often used in memoization tables across the kernel and library where an expression and a numeric parameter (like a depth or offset) uniquely identified a subproblem.

## Corresponding Rust Implementation

There is no equivalent in the `lean_runtime` Rust FFI. Algorithms requiring this kind of stateful memoization have been ported to native Lean code using `HashMap` and `StateM`.
