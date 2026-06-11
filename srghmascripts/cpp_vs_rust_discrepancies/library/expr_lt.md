# Comparison: expr_lt

## Files

- C++ Implementation: `library/expr_lt.cpp`
- C++ Header: `library/expr_lt.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a total ordering (`is_lt`) over `expr` objects in the old C++ runtime. This was useful for sorting expressions or storing them in tree-based maps (`rb_expr_map`) and sets. It could optionally use hash codes as a fast-path comparison.

## Corresponding Rust Implementation

A total order over expressions (`Expr.lt`) is implemented in native Lean 4. The Rust runtime only exposes fast physical pointer comparisons (`lean_expr_eqv`) and structural equality for basic FFI use cases, not a full deep structural less-than comparison.
