# Comparison: replace_visitor

## Files

- C++ Implementation: `library/replace_visitor.cpp`
- C++ Header: `library/replace_visitor.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a base class `replace_visitor` for expression transformations. Subclasses overrode `visit_*` methods to rewrite specific expression kinds, and the base class handled the recursive traversal and memoization (via `expr_bi_map` cache) to preserve sub-expression sharing.

## Corresponding Rust Implementation

No direct Rust port exists. Expression transformations and mapping functions (like `Expr.replace`) are now implemented functionally in native Lean 4, which handles its own traversal and caching without relying on C++ visitor patterns.
