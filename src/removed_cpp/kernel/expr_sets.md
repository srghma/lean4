# Comparison: expr_sets

## Files

- C++ Header: `kernel/expr_sets.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides a C++ type alias (`expr_set`) for an unordered set where elements are Lean expressions, utilizing `expr_hash` and `std::equal_to<expr>` to enforce structural uniqueness.

## Corresponding Rust Implementation

No direct Rust translation exists since this is purely a C++ type definition. If ported, Rust code would simply use `HashSet<LeanObject>` combined with appropriate `Hash`/`Eq` implementations.
