# Comparison: expr_maps

## Files

- C++ Header: `kernel/expr_maps.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides C++ type aliases (`expr_map`, `expr_bi_map`, `expr_cond_bi_map`) for unordered maps where the keys are Lean expressions. These type aliases configure the `lean::unordered_map` to use expression-specific hashing (`expr_hash`) and structural equality (`std::equal_to<expr>` or binder-aware `is_bi_equal_proc`).

## Corresponding Rust Implementation

There is no direct Rust translation for these C++ type aliases. In Rust, standard `HashMap<LeanObject, T>` or specialized expression maps would be used natively, relying on Rust's `Hash` and `Eq` traits rather than C++ templates.
