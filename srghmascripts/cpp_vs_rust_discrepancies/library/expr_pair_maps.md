# Comparison: expr_pair_maps

## Files

- C++ Header: `library/expr_pair_maps.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A templated wrapper `expr_pair_struct_map` over `std::unordered_map` taking `expr_pair` as keys, providing structural equality via `expr_pair_hash` and `expr_pair_eq`. Used for caching operations mapping two expressions to a result.

## Corresponding Rust Implementation

No direct Rust FFI equivalent. Memoizing over pairs of expressions is done natively in Lean 4.
