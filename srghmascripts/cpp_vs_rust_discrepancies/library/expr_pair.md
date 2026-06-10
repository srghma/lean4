# Comparison: expr_pair

## Files

- C++ Header: `library/expr_pair.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a comparison logic (`is_lt`) for a pair of expressions (`expr_pair`), delegating to the `expr_lt` functions. Used mostly as a quick comparator for mapping pairs of expressions to values.

## Corresponding Rust Implementation

No direct Rust runtime port. Lean 4 handles structural comparisons of expression pairs natively when needed (e.g. caching pairs of expressions in MetaM).
