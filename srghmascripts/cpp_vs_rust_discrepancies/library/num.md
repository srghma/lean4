# Comparison: num

## Files

- C++ Implementation: `library/num.cpp`
- C++ Header: `library/num.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided legacy utilities for dealing with numerals encoded via `bit0`, `bit1`, `zero`, and `one`. This was the way natural numbers and integers were represented as expressions in Lean 3 before native number literals were introduced.

## Corresponding Rust Implementation

Lean 4 uses native `Nat` and `Int` literals (via `Expr.lit`) which are backed by `mpz`. The `bit0`/`bit1` encoding is obsolete. The Rust runtime and native Lean 4 simply work with literal expressions, completely replacing this C++ module.
