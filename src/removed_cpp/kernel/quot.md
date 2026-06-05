# Comparison: quot

## Files

- C++ Implementation: `kernel/quot.cpp`
- C++ Header: `kernel/quot.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided definitions and reduction rules for quotient types (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) in the C++ kernel. It contained the hardcoded rules (`quot_reduce_rec`, `quot_is_stuck`) to reduce quotient expressions during definitional equality checking.

## Corresponding Rust Implementation

Quotient reduction logic is entirely ported to Lean 4 native code (`Lean.Meta.Reduce` or kernel equivalents). The Rust runtime no longer performs these high-level expression reductions. It only interacts with quotients generically if they pass through FFI as standard `lean_object`s.
