# Comparison: max_sharing

## Files

- C++ Implementation: `library/max_sharing.cpp`
- C++ Header: `library/max_sharing.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a utility (`max_sharing_fn`) to deeply traverse an expression and return a structurally identical expression but with maximally shared sub-expressions in memory. This helps reduce memory footprint and speeds up equality checks.

## Corresponding Rust Implementation

Max sharing logic is now implemented natively in Lean 4 (`Expr.maxSharing`). The Rust runtime does not need to expose a C++ level max sharing algorithm since `lean_object` reference counting and Lean-level algorithms handle it.
