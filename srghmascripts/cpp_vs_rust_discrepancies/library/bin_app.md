# Comparison: bin_app

## Files

- C++ Implementation: `library/bin_app.cpp`
- C++ Header: `library/bin_app.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided utility functions (`is_bin_app`, `mk_bin_rop`, `foldr`) for working with binary application expressions in Lean. It made it easier to construct or destructure deeply nested applications of binary operators.

## Corresponding Rust Implementation

No direct Rust port exists in `lean_runtime`. Building and manipulating Lean applications (`Expr.app`) is now done natively in Lean 4 via standard library functions (e.g. `mkApp2`, `Expr.getAppFnArgs`).
