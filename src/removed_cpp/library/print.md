# Comparison: print

## Files

- C++ Implementation: `library/print.cpp`
- C++ Header: `library/print.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided legacy utilities for formatting Lean expressions and renaming bound variables to avoid name clashes when printing (`binding_body_fresh`).

## Corresponding Rust Implementation

`Expr` printing is now done functionally using `Lean.Meta.ppExpr` and standard library formatting logic. Variable renaming during pretty-printing is handled directly within the Lean elaborator/pretty printer.
