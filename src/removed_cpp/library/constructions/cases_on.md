# Comparison: constructions/cases_on

## Files

- C++ Implementation: `library/constructions/cases_on.cpp`
- C++ Header: `library/constructions/cases_on.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a function `mk_cases_on` to generate the `casesOn` recursor for an inductive datatype, allowing pattern matching in definitions and proofs.

## Corresponding Rust Implementation

`casesOn` generation is implemented entirely in native Lean 4 (`Lean.Meta.mkCasesOn`). The Rust runtime is not involved.
