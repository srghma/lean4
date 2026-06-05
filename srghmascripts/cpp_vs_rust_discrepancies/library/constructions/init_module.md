# Comparison: constructions/init_module

## Files

- C++ Implementation: `library/constructions/init_module.cpp`
- C++ Header: `library/constructions/init_module.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Registered the C++ macros and environments for inductive datatype constructions like `no_confusion`, `cases_on`, `rec_on`, etc.

## Corresponding Rust Implementation

These inductive constructions are entirely implemented in Lean 4 now (e.g. `Lean.Elab.Inductive`, `Lean.Meta.IndPredBelow`, etc.). The Rust runtime does not initialize constructions.
