# Comparison: inductive

## Files

- C++ Implementation: `kernel/inductive.cpp`
- C++ Header: `kernel/inductive.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided definitions for checking properties of inductive datatypes, handling K-axiom (`to_cnstr_when_K`), struct-eta expansion (`to_cnstr_when_structure`), and implementing the core reduction rules for inductive recursors (`inductive_reduce_rec`).

## Corresponding Rust Implementation

Inductive reduction and definitional equality checks for inductive types are completely ported to Lean 4 natively. The C++ kernel's reduction logic is replaced by the Lean-level kernel (`Lean.Meta.Reduce` and the compiled Lean kernel execution).
