# Comparison: constructions/no_confusion

## Files

- C++ Header: `library/constructions/no_confusion.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided functions to generate `no_confusion` and `no_confusion_type` declarations for inductive datatypes in the C++ environment. These are used to prove disjointness of constructors and injectivity of constructor arguments.

## Corresponding Rust Implementation

The generation of `no_confusion` theorems is natively implemented in Lean 4 (`Lean.Meta.mkNoConfusion`). There is no Rust runtime component for this construction.
