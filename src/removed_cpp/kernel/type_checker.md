# Comparison: type_checker

## Files

- C++ Implementation: `kernel/type_checker.cpp`
- C++ Header: `kernel/type_checker.h`
- Rust Implementation: `src/rust/lean_runtime/src/kernel_type_checker.rs`

## Overview of C++ Implementation

Contains the core type-checking algorithm for the Lean kernel. It implements inference rules for the calculus of inductive constructions (CIC), checks definitional equality (`is_def_eq`), performs weak head normal form reduction (`whnf`), and unfolds definitions. It handles the structural traversal of expressions to enforce type correctness and equality.

## Corresponding Rust Implementation

The Rust translation (`kernel_type_checker.rs`) provides the module initialization and finalization shims (`initialize_type_checker` and `finalize_type_checker`). The actual type-checker logic relies heavily on `lean::expr` and is implemented in C++. No type checking logic has been ported to Rust; the kernel continues to use the C++ implementation.
