# Comparison: declaration

## Files

- C++ Implementation: `kernel/declaration.cpp`
- C++ Header: `kernel/declaration.h`
- Rust Implementation: `rust/lean_runtime/src/kernel_declaration.rs` (Partial)

## Overview of C++ Implementation

Defined the core abstract data types for Lean's environment declarations (axioms, definitions, theorems, opaque definitions, mutual blocks, and inductive types). It also mapped to the `constant_info` objects used during type checking.

## Corresponding Rust Implementation

The Rust runtime `kernel_declaration.rs` provides FFI bindings to inspect the underlying `lean_object`s that represent `Declaration`s and `ConstantInfo`. However, the comprehensive data types (like `DefinitionVal`, `InductiveVal`, `ReducibilityHints`) are now defined purely in Lean 4 (`Lean.Declaration`). The Rust side just wraps `lean_object*` fields for low-level interactions if needed.

## Discrepancies and Issues

### Memory Model

- Relies on Lean 4's standard `lean_object` reference counting instead of manual `object_ref` C++ wrappers.
