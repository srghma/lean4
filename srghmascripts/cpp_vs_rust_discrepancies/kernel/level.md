# Comparison: level

## Files

- C++ Implementation: `kernel/level.cpp`
- C++ Header: `kernel/level.h`
- Rust Implementation: `src/rust/lean_runtime/src/kernel_level.rs`

## Overview of C++ Implementation

Implements Lean's universe level system (`level`), including its variant types (Zero, Succ, Max, IMax, Param, MVar). It handles level equivalence checking, normalization, caching, hashing, and structural operations exported to Lean (e.g., `lean_level_eq`, `lean_level_eqv`, `lean_level_mk_data`).

## Corresponding Rust Implementation

The Rust implementation (`kernel_level.rs`) ports the pure bit-packing utility `lean_level_mk_data` and structural equality checks (`lean_level_eq`, `lean_level_eqv` using `level_eq`) natively to Rust since they operate directly on `LeanObject` tags and pointers. However, complex level normalizations, constructors (`mk_max`, `mk_succ`), and initialization are intentionally left in C++ and invoked via shims (`lean_cxx_initialize_level`).

### Other Issues / How to fix them

- Note: In C++, `lean_level_eqv` calls `is_equivalent` which invokes `normalize()`. The Rust implementation simply delegates both `lean_level_eqv` and `lean_level_eq` to the structural `level_eq` function. This may represent a discrepancy in semantic equivalence checking versus structural equality, though it appears intentional within the FFI boundary.
