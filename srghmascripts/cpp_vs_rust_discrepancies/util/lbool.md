# Comparison: lbool

## Files

- C++ Implementation: `util/lbool.cpp`
- C++ Header: `util/lbool.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Defines a ternary boolean type `lbool` (`l_false`, `l_undef`, `l_true`) and overloads `std::ostream` `operator<<` to allow easy printing of `lbool` values.

## Corresponding Rust Implementation

The Rust implementation (`src/rust/lean_runtime/src/lib.rs` around line 1607) replaces the `std::ostream` `operator<<` overload with a C-FFI function `lean_util_lbool_name(value: i32) -> *const c_char`.

### Dependencies (Third-party vs Native Rust)

- Replaces C++ `<iostream>` with a standard C-style string return, as Rust cannot natively hook into C++ `std::ostream` operators.
