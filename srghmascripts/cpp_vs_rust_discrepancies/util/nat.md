# Comparison: nat

## Files

- C++ Header: `util/nat.h`
- Rust Implementation: None / Handled natively via FFI traits

## Overview of C++ Implementation

Defines a C++ wrapper class `lean::nat` inheriting from `lean::object_ref`. It provides operator overloads (`+`, `-`, `<`, `==`, `<<`, etc.) to easily manipulate Lean `nat` objects (bignums and small scalars) natively within C++ code using familiar arithmetic operators.

## Corresponding Rust Implementation

There is no explicit `nat` wrapper object mimicking this C++ class in the Rust codebase. In Rust, such wrappers are typically defined over `LeanObject` using the `Newtype` pattern and implementing standard traits like `Add`, `Sub`, `Eq`, and `Ord` if native Rust interaction is needed. Currently, the raw Lean object API handles these operations.
