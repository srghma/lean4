# Comparison: module

## Files

- C++ Implementation: `library/module.cpp`
- C++ Header: `library/module.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a `write_module` function to serialize a Lean environment (`elab_environment`) out to an `.olean` file.

## Corresponding Rust Implementation

`Olean` serialization and deserialization is now implemented natively in Lean 4 (`Lean.writeModule`). The Rust runtime and C++ `lean_runtime` only provide the low-level object graph serialization primitives (`lean_serialize_object`, `lean_write_module`), while the high-level logic resides in Lean.
