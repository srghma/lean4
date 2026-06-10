# Comparison: kvmap

## Files

- C++ Implementation: `util/kvmap.cpp`
- C++ Header: `util/kvmap.h`
- Rust Implementation: None

## Overview of C++ Implementation

Defines `lean::data_value`, a C++ wrapper object representing Lean data values (`String`, `Bool`, `Name`, `Nat`, etc.), and `lean::kvmap`, which is an association list (`list_ref<kvmap_entry>`). It provides getters and setters (`get_string`, `set_nat`, etc.) to manipulate Lean key-value maps from C++.

## Corresponding Rust Implementation

There is no direct Rust translation for these C++ wrapper objects. In the Rust runtime, Lean objects like `KVMap` (an association list) and `DataValue` are handled directly through the base `LeanObject` FFI, avoiding the need for a specialized C++-style class hierarchy and typed getters/setters.

### Dependencies (Third-party vs Native Rust)

- The C++ abstraction layer was discarded in favor of manipulating raw `LeanObject` structures where necessary.
