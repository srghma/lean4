# Comparison: name

## Files

- C++ Implementation: `util/name.cpp`
- C++ Header: `util/name.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Defines `lean::name`, a C++ wrapper class around the `lean_name` FFI representation. It provides a rich set of object-oriented utilities for name creation, manipulation, comparisons (`quick_cmp`, `is_prefix_of`, etc.), hashing (`lean_name_hash_exported`), and stringification. It relies on C++ memory management and `<iostream>` for formatting.

## Corresponding Rust Implementation

There is no direct Rust `name` struct replicating this C++ class hierarchy. Instead, the raw Lean object functions are implemented directly in `src/rust/lean_runtime/src/lib.rs` (e.g., `lean_name_hash_ptr_rs` around line 1224) and operate on `*mut LeanObject`. Higher-level Rust constructs (like formatting names for `Debug` or `Display`) handle stringification directly without a rigid C++-like wrapper object.

### Dependencies (Third-party vs Native Rust)

- Discards the `lean::name` wrapper class in favor of direct `LeanObject` manipulation to reduce boilerplate and integrate better with standard Rust idioms.
