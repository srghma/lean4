# Comparison: ascii

## Files

- C++ Implementation: `util/ascii.cpp`
- C++ Header: `util/ascii.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Provides a set of utility functions to check if characters or strings consist only of safe, "keyboard" ASCII characters (`is_safe_ascii`). It initializes an array of booleans (`g_safe_ascii`) to provide an O(1) lookup.

## Corresponding Rust Implementation

These functions were ported directly into `src/rust/lean_runtime/src/lib.rs` (around line 1507) as `is_safe_ascii_byte`. FFI exports are provided:

- `lean_util_is_safe_ascii_char`
- `lean_util_is_safe_ascii`
- `lean_util_is_safe_ascii_n`

## Discrepancies and Issues

### Memory Model

- The Rust implementation replaces the 256-element global lookup array with a direct `match` statement on the byte value. This avoids global mutable state initialization (`initialize_ascii` and `finalize_ascii` are no longer needed).

### Dependencies (Third-party vs Native Rust)

- Fully native Rust with standard `match`.
