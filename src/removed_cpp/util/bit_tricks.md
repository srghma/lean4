# Comparison: bit_tricks

## Files

- C++ Implementation: `util/bit_tricks.cpp`
- C++ Header: `util/bit_tricks.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Contains simple bit manipulation utilities, mainly:

- `is_power_of_two(unsigned v)` (inlined in the header)
- `log2(unsigned v)` (fast integer log2)
- A shadowed `double log2(int v)` to catch and prevent accidental calls to `<cmath>` `log2(int)`.

## Corresponding Rust Implementation

The implementations were moved directly into `src/rust/lean_runtime/src/lib.rs` (around line 1581):

- `lean_util_log2` accurately implements the fast bitwise integer `log2`.
- The `is_power_of_two` logic is natively replaced by Rust's built-in `n.is_power_of_two()` available on standard integer types, so no FFI wrapper was explicitly created.

## Discrepancies and Issues

### Memory Model

- No memory model discrepancies, as this file consists purely of fast scalar bit operations.

### Dependencies (Third-party vs Native Rust)

- Native Rust logic handles the `is_power_of_two` behavior seamlessly.

### Other Issues / How to fix them

- The "poison pill" `double log2(int v)` to avoid standard library `log2` bugs is no longer necessary in Rust, and was omitted.
