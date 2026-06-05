# Comparison: byteslice

## Files

- C++ Implementation: `runtime/byteslice.cpp`
- C++ Header: `runtime/byteslice.h`
- Rust Implementation: `rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Provides a fast array comparison function `lean_byteslice_beq` which compares two Lean byte slices (represented as tuples of `ByteArray`, `start_index`, `end_index`) using `memcmp`.

## Corresponding Rust Implementation

Ported to Rust directly in `lean_runtime/src/lib.rs` (around line 2759) as `lean_byteslice_beq`. The Rust version uses `std::ptr::eq` and `libc::memcmp` to achieve the identical fast comparison.
