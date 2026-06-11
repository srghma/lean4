# Comparison: test

## Files

- C++ Header: `util/test.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A trivial header file that just ensured `LEAN_DEBUG` was defined for unit tests and included debug helpers.

## Corresponding Rust Implementation

No need for a C++-specific test helper. Rust/Lean 4 tests use standard cargo test and lean testing infrastructure.
