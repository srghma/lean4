# Comparison: macros

## Files

- C++ Header: `util/macros.h`
- Rust Implementation: None

## Overview of C++ Implementation

Provides common C++ preprocessor stringification macros (`LEAN_STR` and `LEAN_XSTR`).

## Corresponding Rust Implementation

There is no Rust equivalent because Rust natively provides `stringify!()` and `concat!()` macros as part of the language standard library. The C preprocessor macros are no longer required in a Rust-centric build.

### Dependencies (Third-party vs Native Rust)

- Native Rust macros (`stringify!`) seamlessly handle these cases without explicit definition.
