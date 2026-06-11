# Comparison: ffi

## Files

- C++ Implementation: `util/ffi.cpp`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Provides a few string accessors (`lean_get_leanc_extra_flags`, `lean_get_leanc_internal_flags`, `lean_get_linker_flags`, `lean_get_internal_linker_flags`) that return compiler and linker flags for Lean's FFI. In C++, these are implemented as string literals containing CMake `@VARIABLE@` replacement patterns (e.g., `"@LEANC_EXTRA_CC_FLAGS@"`), which CMake substitutes at configure time.

## Corresponding Rust Implementation

These functions were directly ported into `src/rust/lean_runtime/src/lib.rs` (around line 2480).

## Discrepancies and Issues

### Dependencies (Third-party vs Native Rust)

- The C++ implementation relied on CMake text substitution on the source file.
- The Rust implementation uses the `env!` macro at compile-time to embed the flags from environment variables (e.g., `env!("LEAN_RUST_LEANC_EXTRA_CC_FLAGS")`). These variables are presumably set by a `build.rs` script that bridges CMake and Cargo, making it cleaner and avoiding the need to mutate the source file.
