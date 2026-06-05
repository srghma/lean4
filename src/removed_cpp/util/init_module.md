# Comparison: init_module

## Files

- C++ Implementation: `util/init_module.cpp`
- C++ Header: `util/init_module.h`
- Rust Implementation: `rust/lean_runtime/src/lib.rs` (Initialization)

## Overview of C++ Implementation

Contains the initialization (`initialize_util_module`) and finalization routines for the `util` submodule of Lean. It initializes runtime components, ASCII utilities, name handling, name generation, and configuration options.

## Corresponding Rust Implementation

Initialization routines have been ported to Rust in `lib.rs` (`lean_initialize_runtime_module` and related shims). Since much of `util` was integrated directly into the `lean_runtime` library or replaced by standard Rust constructs (e.g. `options` moved to Lean itself), the `initialize_util_module` concept is flatter in the Rust port. `name` initialization and `runtime` initialization are still explicitly called.
