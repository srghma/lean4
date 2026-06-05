# Comparison: init_module

## Files

- C++ Implementation: `runtime/init_module.cpp`
- C++ Header: `runtime/init_module.h`
- Rust Implementation: `rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Contains the top-level initialization and finalization routines for the entire Lean runtime (`lean_initialize_runtime_module`). It recursively calls sub-initializers for allocators, threads, I/O, objects, processes, and libuv.

## Corresponding Rust Implementation

Ported to Rust directly in `lean_runtime/src/lib.rs` (around line 1826). The Rust implementation performs the same sequential initialization by calling the respective ported `initialize_*` functions for the various runtime subsystems.
