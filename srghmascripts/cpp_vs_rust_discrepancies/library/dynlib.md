# Comparison: dynlib

## Files

- C++ Implementation: `library/dynlib.cpp`
- C++ Header: `library/dynlib.h`
- Rust Implementation: `rust/lean_runtime/src/library_dynlib.rs`

## Overview of C++ Implementation

Provides an abstraction over OS-specific dynamic library loading (`dlopen`/`dlsym` on Unix, `LoadLibrary`/`GetProcAddress` on Windows). It exposes C functions like `lean_dynlib_load`, `lean_dynlib_get`, and `lean_dynlib_symbol_run_as_init` to the Lean runtime, allowing Lean to dynamically load external libraries (plugins).

## Corresponding Rust Implementation

This module has been fully ported to Rust in `library_dynlib.rs`. The Rust implementation uses `extern "C"` blocks to bind to `dlopen`/`dlsym` (Unix) and `LoadLibraryA`/`GetProcAddress` (Windows). It registers Lean external classes (`LeanExternalClass`) with finalizers to ensure libraries are properly closed (`dlclose` or `FreeLibrary`) when garbage collected.

## Discrepancies and Issues

### Memory Model

- Both implement the same Lean external object memory model via `lean_register_external_class` and `lean_runtime_alloc_external`.

### Dependencies (Third-party vs Native Rust)

- The Rust implementation directly binds to the platform's C APIs (e.g., `dlopen` on UNIX, `LoadLibrary` on Windows) without relying on third-party Rust crates like `libloading`.
