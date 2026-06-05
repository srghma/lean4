# Comparison: init_module

## Files

- C++ Implementation: `kernel/init_module.cpp`
- C++ Header: `kernel/init_module.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Contains the standard C++ module initialization and finalization boilerplate (`initialize_kernel_module` and `finalize_kernel_module`) that recursively calls the init/finalize routines for all subsystems within the Lean kernel (e.g., `initialize_level`, `initialize_expr`, `initialize_type_checker`).

## Corresponding Rust Implementation

Rust relies on the C++ layer for module initialization logic across the kernel. `init_module` itself was not ported, though its sub-components might expose Rust FFI shims for initialization (like `lean_cxx_initialize_environment`).
