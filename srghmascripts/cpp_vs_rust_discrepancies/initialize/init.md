# Comparison: init

## Files

- C++ Implementation: `initialize/init.cpp`
- C++ Header: `initialize/init.h`
- Rust Implementation: `rust/lean_runtime/src/lib.rs` (Initialization routines)

## Overview of C++ Implementation

Provided the top-level `initialize` and `finalize` functions for the entire Lean C++ codebase. It sequenced the initialization of all internal C++ submodules (util, thread, kernel, library, frontends, server, etc.).

## Corresponding Rust Implementation

Initialization routines for the runtime are ported to Rust in `lib.rs` (`lean_initialize` and `lean_initialize_runtime_module`). Instead of initializing massive C++ frontends, it only initializes core Lean types and FFI integrations. The rest of the initialization logic is done inside the Lean boot process.
