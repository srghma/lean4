# Comparison: llvm

## Files

- C++ Implementation: `library/llvm.cpp`
- Rust Implementation: `rust/lean_runtime/src/library_llvm.rs`

## Overview of C++ Implementation

Provides barebones bindings to the LLVM C FFI, enabling Lean's compiler backend (`src/Lean/Compiler/IR/EmitLLVM.lean`) to generate LLVM bitcode from Lean IR. Exposes C functions that are called by Lean (e.g. `lean_llvm_create_context`, `lean_llvm_add_function`, `lean_llvm_build_add`) and simply map them to the underlying LLVM C API.

## Corresponding Rust Implementation

This module has been ported to Rust in `library_llvm.rs`. The Rust version provides stub versions of the LLVM bindings (returning errors/panics using `llvm_disabled_error()`) indicating that native LLVM backend support via this specific FFI mechanism has been disabled or replaced in the Rust port, possibly relying on an external toolchain or different code generation approach (e.g. C-based codegen).

### Dependencies (Third-party vs Native Rust)

- The C++ version depended directly on the LLVM library. The Rust version acts as a stub, so the LLVM dependency is effectively removed at the FFI boundary level for these functions.

### Other Issues / How to fix them

- If LLVM JIT/codegen is needed directly within Lean, the Rust bindings would need to be linked against the LLVM C API or use a Rust crate like `llvm-sys`.
