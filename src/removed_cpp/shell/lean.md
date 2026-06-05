# Comparison: lean

## Files

- C++ Implementation: `shell/lean.cpp`
- Rust Implementation: N/A

## Overview of C++ Implementation

A minimal shim containing the C++ `main` function for the `lean` executable, which immediately delegates to `lean_main` in `libleanshared`.

## Corresponding Rust Implementation

No direct Rust equivalent exists for the shell entry point. In modern Lean 4, the executable entry point is defined in Lean itself (`src/lean/main.lean`) which gets compiled to C (or Rust/LLVM backend) and linked with the runtime.
