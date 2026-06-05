# Comparison: elab_environment

## Files

- C++ Implementation: `library/elab_environment.cpp`
- C++ Header: `library/elab_environment.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a C++ wrapper (`elab_environment`) over the kernel `environment` specifically intended for elaboration. It was used to interface with the Lean-level environment when executing elaborator tactics in C++.

## Corresponding Rust Implementation

`Environment` logic is completely natively handled in Lean 4. The `elab_environment` distinction is captured by the different environment states in `CoreM`, `MetaM`, and `ElabM` natively in Lean. The Rust runtime only works with the FFI boundary `lean_object`.
