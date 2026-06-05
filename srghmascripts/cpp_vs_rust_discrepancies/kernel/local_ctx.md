# Comparison: local_ctx

## Files

- C++ Implementation: `kernel/local_ctx.cpp`
- C++ Header: `kernel/local_ctx.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided the `local_ctx` and `local_decl` classes to track free variables and local binders in the kernel type checker. It maintained the mapping from internal free variable IDs to their types, values (for `let` binders), and names.

## Corresponding Rust Implementation

No direct Rust port exists. The local context (`LocalContext`) is entirely implemented in Lean 4 (`Lean.LocalContext`) using functional data structures (e.g. `PersistentHashMap` / `PersistentArray`). The Rust runtime is oblivious to local contexts and only sees raw expressions.
