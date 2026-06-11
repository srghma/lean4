# Comparison: instantiate_mvars

## Files

- C++ Implementation: `library/instantiate_mvars.cpp`
- Rust Implementation: N/A (Has similar logic in `rust/lean_runtime/src/kernel_instantiate.rs` or Lean 4 `Lean.Meta.InstantiateMVars`)

## Overview of C++ Implementation

Provided a two-pass algorithm (`instantiate_direct_fn`, `instantiate_delayed_fn`) for instantiating metavariables in Lean expressions. It efficiently handled nested delayed-assigned metavariables and preserved structural sharing using custom caches and scopes.

## Corresponding Rust Implementation

`instantiateMVars` is primarily implemented in Lean 4's `MetaM` monad today. However, if there are core `lean_instantiate_expr_mvars` stubs, they have either been ported to Rust in the `lean_runtime` library or the logic is simply handled in Lean. The old C++ `instantiate_mvars.cpp` seems to have some Rust-like rewrite (`kernel/instantiate.h`? Actually wait, the file has a 2026 copyright and authors "Joachim Breitner" suggesting it might have been recently modified or ported, but it's in `removed_cpp` meaning the C++ version is gone).
