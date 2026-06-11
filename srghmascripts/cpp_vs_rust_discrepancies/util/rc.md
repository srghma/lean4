# Comparison: rc

## Files

- C++ Header: `util/rc.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_object_rc.rs`

## Overview of C++ Implementation

Provided standard C++ macros (`MK_LEAN_RC`, `LEAN_COPY_REF`, `LEAN_MOVE_REF`) to inject atomic reference counting fields (`m_rc`) and ref-management methods (`inc_ref`, `dec_ref`) into arbitrary C++ classes.

## Corresponding Rust Implementation

Reference counting for Lean objects is ported and consolidated in `runtime_object_rc.rs`. Rust natively avoids these kinds of invasive C++ macros. `LeanObject` has an atomic `m_rc` field defined via `#[repr(C)]`, and the exact semantics of `lean_inc` and `lean_dec` are implemented as standalone `extern "C"` functions in the Rust runtime. Standard Rust structs use `Arc` or `Rc` rather than custom refcounting.
