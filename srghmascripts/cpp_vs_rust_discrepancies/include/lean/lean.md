# Comparison: lean.h

## Files

- C++ Header: `include/lean/lean.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs` (and specific definitions spread across the `lean_runtime` crate)

## Overview of C++ Implementation

`include/lean/lean.h` is the foundational C API header for Lean. It defines the core data structures used by the Lean runtime and compiler, including `lean_object`, `lean_array_object`, `lean_string_object`, `lean_closure_object`, etc. It also defines fundamental memory management and reference counting macros/inline functions (`lean_inc`, `lean_dec`, `lean_alloc_small_object`, etc.) and basic tag constants for object types. It is the primary dependency for almost all other C++ files in the project.

## Corresponding Rust Implementation

The types defined in `lean.h` have been ported to Rust in the `lean_runtime` crate, primarily found in `src/rust/lean_runtime/src/lib.rs`. They are defined as `#[repr(C)]` structs to guarantee identical memory layout to the C structures (e.g., `pub struct LeanObject { pub m_rc: i32, pub m_cs_sz: u16, pub m_other: u8, pub m_tag: u8 }`). The memory management functions (`lean_inc`, `lean_dec`, `lean_alloc_small`) are also implemented in Rust as exported `extern "C"` functions or unsafe methods.

## Discrepancies and Issues

### Memory Model

The memory model remains identical. Rust defines the structs with `#[repr(C)]` to match the exact field layout and sizes expected by Lean's code generator. The RC (reference counting) behavior and small object allocator limits (`LEAN_MAX_SMALL_OBJECT_SIZE`, `LEAN_OBJECT_SIZE_DELTA`) are mirrored perfectly.

### Dependencies (Third-party vs Native Rust)

- The C++ header includes `mimalloc` conditionally (`#ifdef LEAN_MIMALLOC`), while the Rust runtime typically relies on the standard system allocator or configures mimalloc globally via Cargo features.
- Threading features (`std::atomic` or `<stdatomic.h>`) in `lean.h` are replaced by `core::sync::atomic::AtomicU32` / `AtomicI32` in Rust.
- Rust specifically implements an unsafe `SendPtr<T>` wrapper to allow moving raw pointers across thread boundaries for thread closures, which is a Rust-specific safety mechanism for dealing with C pointers.

### Other Issues / How to fix them

- **Flexible Array Members:** The C++ structures use C99 flexible array members (e.g., `lean_object * m_objs[];` in `lean_ctor_object`). Rust does not have native support for flexible array members in structs. The Rust port handles this by either omitting the trailing field and relying on unsafe pointer arithmetic (`(ptr as *mut *mut LeanObject).add(1)`), or leaving comments denoting the limitation. This requires careful use of `unsafe` blocks in Rust whenever accessing these trailing arrays. This is functioning correctly and is standard practice for FFI, but introduces a potential safety pitfall during maintenance. No fix needed, but requires awareness.
