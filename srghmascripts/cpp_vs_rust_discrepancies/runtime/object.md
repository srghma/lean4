# Comparison: object

## Files

- C++ Implementation: `runtime/object.cpp`
- C++ Header: `runtime/object.h`
- Rust Implementations:
  - `rust/lean_runtime/src/runtime_object_array.rs`
  - `rust/lean_runtime/src/runtime_object_nat_int.rs`
  - `rust/lean_runtime/src/runtime_object_panic.rs`
  - `rust/lean_runtime/src/runtime_object_rc.rs`
  - `rust/lean_runtime/src/runtime_object_string.rs`

## Overview of C++ Implementation

`object.cpp` was one of the largest and most central files in the C++ runtime. It implemented memory layout, allocation, initialization, hashing, equality checking, boxing/unboxing, and reference counting (`inc`/`dec`) for every core Lean object type (Constructors, Closures, Arrays, Strings, Nats, Ints, Tasks, external C++ classes, etc.).

## Corresponding Rust Implementation

To make the codebase manageable, `object.cpp` was split into multiple thematic Rust files under `lean_runtime/src/`:

- `runtime_object_array.rs`: Logic for Lean `Array` and `ByteArray` allocation, pushing, popping, and copying.
- `runtime_object_nat_int.rs`: Allocation and runtime operations for `Nat` and `Int` (though many operations still delegate back via FFI to `mpz.cpp` for large math).
- `runtime_object_panic.rs`: Panic handling and trace generation when an object operation fails.
- `runtime_object_rc.rs`: Reference counting (the `lean_inc`, `lean_dec` logic), including deep object traversal for deallocation.
- `runtime_object_string.rs`: UTF-8 string concatenation, encoding, and slicing for Lean `String`.

Core structure definitions are also spread across `lib.rs` and other headers, replacing the C macros in `object.h` with Rust structs (`LeanObject`, `LeanString`, `LeanCtorObject`, etc.) and `#[repr(C)]`.

## Discrepancies and Issues

### Memory Model

- The Rust implementations strictly use `unsafe` blocks when directly mapping memory and manipulating refcounts, ensuring identical memory layouts to the C++ original (via `#[repr(C)]` and `extern "C"`).

### Dependencies (Third-party vs Native Rust)

- Relies on native Rust slice manipulations and UTF-8 validation rather than standard C library functions (`memcpy`, `memcmp`, `strlen`), though FFI to libc is still used in places where performance matching is guaranteed.
