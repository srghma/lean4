# `runtime/object_ref` (`runtime/object_ref.h` and `runtime/object_ref.cpp`)

## Location of corresponding Rust implementation
The implementation corresponds to the core object lifecycle management functions in `src/rust/lean_runtime/src/runtime_object_rc.rs` and the explicit FFI wrappers for Lean objects (like `b_obj_arg`, `obj_arg`) defined in `src/rust/lean_runtime/src/lib.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ implementation provided `lean::object_ref`, an RAII C++ smart pointer for `lean_object *`. It automatically handled reference counting via `inc` on construction and `dec` on destruction, with move semantics and helper methods. In the Rust port, manual reference counting through explicit FFI (`lean_inc`, `lean_dec`) or idiomatic Rust wrappers (like `Obj`) takes over this responsibility.
- **Porting Status**: Replaced by Rust memory management patterns and the low-level garbage collector / reference counting traversal implemented natively in `runtime_object_rc.rs`.
