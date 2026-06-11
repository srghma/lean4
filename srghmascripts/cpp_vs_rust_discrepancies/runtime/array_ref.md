# `runtime/array_ref` (`runtime/array_ref.h`)

## Location of corresponding Rust implementation
The C++ `array_ref<T>` template does not have a single corresponding Rust source file. Its C equivalent is embedded in Lean object macros and arrays (`lean_array_cptr`, `lean_array_size`, etc.).
In the Rust codebase, standard operations for Lean Array object interactions are found in `src/rust/lean_runtime/src/runtime_object_array.rs` (which handles the memory and object model details for `lean_array_object`).

## Discrepancies and issues
- **Wrapper Paradigm**: `array_ref<T>` in C++ was an object-oriented wrapper inheriting from `object_ref`, allowing safe, typed access and iterator support for C++ algorithms. In Rust, direct interaction with Lean objects often goes through `*mut lean_object` utilizing unsafe FFI functions or bespoke idiomatic wrappers rather than generic subclassing. The Rust port focuses on exposing the fundamental runtime capabilities rather than replicating the exact typed C++ convenience templates.
- **Porting Strategy**: Replaced by direct usage of native Lean array APIs or idiomatic Rust types `&[T]` / `Vec<T>` at boundaries.
