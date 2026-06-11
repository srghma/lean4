# `runtime/list_ref` (`runtime/list_ref.h`)

## Location of corresponding Rust implementation
Similar to `array_ref.h`, there is no direct equivalent file for `list_ref<T>`.

## Discrepancies and issues
- **Wrapper Paradigm**: The C++ `list_ref<T>` class was an object-oriented wrapper over `object_ref` to handle Lean's singly-linked list cells (constructors with 2 fields: head and tail). It provided convenience methods like `map`, `filter`, `length`, and iterators.
- **Rust Approach**: In Rust, Lean list manipulation is not abstracted through a generic trait or struct in the runtime port, as the runtime focuses heavily on primitives (`runtime_object_rc.rs`, `runtime_object_panic.rs`, etc.). Any list processing from Rust into Lean space uses direct `lean_ctor_get` and `lean_alloc_ctor` calls, or is just written in Lean itself. The convenience C++ template layer is intentionally omitted in favor of minimal, explicit FFI boundaries.
