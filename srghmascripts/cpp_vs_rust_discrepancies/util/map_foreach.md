# Comparison: map_foreach

## Files

- C++ Implementation: `util/map_foreach.cpp`
- C++ Header: `util/map_foreach.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Provides helper functions (`rbmap_foreach`, `phashmap_foreach`, `hashmap_foreach`, `smap_foreach`) that unpack standard Lean map objects via the C API and iterate through their elements, invoking a C++ `std::function` callback for each key-value pair.

## Corresponding Rust Implementation

These iteration functions were ported to C-FFI compliant functions in `src/rust/lean_runtime/src/lib.rs` (e.g., `lean_rbmap_foreach`).

### Dependencies (Third-party vs Native Rust)

- The C++ version took a `std::function<void(b_obj_arg, b_obj_arg)> const & fn` as the callback.
- The Rust version uses a pure C function pointer `cb: LeanMapForeachFn` and an opaque context pointer `ctx: *mut c_void` to achieve the same iteration logic without C++ closure overhead or ABI issues.
