# Comparison: option_ref

## Files

- C++ Header: `runtime/option_ref.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides a C++ template `option_ref<T>` that wraps a Lean `Option` value. It provides constructors that box an optional value via `mk_cnstr(1, ...)` for `some` and `box(0)` for `none`, as well as accessors like `get()` and `get_val()` that unbox the underlying reference.

## Corresponding Rust Implementation

There is no direct Rust translation for the `option_ref` template. In Rust, standard `Option` mapping over `LeanObject` pointers is used. When interfacing with Lean's C FFI from Rust, optional values are created by instantiating the constructor directly via `lean_runtime_mk_cnstr(1, ...)` or passing `lean_box(0)`.
