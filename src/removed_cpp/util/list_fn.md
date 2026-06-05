# Comparison: list_fn

## Files

- C++ Implementation: `util/list_fn.cpp`
- C++ Header: `util/list_fn.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides common functional operations (`map`, `filter`, `append`, `reverse`, `for_each`) over the `lean::list<T>` type defined in `util/list.h`. These operations were crucial for processing lists within the C++ runtime and compiler.

## Corresponding Rust Implementation

Rust provides these operations natively via `Iterator` traits (`map`, `filter`, `fold`, `collect`, `for_each`) on standard collections (`Vec`, slices). Lean `List`s manipulated at the FFI boundary are handled through recursive destructuring or loops converting them into native Rust `Vec` types.
