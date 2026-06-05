# Comparison: string_ref

## Files

- C++ Header: `runtime/string_ref.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides a C++ wrapper class `string_ref` over Lean's C-level string object representation. It inherits from `object_ref` and adds convenience methods like `length()` (number of Unicode scalars), `num_bytes()` (UTF-8 byte length without null terminator), `data()`, and `to_std_string()`.

## Corresponding Rust Implementation

No direct Rust equivalent. The FFI string manipulation and creation is handled by functions like `lean_string_cstr`, `lean_string_len`, and `lean_mk_string` which are bound directly. In safe Rust code, Lean string objects are often manipulated using native Rust `String` or `&str` through conversions.
