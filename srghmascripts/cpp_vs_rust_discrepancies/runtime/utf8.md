# Comparison: utf8

## Files

- C++ Implementation: `runtime/utf8.cpp`
- C++ Header: `runtime/utf8.h`
- Rust Implementation: Handled natively by Rust's `std::str` and `String` types, or helper functions in `runtime_object_string.rs`

## Overview of C++ Implementation

Contains manual UTF-8 decoding, encoding, validation, and traversal functions (e.g., `utf8_strlen`, `next_utf8`, `utf8_decode`, `push_unicode_scalar`). Since C++ `std::string` is byte-oriented and has no built-in UTF-8 intelligence, these helpers were necessary for Lean's string operations.

## Corresponding Rust Implementation

Rust has first-class UTF-8 support in its standard library (`&str`, `String`, `char`). Manual validation and length calculation functions were largely replaced by native methods like `.chars().count()`, `.is_char_boundary()`, and `std::str::from_utf8`. For FFI compatibility, specific wrappers mimicking `next_utf8` and `utf8_strlen` may appear in `runtime_object_string.rs`.

### Dependencies (Third-party vs Native Rust)

- Pure native Rust string handling instead of bespoke bit-shifting.
