# Comparison: list

## Files

- C++ Header: `util/list.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a templated C++ singly-linked list (`lean::list<T>`) modeled on immutable functional programming paradigms. It implemented cons cells with an invasive atomic reference counter (`MK_LEAN_RC`) for sharing tails, avoiding the need for deep copies when destructuring or prepending.

## Corresponding Rust Implementation

Rust does not recreate an invasive functional list primitive in its runtime. Standard Rust uses `Vec<T>` for dynamic arrays. In places where purely functional immutable lists are required, they are represented natively as Lean objects (via the FFI constructor for `List`) rather than using a C++ or Rust-native generic wrapper inside the runtime layer.
