# Comparison: pair_ref

## Files

- C++ Header: `runtime/pair_ref.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides a C++ template `pair_ref<T1, T2>` that wraps a Lean `Prod` (pair) value. It simplifies creating pairs using `mk_cnstr(0, a, b)` and extracting values with `fst()` and `snd()`.

## Corresponding Rust Implementation

There is no direct Rust translation for the `pair_ref` template. In the Rust port, Lean pairs are handled directly by allocating an object with `lean_runtime_mk_cnstr(0, 2, ...)` or by defining simple structs to manipulate the C FFI fields natively.
