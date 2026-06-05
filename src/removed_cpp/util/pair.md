# Comparison: pair

## Files

- C++ Header: `util/pair.h`
- Rust Implementation: None

## Overview of C++ Implementation

Provides a simple `lean::pair` alias for `std::pair` and a `lean::mk_pair` wrapper around `std::make_pair`.

## Corresponding Rust Implementation

There is no equivalent file in Rust because Rust natively supports heterogeneous tuples like `(T1, T2)`, which completely replace the need for an explicit `pair` struct.

### Dependencies (Third-party vs Native Rust)

- Rust tuples `(T1, T2)` natively replace `std::pair<T1, T2>`.
