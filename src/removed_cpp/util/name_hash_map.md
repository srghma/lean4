# Comparison: name_hash_map

## Files

- C++ Header: `util/name_hash_map.h`
- Rust Implementation: None

## Overview of C++ Implementation

Provides a type alias `name_hash_map<T>` for `lean::unordered_map<name, T, name_hash_fn, name_eq_fn>`, binding the custom `name_hash_fn` and `name_eq_fn` hash/equality operators to a standard C++ unordered map.

## Corresponding Rust Implementation

There is no explicit equivalent file in Rust because Rust's `std::collections::HashMap` natively infers the `Hash` and `Eq` traits of its key type. A map of Lean names is simply declared as `HashMap<Name, T>` when using standard Rust wrappers, negating the need for custom typedefs.

### Dependencies (Third-party vs Native Rust)

- Rust natively handles trait inference for hashing via `std::collections::HashMap` and `std::collections::HashSet`.
