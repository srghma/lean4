# Comparison: name_hash_set

## Files

- C++ Header: `util/name_hash_set.h`
- Rust Implementation: None

## Overview of C++ Implementation

Provides a type alias `name_hash_set` for `lean::unordered_set<name, name_hash_fn, name_eq_fn>`, binding the custom `name_hash_fn` and `name_eq_fn` hash/equality operators to a standard C++ unordered set.

## Corresponding Rust Implementation

There is no explicit equivalent file in Rust because Rust's `std::collections::HashSet` natively infers the `Hash` and `Eq` traits of its key type. A set of Lean names is simply declared as `HashSet<Name>` when using standard Rust wrappers, negating the need for custom typedefs.

### Dependencies (Third-party vs Native Rust)

- Rust natively handles trait inference for hashing via `std::collections::HashMap` and `std::collections::HashSet`.
