# Comparison: mpz

## Files

- C++ Implementation: `runtime/mpz.cpp`
- C++ Header: `runtime/mpz.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_object_nat_int.rs`

## Overview of C++ Implementation

Provides a big-integer abstraction (`lean::mpz`) which delegates to GMP (`mpz_t`) if `LEAN_USE_GMP` is defined, or uses a custom fallback implementation based on digits arrays (`mpn_digit`) if GMP is not available. It implements all standard arithmetic operators and provides conversion to and from primitive integer types.

## Corresponding Rust Implementation

In the Rust port (`runtime_object_nat_int.rs`), BigNat and Int values currently still delegate many operations to the C++ GMP/mpz wrappers via `extern "C"` shims (e.g., `lean_alloc_mpz_gmp`, `lean_mpz_add`). A pure-Rust replacement using a native crate (like `num-bigint` or a custom implementation) is planned but currently deferred by FFI shims to `mpz.cpp` or its successor. Certain smaller conversions and size-checking operations have been directly implemented in Rust (`mpz_to_u128` etc.) by inspecting the internal `mpn_digit` arrays directly.

## Discrepancies and Issues

### Memory Model

- `LeanMpzNonGmp` structs are manipulated using Rust pointers directly for small integers, but allocations and complex arithmetic currently route through the FFI.

### Dependencies (Third-party vs Native Rust)

- The C++ version depended heavily on GMP. The Rust port currently depends on GMP (via FFI), but intends to replace this with a native Rust math library for big integers in the future to simplify cross-compilation and remove the C++ dependency.

### Other Issues / How to fix them

- Complete the rewrite of `mpz` into pure Rust to fully eliminate the GMP dependency from the FFI boundary.
