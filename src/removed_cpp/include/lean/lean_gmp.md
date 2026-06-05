# Comparison: lean_gmp.h

## Files

- C++ Header: `include/lean/lean_gmp.h`
- Rust Implementation: `src/rust/lean_runtime/src/runtime_object_nat_int.rs`

## Overview of C++ Implementation

`include/lean/lean_gmp.h` is a small C header that exposes two functions under the `LEAN_USE_GMP` configuration:

1. `lean_alloc_mpz`: Allocates a Lean `mpz` (multiple-precision integer) object from a GMP `mpz_t`.
2. `lean_extract_mpz_value`: Extracts the value from a Lean `mpz` object and populates an existing `mpz_t` structure.
It depends directly on `<gmp.h>`.

## Corresponding Rust Implementation

These exported functions have been ported to Rust in `runtime_object_nat_int.rs`. The functions are exposed as `pub unsafe extern "C" fn lean_alloc_mpz` and `lean_extract_mpz_value`. In Rust, the `mpz_t` type is abstracted as `*mut core::ffi::c_void` in the function signatures so that the Rust side doesn't have to bind directly to `<gmp.h>` structs. They delegate to internal C/C++ shims or `gmp` equivalents (like `lean_extract_mpz_value_gmp`).

## Discrepancies and Issues

### Memory Model

The same object allocation and pointer handling strategies apply. The Rust code safely delegates the copy and extraction to the underlying C shims to ensure the internal GMP representations remain valid.

### Dependencies (Third-party vs Native Rust)

In C++, `<gmp.h>` is directly included. In the Rust port, the `mpz_t` argument is treated as an opaque pointer (`*mut c_void`). This works around needing to compile GMP bindings in Rust, leaving the actual GMP struct layout definitions and manipulations to the C/C++ side (or a `gmp` rust wrapper) when linking.

### Other Issues / How to fix them

- **Opaque Pointers:** The use of `*mut c_void` instead of strongly typed `mpz_t` bindings in Rust loses some type safety, but this is unavoidable without pulling in an FFI binding crate like `gmp-mpfr-sys` or `rug`. It's functional and correct for the `extern "C"` boundary, so no immediate fixes are necessary.
