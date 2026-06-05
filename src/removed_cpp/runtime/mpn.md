# `runtime/mpn` (`runtime/mpn.h` and `runtime/mpn.cpp`)

## Location of corresponding Rust implementation
The custom multi-precision natural numbers implementation is ported directly to Rust in `src/rust/lean_runtime/src/runtime_mpn.rs`.
Additionally, `src/rust/lean_runtime/src/runtime_mpz.rs` provides the higher-level integer wrapper.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ implementation was a hand-rolled BigInt library (implementing Knuth's algorithms) used as a fallback when the GMP library was not available. The Rust port in `runtime_mpn.rs` is essentially a 1:1 translation of these C++ functions (`mpn_add`, `mpn_sub`, `mpn_mul`, `mpn_div`, `mpn_to_string`), preserving the same math logic and using Rust slices/Vecs for memory safety instead of raw pointers where internal allocations occur.
- **Memory Model**: The original C++ functions used `lean::buffer` and raw pointers, while `runtime_mpn.rs` uses `Vec<MpnDigit>` internally for intermediate computations. To preserve the C ABI, `runtime_mpn.rs` exposes functions like `mpn_add` that take `*const MpnDigit` and `*mut MpnDigit`, internally slicing them via `core::slice::from_raw_parts`.
- **Third-party alternatives**: The Lean runtime supports an optional GMP path. In the Rust port, this is controlled by the `#[cfg(lean_use_gmp)]` flag in `runtime_mpz.rs` which directly links to GMP's `__gmpz_*` C APIs. When this flag is unset, the custom `runtime_mpn.rs` functions are used. In a pure Rust idiom, relying on native cargo crates like `num-bigint` might be more maintainable long-term than maintaining a hand-rolled C-ABI fallback, but the current port strictly retains the existing C++ semantics and binary interface.
