# `runtime/hash` (`runtime/hash.h` and `runtime/hash.cpp`)

## Location of corresponding Rust implementation
The implementation corresponds to the Rust file `src/rust/lean_runtime/src/lib.rs` (specifically the function `lean_runtime_hash_str`).

## Discrepancies and issues
- **Algorithm**: The C++ code implements MurmurHash64A by Austin Appleby. The Rust code implements the exact same MurmurHash64A algorithm inline (`lean_runtime_hash_str`), ensuring that strings hash to identical values between C++ and Rust code without relying on an external dependency crate. 
- **Types**: The generic `hash` function defined in `runtime/hash.h` is likely folded into the Rust runtime or not needed as a standalone export.
- There are no major discrepancies in memory model or behavior. The Rust code handles the unaligned byte reads and trailing byte logic explicitly using standard Rust `u64` masking and bit shifts, mirroring the C++ switch statement implementation.
