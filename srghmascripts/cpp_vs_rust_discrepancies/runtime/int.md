# `runtime/int` (`runtime/int.h`)

## Location of corresponding Rust implementation
No specific Rust file is needed. The `runtime/int.h` file contained C++ typedefs mapping standard integer types (e.g., `int8_t`, `size_t`) to Lean-specific shorter names (`int8`, `usize`, `isize`).

## Discrepancies and issues
Rust has native primitive types for all of these: `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64`, `u64`, `isize`, and `usize`. Therefore, no custom mapping or definitions are required. The codebase natively uses Rust's built-in numeric primitives.
