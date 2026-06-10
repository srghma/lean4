# Comparison: io

## Files

- C++ Implementation: `runtime/io.cpp`
- C++ Header: `runtime/io.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_io.rs`

## Overview of C++ Implementation

Contains core I/O utilities for the Lean runtime, such as wrapping standard C `FILE*` handles into Lean objects (`io_wrap_handle`) and constructing `IO.Error` variants (`io_result_mk_ok`, `io_result_mk_error`, `decode_io_error`). It bridges the gap between C/OS error codes and the Lean `IO` monad representations.

## Corresponding Rust Implementation

Ported to `rust/lean_runtime/src/runtime_io.rs`. The Rust module duplicates this logic, constructing the equivalent `IO.Error` representations for OS-level and `libuv` errors using Rust's `std::io::Error` and `libc` codes. Rust's `String` conversions natively handle the error message constructions.

### Dependencies (Third-party vs Native Rust)

- Rust uses `std::io::Error::last_os_error()` instead of reading `errno` directly from C.
