# Comparison: util/io

## Files

- C++ Header: `util/io.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Provides C++ helper template functions (`get_io_result`, `consume_io_result`, and `get_io_scalar_result`) for safely calling Lean IO functions from C++ code. If the returned `io_result` contains an error, they extract the error string and throw a C++ `lean::exception`.

## Corresponding Rust Implementation

`consume_io_result` was manually ported directly into `src/rust/lean_runtime/src/lib.rs` (around line 1674). The templated versions (`get_io_result`, `get_io_scalar_result`) were omitted as they are not needed by the Rust bootstrap sequence.

## Discrepancies and Issues

### Memory Model

- **Exception Handling**: Because Rust does not use C++ exceptions, the Rust port of `consume_io_result` unwraps the IO error and prints it to stderr via direct `write` syscalls, then unconditionally calls `abort()` to crash the process, rather than throwing an exception.

### Dependencies (Third-party vs Native Rust)

- Replaces C++ `throw exception(...)` with process termination (`abort()`).

. The `consume_io_result` is strictly used during initialization in Rust, so aborting on failure is the intended design for fatal initialization errors.
