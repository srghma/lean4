# Comparison: system

## Files

- C++ Implementation: `runtime/uv/system.cpp`
- C++ Header: `runtime/uv/system.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_system.rs`

## Overview of C++ Implementation

Exposes system-level operations over `libuv` to Lean, including executing processes (via `uv_spawn`), capturing standard streams (stdin/out/err) through pipes, and querying system environment details.

## Corresponding Rust Implementation

Ported to `runtime_system.rs`. Re-implements `uv_spawn` bindings for `LeanProcess` construction, piping setups, and environment variable lookups.

### Dependencies (Third-party vs Native Rust)

- Rust uses `libuv` through `unsafe` calls. Eventually, `std::process::Command` or `tokio::process` could provide a safer abstraction, but would require large changes.
