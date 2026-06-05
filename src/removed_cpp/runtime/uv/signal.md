# Comparison: signal

## Files

- C++ Implementation: `runtime/uv/signal.cpp`
- C++ Header: `runtime/uv/signal.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_signal.rs`

## Overview of C++ Implementation

Integrates OS-level POSIX signal handling (like `SIGINT`, `SIGTERM`) with the `libuv` event loop so Lean programs can respond to interrupts asynchronously without crashing.

## Corresponding Rust Implementation

Ported to `runtime_signal.rs`. It binds `uv_signal_init` and `uv_signal_start` to map OS signals to the Lean event loop.

### Dependencies (Third-party vs Native Rust)

- Relies on `libuv`'s cross-platform signal abstraction.
