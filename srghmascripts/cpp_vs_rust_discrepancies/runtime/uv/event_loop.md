# Comparison: event_loop

## Files

- C++ Implementation: `runtime/uv/event_loop.cpp`
- C++ Header: `runtime/uv/event_loop.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_event_loop.rs`

## Overview of C++ Implementation

Wraps the `libuv` event loop (`uv_loop_t`) and provides Lean-facing bindings to initialize, start, and manage the asynchronous event loop used by Lean's IO system.

## Corresponding Rust Implementation

Ported to `runtime_event_loop.rs`. The Rust module provides an identical interface to `libuv` via `unsafe` FFI bindings to `uv_loop_init` and `uv_run`. The structure is fundamentally similar, utilizing Rust's `std::ffi` types for bridging instead of C++.

### Dependencies (Third-party vs Native Rust)

- Continues to rely on `libuv` directly through FFI.
