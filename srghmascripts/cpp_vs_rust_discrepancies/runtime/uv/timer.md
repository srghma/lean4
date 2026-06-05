# Comparison: timer

## Files

- C++ Implementation: `runtime/uv/timer.cpp`
- C++ Header: `runtime/uv/timer.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_timer.rs`

## Overview of C++ Implementation

Provides an asynchronous timer interface over `libuv` (`uv_timer_init`, `uv_timer_start`, `uv_timer_stop`). This is primarily used for asynchronous `IO.sleep`.

## Corresponding Rust Implementation

Ported to `runtime_timer.rs`. Implements the exact same abstractions for initializing and managing timers in the `libuv` event loop through `unsafe` Rust.
