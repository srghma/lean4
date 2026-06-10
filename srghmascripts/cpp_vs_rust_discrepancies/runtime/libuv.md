# Comparison: libuv

## Files

- C++ Implementation: `runtime/libuv.cpp`
- C++ Header: `runtime/libuv.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_libuv.rs`

## Overview of C++ Implementation

A global initialization and finalization file for all `libuv` modules. It registers classes (e.g., handles for streams, timers) and initializes submodules in `runtime/uv/`.

## Corresponding Rust Implementation

Ported to `runtime_libuv.rs`. Contains `initialize_libuv()` which calls the Rust-mapped initializers for the event loop, timers, signals, network types, and system processes.
