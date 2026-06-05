# Comparison: tcp

## Files

- C++ Implementation: `runtime/uv/tcp.cpp`
- C++ Header: `runtime/uv/tcp.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_libuv.rs` (Initialization/Bindings)

## Overview of C++ Implementation

Provides async TCP socket wrappers via `libuv` (`uv_tcp_init`, `uv_tcp_bind`, `uv_listen`, `uv_accept`).

## Corresponding Rust Implementation

Rust has FFI bindings defined for TCP, likely in `runtime_libuv.rs` or directly within the Lean definitions. Uses raw pointers to `uv_tcp_t`.

### Dependencies (Third-party vs Native Rust)

- Uses `libuv`. Rust native `std::net::TcpStream` or `tokio::net` is an eventual target.
