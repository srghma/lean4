# Comparison: udp

## Files

- C++ Implementation: `runtime/uv/udp.cpp`
- C++ Header: `runtime/uv/udp.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_libuv.rs` (Initialization/Bindings)

## Overview of C++ Implementation

Provides async UDP socket wrappers via `libuv` (`uv_udp_init`, `uv_udp_bind`, `uv_udp_send`, `uv_udp_recv_start`).

## Corresponding Rust Implementation

Rust provides FFI bindings for UDP in `runtime_libuv.rs` or directly within the Lean definitions. As with TCP, it manages `uv_udp_t` handles.

### Dependencies (Third-party vs Native Rust)

- Uses `libuv`. Rust native `std::net::UdpSocket` or `tokio::net` is an eventual target.
