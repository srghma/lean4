# Comparison: net_addr

## Files

- C++ Implementation: `runtime/uv/net_addr.cpp`
- C++ Header: `runtime/uv/net_addr.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_net_addr.rs`

## Overview of C++ Implementation

Provides translation between Lean's network address representations and C/POSIX `sockaddr_in` and `sockaddr_in6` structs used by `libuv`.

## Corresponding Rust Implementation

Ported to `runtime_net_addr.rs`. Uses Rust's standard `libc` interop to map Lean objects to `sockaddr` types. The implementation achieves identical results by reading IP strings and port numbers and using FFI utilities (`uv_ip4_addr` and `uv_ip6_addr`).
