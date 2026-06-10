# Comparison: dns

## Files

- C++ Implementation: `runtime/uv/dns.cpp`
- C++ Header: `runtime/uv/dns.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_dns.rs`

## Overview of C++ Implementation

Provides asynchronous DNS resolution (`getaddrinfo`) bindings for Lean IO, utilizing `uv_getaddrinfo` from `libuv`.

## Corresponding Rust Implementation

Ported to `runtime_dns.rs`. It replicates the asynchronous DNS queries over `libuv` using `unsafe` blocks. Note that if Lean is built without `libuv`, these operations currently panic in the Rust implementation.

### Dependencies (Third-party vs Native Rust)

- The Rust codebase maintains the dependency on `libuv` for asynchronous DNS. A pure Rust replacement (like `tokio` or `async-std`) would be a significant architectural departure.
