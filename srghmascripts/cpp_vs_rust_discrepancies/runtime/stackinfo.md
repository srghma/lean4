# Comparison: stackinfo

## Files

- C++ Implementation: `runtime/stackinfo.cpp`
- C++ Header: `runtime/stackinfo.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_stackinfo.rs`

## Overview of C++ Implementation

Retrieves information about the current thread's stack size and available stack space to detect deep recursion before it crashes the process. It uses `pthread_getattr_np` on Linux and `GetThreadContext` on Windows to read the stack bounds, and tracks it against `g_stack_space_main`.

## Corresponding Rust Implementation

This module has been fully ported to Rust in `runtime_stackinfo.rs`. It queries the stack boundaries similarly, utilizing OS-specific APIs via `libc` (e.g. `pthread_getattr_np`) and Windows APIs. It exposes the same API functions like `get_available_stack_size()` to the FFI.

### Dependencies (Third-party vs Native Rust)

- Rust accesses platform APIs natively via the `libc` and `windows-sys` crates instead of C headers.
