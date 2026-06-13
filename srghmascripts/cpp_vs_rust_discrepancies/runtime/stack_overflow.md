# Comparison: stack_overflow

## Files

- Rust Implementation: `rust/lean_runtime/src/runtime_stack_overflow.rs`

## Overview

The stack overflow handling is now implemented in Rust. On Unix, it sets up an alternate signal stack using `sigaltstack` and catches `SIGSEGV`/`SIGBUS`. It then verifies whether the segfault occurred near the bounds of the current thread's stack limit. On Windows, it uses `AddVectoredExceptionHandler` to catch `EXCEPTION_STACK_OVERFLOW`.

## Corresponding Rust Implementation

This module is implemented in `runtime_stack_overflow.rs`. The Rust code replicates the same logic: on Unix, it relies on `libc` and `sigaction` to set up the alternate signal stack (`sigaltstack`) and trap `SIGSEGV`/`SIGBUS`. On Windows, it binds to `AddVectoredExceptionHandler`.

### Dependencies (Third-party vs Native Rust)

- The Rust port correctly uses the `libc` crate for Unix signals and `winapi`/`windows-sys` for Windows APIs instead of bringing in external complex crash handlers.
