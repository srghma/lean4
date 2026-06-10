# Comparison: interrupt

## Files

- C++ Implementation: `runtime/interrupt.cpp`
- C++ Header: `runtime/interrupt.h`
- Rust Implementation: `rust/lean_runtime/src/runtime_interrupt.rs`

## Overview of C++ Implementation

Implements heartbeats (instruction limits), thread-local max heartbeats, and interruption using `CancelToken`s. It exposes functions to increment heartbeats, check limits (`check_heartbeat`), check for user cancellation (`check_interrupted`), and check all system constraints at once (`check_system`).

## Corresponding Rust Implementation

This module has been fully ported to Rust in `runtime_interrupt.rs`. The Rust version exposes the same functionality (`lean_internal_set_max_heartbeat`, `check_system`, etc.) over FFI. It utilizes thread-local storage (`thread_local!`) in Rust to replace the `LEAN_THREAD_VALUE` macros for tracking heartbeats and the cancel token.
