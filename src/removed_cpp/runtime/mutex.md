# Comparison: mutex

## Files

- C++ Implementation: `runtime/mutex.cpp`
- C++ Header: `runtime/mutex.h`
- Rust Implementation: `rust/lean_runtime/src/lib.rs` (Initialization)

## Overview of C++ Implementation

Provides an initialization stub (`initialize_mutex` and `finalize_mutex`) for the Lean mutex subsystem. Previously used for C++-level threading primitives and concurrency management within the runtime.

## Corresponding Rust Implementation

Rust handles concurrency via standard library types (`std::sync::Mutex`, `RwLock`) or atomic primitives. Any required global initializers are routed through standard Rust static blocks or explicit init functions. There is no direct file for `mutex` alone, as Rust's thread-safety mechanisms are integrated directly into the `LeanObject` implementations (like multi-threaded refcounting).

### Dependencies (Third-party vs Native Rust)

- Rust uses `std::sync` primitives instead of `std::mutex` from C++.
