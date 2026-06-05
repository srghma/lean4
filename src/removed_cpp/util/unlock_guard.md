# Comparison: unlock_guard

## Files

- C++ Header: `util/unlock_guard.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided an `unlock_guard` class that unlocked a mutex upon construction and relocked it upon destruction (the dual of `std::lock_guard`). Useful for temporarily dropping a lock during a long operation or callback.

## Corresponding Rust Implementation

In Rust, locks (e.g. `std::sync::MutexGuard`) can be explicitly dropped using `drop(guard)` and re-acquired later. Rust's ownership model naturally handles these scoping patterns without needing a specialized `unlock_guard`.
