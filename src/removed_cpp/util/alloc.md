# Comparison: alloc

## Files

- C++ Header: `util/alloc.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided macros and C++ template aliases (`lean::allocator`, `lean::unordered_map`) to integrate custom C++ allocators (specifically `mimalloc`) into standard C++ containers. It optimized memory allocations for hash maps and sets across the C++ codebase.

## Corresponding Rust Implementation

Rust handles custom allocators globally at the binary level using the `#[global_allocator]` attribute. In Lean 4's Rust port, memory allocation policies are configured for the entire Rust ecosystem, and the specific per-type `allocator` overrides seen in C++ (`std::allocator` vs `mi_stl_allocator`) are no longer needed. Rust's `std::collections::HashMap` uses the global allocator automatically.
