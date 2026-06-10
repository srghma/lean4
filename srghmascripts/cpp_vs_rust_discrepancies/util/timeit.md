# Comparison: timeit

## Files

- C++ Implementation: `util/timeit.cpp`
- C++ Header: `util/timeit.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a simple RAII-based timer (`timeit` and `xtimeit`) to measure elapsed time using `std::chrono::steady_clock` and print it out to a stream or call a callback.

## Corresponding Rust Implementation

`timeit` functionality is now handled by the `profileit` runtime primitive (`src/runtime/profileit.cpp` or Rust equivalent) and the Lean 4 standard library methods. It is no longer part of a generic `util` library.
