# Comparison: profiling

## Files

- C++ Implementation: `library/profiling.cpp`
- C++ Header: `library/profiling.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided utilities for profiling in the C++ runtime, checking `profiler` and `profiler.threshold` options to determine if operations (like elaboration) should be timed and logged.

## Corresponding Rust Implementation

Profiling is now completely implemented natively in Lean 4 via `Lean.profileit` (which has a lightweight primitive `profileitImpl` in the C++ runtime `src/runtime/profileit.cpp` and soon to be Rust). The high-level profiling options and logic in `library/profiling` are handled natively in Lean 4.
