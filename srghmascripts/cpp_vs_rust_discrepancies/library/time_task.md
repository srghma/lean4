# Comparison: time_task

## Files

- C++ Implementation: `library/time_task.cpp`
- C++ Header: `library/time_task.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a `time_task` class which used `xtimeit` to measure the execution time of tasks (like elaboration or type checking), and report it to the cumulative profiler (`display_cumulative_profiling_times`).

## Corresponding Rust Implementation

Replaced by Lean 4's native `profileit` and tracing mechanisms (`Lean.profileitM` / `Lean.profileit`). The Rust runtime implements the low-level `lean_profileit` timer natively, but the logic aggregating the timing data is largely in Lean.
