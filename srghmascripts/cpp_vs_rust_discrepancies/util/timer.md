# Comparison: timer

## Files

- C++ Implementation: `util/timer.cpp`
- C++ Header: `util/timer.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a `single_timer` class, which was a background thread utility used to execute a callback after a certain timeout. Used to implement timeouts for tasks (e.g. `set_option timeout 100`).

## Corresponding Rust Implementation

Timeouts and tasks are now handled by Lean 4's native `Task` system and runtime `lean_task` implementation (e.g., `Heartbeat` limits instead of strict time limits, to ensure determinism). The `timer.cpp` utility was dropped.
