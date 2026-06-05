# Comparison: trace

## Files

- C++ Implementation: `kernel/trace.cpp`
- C++ Header: `kernel/trace.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a `lean_trace` macro and tracing classes (`register_trace_class`) used to conditionally print diagnostic messages in C++ when certain trace options (e.g., `set_option trace.compiler true`) were enabled.

## Corresponding Rust Implementation

Tracing is now fully handled in Lean 4 natively (`Lean.trace[foo]` macro, `Lean.MessageLog`). The Rust runtime does not have its own tracing infrastructure linked to Lean options.
