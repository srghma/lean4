# Comparison: option_declarations

## Files

- C++ Implementation: `util/option_declarations.cpp`
- C++ Header: `util/option_declarations.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a registry (`option_declarations` map) to declare configuration options (e.g., `trace.compiler`, `pp.all`) with their types, default values, and descriptions. Used the `register_option` macro at initialization.

## Corresponding Rust Implementation

Options and option declarations are natively implemented in Lean 4 (`Lean.OptionDecl`, `Lean.registerOption`). The Rust runtime does not maintain a registry of Lean options, as they are fully managed by the Lean boot and initialization process.
