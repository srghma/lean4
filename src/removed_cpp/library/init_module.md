# Comparison: library/init_module

## Files

- C++ Implementation: `library/init_module.cpp`
- C++ Header: `library/init_module.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided initialization routines (`initialize_library_module`) for all the C++ components in the `library` directory (e.g. `initialize_print`, `initialize_num`, `initialize_profiling`).

## Corresponding Rust Implementation

Rust does not have a monolithic initialization module for these libraries because most of them were completely ported to Lean 4 or no longer require initialization.
