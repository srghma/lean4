# Comparison: name_generator

## Files

- C++ Implementation: `util/name_generator.cpp`
- C++ Header: `util/name_generator.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a `name_generator` class to create unique Lean names (`name`) by appending a monotonic counter to a given prefix (like `_fresh.1.2`). It was used throughout the system to generate fresh variables during elaboration, unification, and abstraction.

## Corresponding Rust Implementation

Fresh name generation is now natively implemented in Lean 4 (`Lean.NameGenerator` structure, which holds a `namePrefix` and `idx`). The Rust runtime does not maintain its own name generator since name generation mostly happens in the Lean-level monads (e.g. `CoreM`, `MetaM`).
