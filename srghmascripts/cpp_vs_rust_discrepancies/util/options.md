# Comparison: options

## Files

- C++ Implementation: `util/options.cpp`
- C++ Header: `util/options.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided the `options` class, which was a wrapper around `kvmap` (a key-value map), used to store and pass around configuration flags throughout the C++ codebase (e.g., in the elaborator or tactics).

## Corresponding Rust Implementation

`Options` is implemented natively in Lean 4 (`Lean.Options`) as a wrapper around a `KVMap`. The C++ runtime relies entirely on the Lean implementation of options.
