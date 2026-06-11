# Comparison: init_attribute

## Files

- C++ Implementation: `library/init_attribute.cpp`
- C++ Header: `library/init_attribute.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided utility functions to query whether a declaration had the `@[builtinInit]` or `@[init]` attributes, which designated it as an initialization function.

## Corresponding Rust Implementation

Handling of `@[init]` and `@[builtinInit]` attributes is now fully implemented in Lean 4 (`Lean.Compiler.InitAttr`). The runtime doesn't query this attribute directly in C++ anymore, instead initialization hooks are executed by generated code or interpreted during the Lean boot process.
