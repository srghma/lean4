# Comparison: annotation

## Files

- C++ Implementation: `library/annotation.cpp`
- C++ Header: `library/annotation.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a mechanism to wrap expressions with "annotations" (like `have`, `show`, `suffices`) that had no semantic meaning to the type checker but guided the pretty printer or automation tactics. It was implemented using macro expressions under the hood.

## Corresponding Rust Implementation

Expression annotations are completely redefined in Lean 4 natively as `mdata` expressions (metadata attached to expressions) or native syntax node wrappers. There is no Rust FFI stub for these old `annotation` macros.
