# Comparison: constants

## Files

- C++ Implementation: `library/constants.cpp`
- C++ Header: `library/constants.h`
- Rust Implementation: `src/rust/lean_runtime/src/library_constants.rs`

## Overview of C++ Implementation

Auto-generated files (via `scripts/gen_constants_cpp.py`) that declare and initialize global persistent Lean `name` objects for commonly used constants (like `And`, `Nat`, `Eq`). These are accessed through C++ getter functions like `get_absurd_name()`.

## Corresponding Rust Implementation

The Rust implementation in `library_constants.rs` mimics this behavior using a macro `library_constant_getter!`. The macro defines an array of global uninitialized pointers for the constants and generates FFI exported getter functions with identical C++ mangled names (e.g., `_ZN4lean15get_absurd_nameEv`) to ensure compatibility with compiled object files expecting the C++ symbols. It also implements an initialization function `initialize_constants` that constructs all the string names at runtime and marks them as persistent, exactly like the C++ version.

## Discrepancies and Issues

### Memory Model

- **Initialization**: Rust manages an array of raw mutable static pointers (`const mut *LeanObject`) which are populated during the single-threaded initialization phase via `lean_name_mk_string`, safely bypassing Rust's strict mutability constraints for globals.

### Dependencies (Third-party vs Native Rust)

- Rust uses an elegant macro `library_constant_getter!` to abstract away the boilerplate that the C++ version auto-generated via Python script.
