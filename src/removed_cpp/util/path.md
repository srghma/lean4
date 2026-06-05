# Comparison: path

## Files

- C++ Implementation: `util/path.cpp`
- C++ Header: `util/path.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided standard path manipulation functions (like `dirname`, `stem`, `normalize_path`, `resolve`) and filesystem wrappers (like `is_dir`, `get_mtime`, `read_dir`) with cross-platform handling for Windows, macOS, and Linux. This was heavily used for finding `.lean` source files and resolving imports.

## Corresponding Rust Implementation

Rust handles these exact operations natively and cross-platform via the `std::path::Path`, `std::path::PathBuf`, and `std::fs` standard library modules. The Lean 4 compiler uses standard Rust types or its own internal Lean IO abstractions instead of this legacy C++ filesystem wrapper.

### Dependencies (Third-party vs Native Rust)

- Rust uses `std::fs` and `std::path` natively without manual `#ifdef` branching for Windows vs Linux.
