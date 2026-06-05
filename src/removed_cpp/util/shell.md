# Comparison: shell

## Files

- C++ Implementation: `util/shell.cpp`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided the `main` wrapper and `run_shell_main` for the `lean` executable, handling command line arguments (`getopt`), setting up search paths, and invoking `lean_shell_main`. It was essentially the C++ scaffolding for the CLI.

## Corresponding Rust Implementation

Lean 4 has a natively implemented CLI in `src/Lean/Elab/Frontend.lean` and `src/bin/lean.cpp` (or Rust `lean_main`), which parse arguments natively using Lean structures or minimal C code, completely bypassing `util/shell.cpp`.
