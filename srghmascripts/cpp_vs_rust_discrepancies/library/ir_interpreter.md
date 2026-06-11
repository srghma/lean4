# Comparison: ir_interpreter

## Files

- C++ Implementation: `library/ir_interpreter.cpp`
- C++ Header: `library/ir_interpreter.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a minimal C++ interpreter for the Lean compiler's intermediate representation (`ir`). It was mainly used to run compiled Lean code (`run_boxed` or `run_main`) directly from the C++ environment before fully compiling to native C code.

## Corresponding Rust Implementation

Lean code is now either interpreted using the native Lean interpreter (`Lean.Meta.evalExpr` or compiled bytecode execution) or compiled to C/LLVM. The Rust runtime does not include an IR interpreter. Execution of `main` is handled in `lean_runtime` (like `lean_run_main`).
