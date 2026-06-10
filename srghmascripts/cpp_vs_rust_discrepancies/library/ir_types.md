# Comparison: ir_types

## Files

- C++ Header: `library/ir_types.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided C++ type aliases (`var_id`, `jp_id`, `fun_id`, `arg`, `expr`, `param`, etc.) and an enum `type` corresponding to Lean's intermediate representation (IR) used by the compiler.

## Corresponding Rust Implementation

The compiler IR and its types (`IRType`, `Decl`, `FnBody`, `Alt`, etc.) are natively implemented in Lean 4 (`Lean.Compiler.IR`). The Rust runtime interacts with compiler artifacts directly without needing an IR representation.
