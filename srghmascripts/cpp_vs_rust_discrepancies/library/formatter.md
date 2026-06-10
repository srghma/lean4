# Comparison: formatter

## Files

- C++ Implementation: `library/formatter.cpp`
- C++ Header: `library/formatter.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provided a hook for pretty-printing Lean expressions to C++ standard output streams (`std::ostream`). It was heavily used for debugging expressions from C++.

## Corresponding Rust Implementation

No direct Rust FFI equivalent. Pretty printing of `Expr` is implemented in Lean 4 itself (`Lean.Meta.ppExpr`). For low-level runtime debugging in Rust, `Expr` objects can be dumped using internal basic formatting (often via `lean_object_to_string` or Lean-level toString implementations), but the elaborate formatting environment configuration (`options`, `formatter`) is pure Lean.
