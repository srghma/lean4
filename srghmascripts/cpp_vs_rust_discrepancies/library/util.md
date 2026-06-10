# Comparison: util

## Files

- C++ Implementation: `library/util.cpp`
- C++ Header: `library/util.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A large grab-bag of C++ utility functions for manipulating expressions, inspecting types (e.g., `is_and`, `is_eq`, `is_ite`), and retrieving environment metadata (like the number of constructors for an inductive datatype or its universe levels).

## Corresponding Rust Implementation

Replaced by Lean 4's native `Lean.Expr` utilities, `Lean.Meta` helpers, and native compiler code. The Rust runtime avoids duplicating Lean-level expression manipulation helpers and leaves this completely to Lean.
