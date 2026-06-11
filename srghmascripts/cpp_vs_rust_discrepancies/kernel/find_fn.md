# Comparison: find_fn

## Files

- C++ Header: `kernel/find_fn.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides a templated utility function `find` that recursively searches a Lean expression for a subexpression satisfying a given predicate. It uses `for_each` under the hood and short-circuits the traversal once a matching subexpression is found.

## Corresponding Rust Implementation

There is no direct Rust translation for this utility function. In a native Rust codebase, this would be implemented as a recursive function or iterator over the `LeanObject` expression tree.
