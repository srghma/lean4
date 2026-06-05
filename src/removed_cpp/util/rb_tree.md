# Comparison: rb_tree

## Files

- C++ Header: `util/rb_tree.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Implemented a generic, persistent (immutable), reference-counted Left-Leaning Red-Black Tree in C++. It used `lean_object` style `MK_LEAN_RC()` reference counting for thread-safe structural sharing and O(1) copying.

## Corresponding Rust Implementation

No direct Rust port. Purely functional red-black trees are implemented in native Lean 4 (`Std.RBTree`, `Std.RBMap`) instead. The Rust runtime only occasionally interfaces with functional data structures if it needs to inspect them, but the tree manipulation algorithms live in Lean.
