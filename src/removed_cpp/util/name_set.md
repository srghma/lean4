# Comparison: name_set

## Files

- C++ Implementation: `util/name_set.cpp`
- C++ Header: `util/name_set.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A simple type alias (`typedef rb_tree<name, name_quick_cmp> name_set;`) for a red-black tree storing Lean `name`s, along with a few utility functions like `mk_unique` to generate a name not present in the set.

## Corresponding Rust Implementation

`NameSet` is now implemented natively in Lean 4 (`Std.RBTree Name Name.quickCmp` or similar functional structures). The Rust runtime does not use this structure.
