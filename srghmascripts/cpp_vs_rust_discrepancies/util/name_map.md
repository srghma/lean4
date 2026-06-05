# Comparison: name_map

## Files

- C++ Header: `util/name_map.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A simple type alias (`template<typename T> using name_map = rb_map<name, T, name_quick_cmp>;`) for an `rb_map` using Lean `name`s as keys.

## Corresponding Rust Implementation

Replaced natively in Lean 4 by `Std.RBMap Name T Name.quickCmp` or similar (`NameMap` structure). The Rust runtime has no direct analogue.
