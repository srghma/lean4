# Comparison: freset

## Files

- C++ Header: `util/freset.h`
- Rust Implementation: None

## Overview of C++ Implementation

Provides a RAII template class `freset<T>` for "fluid-resets", executing a temporary swap of a variable within a scope and restoring it upon destruction.

## Corresponding Rust Implementation

No direct Rust equivalent was created. Rust generally avoids implicit "fluid-resets" via global or mutable references due to its borrowing rules. When temporary context switching is needed in Rust, it is usually managed via explicit mutable borrows, shadowing, or passing context structures directly.

### Dependencies (Third-party vs Native Rust)

- Relied on C++ RAII semantics and `std::swap`. Not ported.
