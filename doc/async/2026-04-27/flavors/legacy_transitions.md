# Lean 4 Legacy Data Type Transitions

This document tracks the transition of key data types in Lean 4 from legacy implementations to modern, high-performance alternatives.

## Transition: Substring $	o$ String.Slice

### The Legacy Type: `Substring` / `Substring.Raw`
Originally, Lean used `Substring` and `Substring.Raw` to provide views into strings without copying. `Substring.Raw` was a simple triplet of `(String, startPos, stopPos)`.

### The Modern Type: `String.Slice`
`String.Slice` was introduced to provide a more robust and feature-rich API for string manipulation.

### Why it became legacy
`Substring.Raw` was too primitive. It lacked a unified way to handle search patterns, splitting, and iteration efficiently. `String.Slice` introduces:
- **Pattern-based Search**: Generic `startsWith`, `endsWith`, `find?` and `split` that work with `Char`, `String`, or predicates (`Char → Bool`).
- **Iterator Integration**: Slices return iterators rather than allocating intermediate lists, reducing GC pressure.
- **Subslice Support**: The introduction of `Subslice` allows for relative indexing, which is critical for complex parsing.

### Proof of Legacy
The transition is explicitly marked in the source code:
- **`src/Init/Data/String/Substring.lean`**: This file contains numerous `@deprecated` attributes.
- **Example**: `Substring.Raw.bsize` is marked `@deprecated (since := "2025-11-16")`.
- **Explicit Note**: The file header explicitly states: *"This file contains API for `Substring` type, which is a legacy API that will be replaced by the safer variant `String.Slice`."*

---

## General Pattern of Modernization in Lean 4

Lean 4 has shifted from a purely functional, linked-data structure approach toward a more "systems-oriented" approach:

1. **Contiguous Memory**: Shifting from `List` to `Array` for large collections to improve cache locality.
2. **View-based APIs**: Shifting from copying data (e.g., `String.extract`) to returning views (e.g., `String.Slice`).
3. **Iterator-based Processing**: Moving away from producing lists of results in favor of `Std.Iterator`, allowing the consumer to decide how to collect the data.

## Summary for Developers
If you see `Substring` or `Substring.Raw` in older tutorials or documentation, you should almost always replace them with `String.Slice` in new code to ensure compatibility with future Lean 4 versions and to take advantage of the performance improvements.
