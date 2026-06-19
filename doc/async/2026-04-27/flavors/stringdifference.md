# Lean 4 String and Slice Types Reference

This document outlines the differences between the various string-like types in Lean 4, specifically focusing on how slices and substrings are handled for performance and memory efficiency.

## Summary Table

| Type | Definition/Location | Indexing | Behavior | Best Use Case |
| :--- | :--- | :--- | :--- | :--- |
| `String` | Core | Character | Owned, immutable UTF-8 string. | General purpose text storage. |
| `String.Slice` | `Init.Data.String.Slice` | Byte-based | A view into a `String`. Optimized for searching and iteration. | High-performance parsing, tokenization. |
| `String.Slice.Subslice` | `Init.Data.String.Subslice` | Byte-based | A region relative to another `Slice`. | Tracking nested regions within a token. |
| `Substring.Raw` | `Init.Data.String.Substring` | Byte-based | A lightweight view into a `String` using `String.Pos.Raw`. | Internal Lean parser/compiler logic. |
| ~`Substring`~ | `Init.Data.String.Substring` | Character | High-level UTF-8 aware view of a string. | General application logic needing slices. |

---

## Detailed Breakdown

### 1. `String`
The standard owned string type in Lean. It is a UTF-8 encoded sequence of characters. Operations that return a `String` (like `s.extract`) typically perform a copy.

### 2. `String.Slice` (Modern API)
Defined in `Init.Data.String.Slice`. This is the modern, high-performance replacement for `Substring`.
- **Nature**: A view into a base string.
- **Indexing**: Uses a custom `Pos` type (byte-based).
- **Features**: Includes a rich API for forward/backward pattern matching, splitting, and trimming.
- **Efficiency**: Avoids allocations during slicing; only copies when `toString` (or `copy`) is called.

### 3. `String.Slice.Subslice`
Defined in `Init.Data.String.Subslice`.
- **Nature**: A "slice of a slice". It is indexed relative to its parent `Slice`.
- **Use Case**: Extremely useful when you have already sliced a large file into a "token slice" and now want to identify a "name slice" inside that token without recalculating offsets relative to the start of the whole string.

### 4. `Substring.Raw` (Legacy/Internal API)
Defined in `Init.Data.String.Substring`.
- **Nature**: A simple structure containing the base string and two `String.Pos.Raw` offsets.
- **Indexing**: Strictly byte-based.
- **Status**: Marked as `@deprecated` in newer versions of Lean (see `Init.Data.String.Substring.lean`).
- **Proof of Legacy**: The file `src/Init/Data/String/Substring.lean` contains explicit `@deprecated` attributes on core functions like `Substring.Raw.bsize`, `Substring.Raw.toString`, and `Substring.Raw.isEmpty` (deprecated since "2025-11-16").
- **Reason for Legacy**: `Substring.Raw` is a primitive view. `String.Slice` provides a more robust, iterator-based API that is more ergonomic and integrates better with Lean's pattern matching and search utilities.

### 5. `Substring` (Legacy/High-Level API)
Defined in `Init.Data.String.Substring`.
- **Nature**: A UTF-8 aware wrapper around raw slices.
- **Behavior**: Ensures that slicing operations do not split characters in the middle of a multi-byte sequence.
- **Status**: Now an alias for `Substring.Raw` in many contexts, but conceptually represents the character-aware view.

---

## Comparison: `String.Slice` vs `Substring.Raw`

While both provide views into strings, `String.Slice` is the intended modern API. It provides better integration with Lean's iterator system and a more powerful pattern-matching engine. `Substring.Raw` is a simpler, more "primitive" view.

## Recommendation for Parsers
For implementing a CST/AST parser in Lean 4:
1. Use **`String.Slice`** for the primary input stream.
2. Use **`String.Slice.Subslice`** for nodes in your CST to maintain precise source mapping relative to parent nodes.
3. Avoid `String` concatenation (`++`) entirely; use slice-based `takeWhile`, `drop`, and `split`.
