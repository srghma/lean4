# Lean 4 Position Types Reference

This document explains the different ways of representing positions within strings in Lean 4, contrasting raw byte offsets with high-level character positions.

## Summary Table

| Type | Location | Nature | Behavior | Best Use Case |
| :--- | :--- | :--- | :--- | :--- |
| `String.Pos.Raw` | `Init.Data.String.PosRaw` | Byte Offset | A simple wrapper around a `Nat` representing the byte index. | Low-level slicing, internal parser offsets. |
| `s.Pos` (from `Slice`) | `Init.Data.String.Slice` | Contextual | A position relative to a specific `Slice` `s`. | High-level slicing within a specific `String.Slice`. |
| `Char` Index | Core | Character | Indexing by Unicode code point. | General purpose string indexing. |

---

## Detailed Breakdown

### 1. `String.Pos.Raw`
Defined in `src/Init/Data/String/PosRaw.lean`.
- **Nature**: It is the most primitive representation of a position. It is essentially a `Nat` wrapped in a structure for type safety.
- **Logic**: `0` is the start of the string. `s.rawEndPos` is the end.
- **Operations**: 
    - `inc` / `dec`: Move by exactly 1 byte.
    - `next` / `prev`: Move by one UTF-8 character (requires the base string to calculate byte size).
- **Warning**: Because it is byte-based, you cannot simply add `1` to move to the next character unless the character is 1-byte (ASCII). Always use `.next` or `+ Char` for character movement.

### 2. `s.Pos` (Slice Position)
Used extensively in `String.Slice` (defined in `Init.Data.String.Slice`).
- **Nature**: Instead of being a global offset, `s.Pos` is a position that is logically bound to a specific slice `s`.
- **Benefit**: This prevents "position leakage" where you accidentally use a position from one string/slice to index into another. It provides a layer of type safety that ensures the position is valid for the slice it is being used with.
- **Conversion**: Can be converted to/from `String.Pos.Raw` via `.offset`.

---

## Comparison: Byte-based vs Character-based

| Operation | Byte-based (`Pos.Raw`) | Character-based (Standard indexing) |
| :--- | :--- | :--- |
| **Speed** | $O(1)$ to jump/slice | $O(N)$ to find the $N$-th character |
| **Precision** | Exact byte alignment | Logical character alignment |
| **Risk** | Can split a UTF-8 character | Always safe |

## Recommendation for Parsers
When building a lexer or parser:
1. Use **`String.Pos.Raw`** for the absolute indices of your tokens (e.g., `startPos` and `stopPos`).
2. Use **`s.Pos`** when performing local searches or splits within a `String.Slice`.
3. Never manually increment a position by `1` unless you are specifically dealing with ASCII bytes; always use the provided `next`/`prev` utilities to maintain UTF-8 integrity.
