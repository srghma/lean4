# Lean 4 Array vs List Reference

This document compares `Array` and `List` in Lean 4, explaining when to use each based on performance characteristics and usage patterns.

## Summary Table

| Feature | `List α` | `Array α` |
| :--- | :--- | :--- |
| **Structure** | Singly linked list | Contiguous memory block |
| **Access (Index)** | $O(n)$ | $O(1)$ |
| **Prepending (Cons)** | $O(1)$ | $O(1)$ (Amortized) |
| **Appending** | $O(n)$ | $O(1)$ (Amortized) |
| **Iteration** | Efficient (Recursive) | Efficient (Loop) |
| **Memory Layout** | Fragmented (Nodes) | Compact (Contiguous) |
| **Common Use Case** | Small collections, recursive processing | Large data, random access, buffers |

---

## Detailed Breakdown

### 1. `List α`
A classic functional linked list.
- **Strengths**:
    - Extremely fast prepending (`x :: xs`).
    - Natural fit for recursive functions and pattern matching.
    - Immutable and persistent (sharing tails).
- **Weaknesses**:
    - Random access is slow ($O(n)$).
    - Appending to the end is slow ($O(n)$).
    - Higher memory overhead per element due to pointer nodes.

### 2. `Array α`
A dynamically sized, contiguous array (similar to `std::vector` in C++ or `ArrayList` in Java).
- **Strengths**:
    - Constant time random access ($O(1)$).
    - Very memory efficient (compact layout).
    - Fast appending to the end (amortized $O(1)$).
- **Weaknesses**:
    - Prepending is slow ($O(n)$) as it requires shifting all elements.
    - Less ergonomic for certain recursive patterns compared to `List`.

---

## Decision Matrix: Which one to choose?

| If you need to... | Use `List` | Use `Array` | Why? |
| :--- | :---: | :---: | :--- |
| Access elements by index | | ✅ | Array is $O(1)$, List is $O(n)$. |
| Prepend many elements | ✅ | | List is $O(1)$, Array is $O(n)$. |
| Append to the end | | ✅ | Array is $O(1)$, List is $O(n)$. |
| Process elements recursively | ✅ | | List pattern matching is idiomatic. |
| Store thousands of items | | ✅ | Array has much lower memory overhead. |
| Pass data to C++ / FFI | | ✅ | Array layout is contiguous and compatible. |

## Recommendation for Parsers
In a parser or lexer implementation:
1. Use **`Array`** for the final list of tokens. Since you typically append tokens as you find them, `Array`'s amortized $O(1)$ push is superior to `List`'s $O(n)$ append.
2. Use **`List`** for small, short-lived collections of options or temporary results where recursive processing is the primary goal.
3. If you need to build a list by prepending and then reverse it at the end (a common functional pattern), `List` is appropriate.
