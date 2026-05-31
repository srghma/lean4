# Proposing the EmitEs6 Path

This document analyzes different paths for generating JavaScript (ES6) from Lean 4 code and recommends the most effective approach.

## Recommended Path: LCNF -> JS Source

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> JS Source`

I propose targetting LCNF (specifically the **Impure** phase) for JavaScript emission.

### Comparison of Potential Paths

| Path | Input | Output (Concept) | Pros | Cons |
| :--- | :--- | :--- | :--- | :--- |
| **Path A: Expr -> JS** | `Expr.app (Expr.const Nat.add) [x, 1]` | `lean_nat_add(x, 1)` | Very simple to implement. | No optimizations (inlining, CSE). No handling of join points. |
| **Path B: Decl -> JS** | `LCNF.Decl` | `function f(x) { ... }` | Easier than Code for simple functions. | Lacks context of the full code block for nested optimizations. |
| **Path C: LCNF -> JS** | `LCNF.Code (let ...; case ...; jmp ...)` | `const x1 = ...; switch(...) { ... }` | **Best performance.** Leverages Lean's modern optimizer and handles complex control flow (join points). | Most complex to implement correctly. |

---

## Why LCNF?

1.  **Optimizations**: LCNF is where inlining, common subexpression elimination, and specialization happen. If we emit from `Expr`, we lose all these benefits.
2.  **Control Flow**: LCNF handles "join points" (low-level labels/continuations) which map efficiently to JS structures, but are difficult to handle directly from high-level `Expr`.
3.  **Closures**: LCNF's Lambda Lifting pass already handles closure conversion, meaning we don't have to re-implement it for JavaScript.

---

## Input/Output Examples

### Input Lean Code
```lean
def multiplyAdd (x y z : Nat) : Nat :=
  let result := x * y
  result + z
```

### Path: Expr -> JS
**Input (Expr)**:
```text
(app (app (const Nat.add) (app (app (const Nat.mul) x) y)) z)
```
**Output (JS)**:
```javascript
export function multiplyAdd(x, y, z) {
  return lean_nat_add(lean_nat_mul(x, y), z);
}
```

### Path: LCNF -> JS (Recommended)
**Input (LCNF Code)**:
```text
let _x.1 := Nat.mul x y
let _x.2 := Nat.add _x.1 z
_x.2
```
**Output (JS)**:
```javascript
export function multiplyAdd(x, y, z) {
  const _x_1 = lean_nat_mul(x, y);
  const _x_2 = lean_nat_add(_x_1, z);
  return _x_2;
}
```

## Conclusion

Targetting **LCNF** is the modern and correct way to build a Lean 4 backend. It ensures the generated JavaScript is as optimized as the C++ code while maintaining structural simplicity.
