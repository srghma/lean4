# Lean 4 Compilation Stages: A Concrete Example

This document traces the transformation of a simple Lean function through the various stages of the Lean 4 compiler.

## Source Code

```lean
def squareAdd (x y : Nat) : Nat :=
  let s := x * x
  s + y
```

---

## 1. Frontend Stage
**Datatype**: `Lean.Expr`
**Module**: Front-end parser and elaborator.

The high-level AST represents the fully typed, dependently typed expression.

```text
Expr.lam `x (const `Nat) (
  Expr.lam `y (const `Nat) (
    Expr.letE `s (const `Nat)
      (app (app (const `Nat.mul) (fvar `x)) (fvar `x))
      (app (app (const `Nat.add) (fvar `s)) (fvar `y))
  )
)
```

---

## 2. LCNF Base Phase
**Datatype**: `Lean.Compiler.LCNF.Decl` (with `Purity.pure`)
**Module**: `Lean.Compiler.LCNF.ToLCNF`

The code is converted to **A-normal form (ANF)**. Every intermediate application is bound to a `let` declaration.

```text
def squareAdd (x : Nat) (y : Nat) : Nat :=
  let _x.1 := Nat.mul x x
  let _x.2 := Nat.add _x.1 y
  _x.2
```

---

## 3. LCNF Optimization (Simp)
**Datatype**: `Lean.Compiler.LCNF.Decl`
**Module**: `Lean.Compiler.LCNF.Simp`

The simplifier performs inlining and constant folding. If `Nat.mul` or `Nat.add` were small inlineable functions, they would be expanded here. For primitive `Nat` ops, it usually remains in ANF but may consolidate variables.

---

## 4. LCNF Mono Phase (Monomorphization)
**Datatype**: `Lean.Compiler.LCNF.Decl`
**Module**: `Lean.Compiler.LCNF.ToMono`

If our function used polymorphism (e.g., `List α`), this phase would create specialized versions for concrete types like `Nat`. For our `squareAdd`, it stays largely the same but types are prepared for the backend.

---

## 5. LCNF Impure Phase
**Datatype**: `Lean.Compiler.LCNF.Decl` (with `Purity.impure`)
**Module**: `Lean.Compiler.LCNF.ToImpure`

This phase marks the transition where side effects and reference counting become relevant. It also handles **Boxing/Unboxing** via `Lean.Compiler.LCNF.ExplicitBoxing`.

**Example (Conceptual after Boxing)**:
If `Nat` is treated as an object:
```text
def squareAdd (x : Nat) (y : Nat) : Nat :=
  let _x.1 := Nat.mul x x
  let _x.2 := Nat.add _x.1 y
  return _x.2
```

---

## 6. Low-Level IR Phase
**Datatype**: `Lean.IR.Decl`
**Module**: `Lean.Compiler.IR.ToIR`

The code is lowered to a representation with explicit reference counting (`inc`/`dec`) and specialized types (`obj`, `u64`, etc.).

```text
fdecl squareAdd (x : obj) (y : obj) : obj :=
  let x_1 := Nat.mul x x;
  let x_2 := Nat.add x_1 y;
  inc x_2;
  dec x;
  dec y;
  dec x_1;
  ret x_2
```

---

## 7. Code Generation (C++ or LLVM)
**Datatype**: `String`
**Module**: `Lean.Compiler.LCNF.EmitC` or `Lean.Compiler.IR.EmitLLVM`

Final conversion to target source code.

**C++ Output (Simplified)**:
```cpp
lean_object* l_squareAdd(lean_object* x, lean_object* y) {
    lean_object* x_1 = lean_nat_mul(x, x);
    lean_object* x_2 = lean_nat_add(x_1, y);
    lean_inc(x_2);
    lean_dec(x);
    lean_dec(y);
    lean_dec(x_1);
    return x_2;
}
```
