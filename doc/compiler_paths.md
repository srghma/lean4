# Lean 4 Compilation Paths

This document explains the standard compilation paths in Lean 4, the datatypes used at each stage, and the reasons for each transformation.

## 1. Standard Path (The Heavy-Duty Optimizer)

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> IR -> LLVM IR -> Machine Code`

### Stage Breakdown

| Stage | Datatype | Why |
| :--- | :--- | :--- |
| **Source** | `.lean` File | Human-readable Lean code. |
| **Expr** | `Lean.Expr` | High-level, dependently typed abstract syntax tree. Represents full mathematical intent. |
| **Decl** | `Lean.Compiler.LCNF.Decl` | LCNF declaration. Strips mathematical details not needed for computation. |
| **Code (LCNF)** | `Lean.Compiler.LCNF.Code` | A-normal form (ANF). Makes control flow and intermediate values explicit. Ideal for inlining, CSE, and specialization. |
| **IR** | `Lean.IR.Decl` | Low-level IR. Adds explicit reference counting (`inc`/`dec`) and unboxing for scalar types. |
| **LLVM IR** | `String/Bitcode` | Standard representation for industrial-strength optimizations and machine code generation via LLVM. |

### Example Transformation

**Source**:
```lean
def f (x : Nat) : Nat := x + 1
```

**LCNF Code (simplified)**:
```lean
def f (x : Nat) : Nat :=
  let _x.1 := 1
  let _x.2 := Nat.add x _x.1
  _x.2
```

**IR (simplified)**:
```lean
def f (x : obj) : obj :=
  let x_1 := 1
  let x_2 := Nat.add x x_1
  inc x_2
  dec x
  ret x_2
```

---

## 2. Current C++ Path (The Runtime-Based Path)

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> C++ Source`

This is the default path for generating executables and shared libraries that link against the Lean runtime (`liblean`).

### Stage Breakdown

| Stage | Datatype | Why |
| :--- | :--- | :--- |
| **Source/Expr/Decl** | Same as above. | - |
| **Code (LCNF)** | `Lean.Compiler.LCNF.Code` | Specifically after the **Impure** phase, where side effects and RC operations are conceptually ready for lowering. |
| **C++ Source** | `String (.cpp)` | Human-readable (but mangled) C++ code that calls Lean runtime functions. |

### Why C++?
- **Interoperability**: Easy to call C/C++ from Lean and vice-versa.
- **Portability**: Leverages existing C++ compilers (GCC, Clang, MSVC) for the final machine code step.
- **Runtime Integration**: The Lean runtime is written in C++, so direct emission simplifies the interface.

### Example (C++ Output concept)
```cpp
lean_object* l_f(lean_object* x) {
    lean_object* x_1 = lean_int64_to_int(1);
    lean_object* x_2 = lean_nat_add(x, x_1);
    lean_dec(x);
    return x_2;
}
```
