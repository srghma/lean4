# Lean 4 Compiler Architecture

This document provides a comprehensive overview of the Lean 4 compiler's internal structure, its intermediate representations, and the code generation paths.

## Compiler File Graph

All files are located under `src/Lean/Compiler`.

### Core Structure

```text
src/Lean/Compiler/
├── LCNF/                   # Lean Compiler Normal Form (Modern IR)
│   ├── Simp/               # LCNF Simplifier (Optimization engine)
│   ├── Basic.lean          # Core LCNF data structures (Code, Decl, LetDecl, Param)
│   ├── EmitC.lean          # Modern C++ code generator
│   ├── Main.lean           # LCNF driver and pass management
│   ├── Passes.lean         # The actual pipeline (Base -> Mono -> Impure)
│   └── ...                 # See "LCNF Modules" for details
├── IR/                     # Low-level IR (Explicit RC and Unboxing)
│   ├── Basic.lean          # IR data structures (inductive IRType, Decl, etc.)
│   ├── EmitLLVM.lean       # LLVM bitcode generation
│   └── ToIR.lean           # Conversion from LCNF to IR
├── Main.lean               # Overall entry point for the compiler
├── IR.lean                 # Entry point for the IR module
└── LCNF.lean               # Entry point for the LCNF module
```

### LCNF Modules

The `src/Lean/Compiler/LCNF` directory contains over 70 modules. Key modules include:

- **Analysis & Utilities**: `AlphaEqv`, `Check`, `CompilerM`, `FVarUtil`, `InferType`, `LCtx`, `LiveVars`, `PrettyPrinter`, `Types`.
- **Transformations**:
  - `CSE`: Common Subexpression Elimination.
  - `ElimDead`: Dead code elimination.
  - `LambdaLifting`: Flattens nested functions.
  - `Monomorphization`: `ToMono`, `MonoTypes`.
  - `Simp`: The main optimization engine (`Simp/`, `SimpCase`).
  - `Specialization`: `Specialize`, `SpecInfo`.
- **Lowering & Emission**:
  - `ToImpure`, `ToImpureType`: Prepares LCNF for code generation by making side effects explicit.
  - `EmitC`, `EmitUtil`: Generates C++ code.
- **Structural**: `Bind`, `Closure`, `JoinPoints`, `PullLetDecls`, `PushProj`.

### Module Roles

- **LCNF (Lean Compiler Normal Form)**: The modern heart of the compiler. It uses an A-normal form to make every intermediate value explicit, which is crucial for optimizations like inlining and CSE.
- **Simp**: A highly iterative pass that repeatedly applies local transformations to shrink and speed up the code.
- **Monomorphization (`ToMono`)**: Replaces polymorphic functions with specialized versions for concrete types (e.g., `List α` -> `List Nat`).
- **Lambda Lifting**: Flattens nested functions, turning them into top-level declarations and explicitly passing captured variables.
- **IR**: The final stop before machine code or LLVM. It adds low-level details like `inc`/`dec` for reference counting.

---

## Compilation Paths

### 1. Standard Path (The Heavy-Duty Optimizer)

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> IR -> LLVM IR -> Machine Code`

This path is designed for maximum performance, leveraging LLVM's optimization passes.

### 2. C++ Path (Runtime-Based)

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> C++ Source`

This is the most common path. It translates LCNF (after the `impure` phase) directly into C++ code that calls the Lean runtime.

### Datatype Transformations and Examples

| Phase | Datatype | Why | Example (Conceptual) |
| :--- | :--- | :--- | :--- |
| **Front-end** | `Expr` | High-level, dependently typed. | `fun x => x + 1` |
| **LCNF** | `LCNF.Code` | Flat structure (ANF), easy to optimize. | `let _x.1 := 1; let _x.2 := Nat.add x _x.1; _x.2` |
| **IR** | `IR.Decl` | Low-level, explicit RC and unboxing. | `inc x; let y := unbox(x) + 1; ret box(y)` |
| **Output** | `String` | Source code for C++ or JS. | `lean_object* f(lean_object* x) { ... }` |

---

## Proposal: `EmitEs6` (JavaScript Backend)

To implement a JavaScript backend, I recommend the following path:
**`Source -> Expr -> Decl -> Code (LCNF) -> JS Source`**

### Path Options for JS

1. **`Expr -> JS`**:
   - **Pros**: Easy to write.
   - **Cons**: No optimizations. Closures and join points are hard to handle. Very slow.
2. **`LCNF -> JS`** (Recommended):
   - **Pros**: Leverages all of Lean's modern optimizations (inlining, CSE, lambda lifting). LCNF structure maps naturally to JS `const` bindings.
   - **Cons**: Requires handling the LCNF `Code` tree.
3. **`IR -> JS`**:
   - **Pros**: Very low level.
   - **Cons**: Reference counting is unnecessary in JS (which has its own GC). Unboxing logic is complex to map to JS.

### JS Example (from LCNF)

**Input LCNF**:

```lean
def myFun (x : Nat) : Nat :=
  let _x.1 := 1
  let _x.2 := Nat.add x _x.1
  _x.2
```

**Output JS**:

```javascript
export function myFun(x) {
  const _x_1 = 1n;
  const _x_2 = lean_nat_add(x, _x_1);
  return _x_2;
}
```

---

## Learning and Implementation Plan for `EmitEs6`

### 1. Learning Plan

- **LCNF Structures**: Study `src/Lean/Compiler/LCNF/Basic.lean`. Focus on `inductive Code` and `structure LetDecl`.
- **The Pipeline**: Examine `src/Lean/Compiler/LCNF/Passes.lean`. This is where you will eventually hook in the JS emitter.
- **Prior Art**: Read `src/Lean/Compiler/LCNF/EmitC.lean`. It is the "gold standard" for emitting code from LCNF.

### 2. Implementation Plan

- **Step 1: The Emitter Monad**: Define `EmitM` with state for the output buffer and indentation level.
- **Step 2: Name Mangling**: Create a utility to convert Lean `Name` to valid JS identifiers.
- **Step 3: Expression Emission**: Write a function to emit `LCNF.Expr` (literals, constants, apps).
- **Step 4: Code Emission**: Implement a recursive `emitCode` that handles `let` bindings, `case` blocks, and `jmp`.
- **Step 5: Runtime library**: Create a small `lean-runtime.js` that provides `lean_nat_add`, `lean_string_append`, etc.
- **Step 6: Integration**: Register the new emitter as a compiler pass or a command-line option.
