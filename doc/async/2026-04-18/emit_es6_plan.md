# Learning and Implementation Plan for EmitEs6

This document outlines the steps required to learn the Lean compiler internals and implement a JavaScript (ES6) backend.

## 1. Learning Plan

To implement `EmitEs6` effectively, you need to master the following:

### A. LCNF Structure
*   **File**: `src/Lean/Compiler/LCNF/Basic.lean`
*   **Goal**: Understand `inductive Code`, `structure LetDecl`, and `inductive Expr`. Learn how LCNF represents assignments, cases, and jumps.

### B. Existing Emitters
*   **File**: `src/Lean/Compiler/LCNF/EmitC.lean`
*   **Goal**: This is the "gold standard" for LCNF-based emission. Study how it traverses the `Code` tree and manages local variables.
*   **File**: `src/Lean/Compiler/IR/EmitJavascript.lean_`
*   **Goal**: Study previous (experimental) attempts to understand JS-specific challenges like BigInt for `Nat` and name mangling.

### C. The Compiler Pipeline
*   **File**: `src/Lean/Compiler/LCNF/Passes.lean`
*   **Goal**: Learn where the emission step fits into the `Base -> Mono -> Impure` pipeline.

---

## 2. Implementation Plan

### Step 1: Emitter Infrastructure
- Define an `EmitM` monad (State + Reader) to handle:
    - Output buffer (string builder).
    - Indentation level.
    - Name mangling/sanitization (avoiding JS keywords like `class`, `const`, etc.).

### Step 2: Name Mangling
- Implement a function to convert Lean `Name` into valid JS identifiers (e.g., `Lean.Compiler.f` -> `Lean_Compiler_f`).

### Step 3: Expression Emission
- Implement `emitExpr` to handle:
    - Literals (Numbers, Strings).
    - Constants (Global functions).
    - Function applications (`f(a, b)`).

### Step 4: Code Block Emission
- Implement `emitCode` (recursive):
    - `let` binding -> `const x = ...;`
    - `case` -> `switch` or nested `if/else`.
    - `jmp` -> Join point invocation.
    - `return` -> `return x;`

### Step 5: Runtime Support
- Create a small JavaScript runtime library (`lean-runtime.js`) to provide:
    - `lean_nat_add`, `lean_nat_mul` (using `BigInt`).
    - Basic string and array operations.
    - Object representation for Lean types.

### Step 6: Integration
- Add `EmitEs6` to the Lean compiler driver.
- Add a command-line flag or attribute to trigger JS emission.
- Verify with basic "Hello World" Lean programs.
