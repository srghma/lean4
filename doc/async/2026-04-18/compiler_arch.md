# Lean 4 Compiler Architecture

This document provides a comprehensive overview of the Lean 4 compiler's internal structure, its intermediate representations, and the code generation paths.

## Compiler File Graph

The following is a complete list of all source files in `src/Lean/Compiler` and their roles.

### Root Directory (`src/Lean/Compiler/`)

- **`BorrowedAnnotation.lean`**: Handles `@[borrowed]` annotations for tracking parameter ownership.
- **`CSimpAttr.lean`**: Implementation of the `@[csimp]` attribute for compiler simplification rules.
- **`ClosedTermCache.lean`**: Cache for closed terms to avoid redundant processing.
- **`EmitEs6.lean_`**: (Experimental) Preliminary work on an ES6 JavaScript emitter.
- **`ExportAttr.lean`**: Handles the `@[export]` attribute for making Lean functions visible to C/C++.
- **`ExternAttr.lean`**: Logic for the `@[extern]` attribute, linking Lean declarations to external code.
- **`FFI.lean`**: Foreign Function Interface utilities.
- **`IR.lean`**: Main entry point for the low-level IR module.
- **`ImplementedByAttr.lean`**: Implementation of `@[implemented_by]`.
- **`InitAttr.lean`**: Logic for the `@[init]` attribute (module initialization).
- **`InlineAttrs.lean`**: Logic for `@[inline]`, `@[always_inline]`, `@[macro_inline]`, and `@[noinline]`.
- **`LCNF.lean`**: Main entry point for the Lean Compiler Normal Form module.
- **`Main.lean`**: High-level driver for the compiler.
- **`MetaAttr.lean`**: Support for `@[meta]` declarations.
- **`ModPkgExt.lean`**: Module and package level extensions for the compiler.
- **`NameDemangling.lean`**: Converts mangled C names back to Lean names.
- **`NameMangling.lean`**: Converts Lean names into valid C identifiers.
- **`NeverExtractAttr.lean`**: Implementation of `@[never_extract]`.
- **`NoncomputableAttr.lean`**: Tracking of `noncomputable` declarations.
- **`Old.lean`**: Legacy compiler code or compatibility layers.
- **`Options.lean`**: Configuration options for the compiler (e.g., `compiler.check`).
- **`Specialize.lean`**: Logic for the `@[specialize]` attribute.

### LCNF (`src/Lean/Compiler/LCNF/`)

LCNF is the primary IR for optimizations.

- **`AlphaEqv.lean`**: Alpha-equivalence for LCNF expressions.
- **`AuxDeclCache.lean`**: Cache for auxiliary declarations.
- **`BaseTypes.lean`**: Identification of "base" types in LCNF.
- **`Basic.lean`**: Core LCNF data structures: `Code`, `Decl`, `LetDecl`, `Param`, `Expr`.
- **`Bind.lean`**: Monadic binding utilities for LCNF code.
- **`CSE.lean`**: Common Sub-expression Elimination.
- **`Check.lean`**: Structural and type consistency checker for LCNF.
- **`Closure.lean`**: Utilities for handling closures.
- **`CoalesceRC.lean`**: Optimization to reduce redundant reference counting operations.
- **`CompatibleTypes.lean`**: Type compatibility checks within LCNF.
- **`CompilerM.lean`**: The `CompilerM` monad for LCNF passes.
- **`ConfigOptions.lean`**: Configuration specific to LCNF passes.
- **`DeclHash.lean`**: Hashing for LCNF declarations.
- **`DependsOn.lean`**: Dependency analysis for variables and declarations.
- **`ElimDead.lean`**: Dead code elimination (variables and expressions).
- **`ElimDeadBranches.lean`**: Removes unreachable branches in `case` expressions.
- **`EmitC.lean`**: Generates C++ code from LCNF.
- **`EmitUtil.lean`**: Utilities used by `EmitC`.
- **`ExpandResetReuse.lean`**: Lowers `reset` and `reuse` operations.
- **`ExplicitBoxing.lean`**: Inserts explicit boxing/unboxing operations for scalar types.
- **`ExplicitRC.lean`**: Inserts explicit reference counting (`inc`/`dec`) operations.
- **`ExtractClosed.lean`**: Pulls closed expressions out into top-level constants.
- **`FVarUtil.lean`**: Utilities for working with free variables.
- **`FixedParams.lean`**: Static analysis to identify fixed parameters in recursive functions.
- **`FloatLetIn.lean`**: Optimization to "float" let-bindings closer to their use sites.
- **`InferBorrow.lean`**: Analysis to infer which parameters can be borrowed.
- **`InferType.lean`**: Type inference for LCNF expressions.
- **`Internalize.lean`**: Converts external declarations into an internal LCNF format.
- **`Irrelevant.lean`**: Identification and removal of computationally irrelevant terms.
- **`JoinPoints.lean`**: Optimization and management of join points (continuations).
- **`LCtx.lean`**: Local context management for LCNF variables.
- **`LambdaLifting.lean`**: Converts nested lambdas into top-level declarations.
- **`Level.lean`**: Universe level management in LCNF.
- **`LiveVars.lean`**: Liveness analysis for variables.
- **`Main.lean`**: LCNF pass manager driver.
- **`MonadScope.lean`**: Monadic scope tracking for LCNF.
- **`MonoTypes.lean`**: Type representation for monomorphization.
- **`OtherDecl.lean`**: Handling of non-function declarations.
- **`PassManager.lean`**: Framework for defining and running LCNF pass pipelines.
- **`Passes.lean`**: The standard LCNF pass pipeline definition.
- **`PhaseExt.lean`**: Support for different compiler phases (Base, Mono, Impure).
- **`PrettyPrinter.lean`**: Human-readable output for LCNF.
- **`Probing.lean`**: Utilities for inspecting LCNF code during compilation.
- **`PropagateBorrow.lean`**: Propagates borrowed annotations through the call graph.
- **`PublicDeclsExt.lean`**: Tracks which declarations are visible outside the module.
- **`PullFunDecls.lean`**: Lifts function declarations.
- **`PullLetDecls.lean`**: Lifts let-bindings.
- **`PushProj.lean`**: Pushes projections into `case` branches.
- **`ReduceArity.lean`**: Optimization to reduce the number of arguments in functions.
- **`ReduceJpArity.lean`**: Specifically reduces arity for join points.
- **`Renaming.lean`**: Variable renaming utilities.
- **`ResetReuse.lean`**: Optimization to reuse memory cells.
- **`ScopeM.lean`**: Monad for tracking variable scope.
- **`Simp.lean`**: Entry point for the LCNF simplifier.
- **`SimpCase.lean`**: Simplification of `case` expressions.
- **`SimpleGroundExpr.lean`**: Identification of ground (no free variables) expressions.
- **`SpecInfo.lean`**: Information tracking for specialization.
- **`Specialize.lean`**: Monomorphization and function specialization.
- **`SplitSCC.lean`**: Splits strongly connected components in the call graph.
- **`StructProjCases.lean`**: Optimizes `case` expressions over structure projections.
- **`ToDecl.lean`**: High-level conversion of `Expr` to LCNF declarations.
- **`ToExpr.lean`**: Conversion of LCNF back to `Expr` (mostly for debugging).
- **`ToImpure.lean`**: Transition from pure LCNF to impure LCNF.
- **`ToImpureType.lean`**: Type conversion for the impure phase.
- **`ToLCNF.lean`**: The main `Expr -> LCNF` conversion logic.
- **`ToMono.lean`**: Monomorphization pass.
- **`Toposort.lean`**: Topologically sorts declarations based on dependencies.
- **`Types.lean`**: Primitive types and type utilities for LCNF.
- **`Util.lean`**: General utilities for LCNF.
- **`Visibility.lean`**: Logic for declaration visibility.

#### LCNF Simplifier (`src/Lean/Compiler/LCNF/Simp/`)

- **`Basic.lean`**: Core state and types for the simplifier.
- **`Config.lean`**: Configuration options for `Simp`.
- **`ConstantFold.lean`**: Constant folding rules.
- **`DefaultAlt.lean`**: Handling of default alternatives in `case`.
- **`DiscrM.lean`**: Monad for tracking discriminants in `case` expressions.
- **`FunDeclInfo.lean`**: Tracking information about function declarations (e.g., usage count).
- **`InlineCandidate.lean`**: Heuristics for determining when to inline.
- **`InlineProj.lean`**: Inlining for structure projections.
- **`JpCases.lean`**: Join point specific case optimizations.
- **`Main.lean`**: The main simplification loop.
- **`SimpM.lean`**: The simplifier monad.
- **`SimpValue.lean`**: Simplified value representation.
- **`Used.lean`**: Tracking of used variables.

### Low-Level IR (`src/Lean/Compiler/IR/`)

IR is used for reference counting and unboxing.

- **`Basic.lean`**: Core IR data structures.
- **`Checker.lean`**: Consistency checker for IR.
- **`CompilerM.lean`**: The IR compiler monad.
- **`EmitJavascript.lean_`**: (Experimental) Preliminary JS emitter from IR.
- **`EmitLLVM.lean`**: Generates LLVM IR.
- **`EmitUtil.lean`**: Shared utilities for IR emitters.
- **`Format.lean`**: Pretty printer for IR.
- **`JsBasic.lean_`**: (Experimental) Basic JS IR definitions.
- **`LLVMBindings.lean`**: Bindings to the LLVM API.
- **`Meta.lean`**: Metadata for IR declarations.
- **`NormIds.lean`**: Normalization of variable identifiers.
- **`Sorry.lean`**: Handling of `sorry` in IR.
- **`ToIR.lean`**: Lowering from LCNF to IR.
- **`ToIRType.lean`**: Type conversion for IR.
- **`UnboxResult.lean`**: Optimization to return scalar results without boxing.

---

## Compilation Paths

### 1. Standard Path (The Heavy-Duty Optimizer)

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> IR -> LLVM IR -> Machine Code`

Designed for maximum performance using LLVM.

### 2. C++ Path (Modern Default)

**Path**: `Source -> Expr -> Decl -> Code (LCNF) -> C++ Source`

The modern backend generates C++ directly from LCNF (Impure phase).

---

## Proposal: `EmitEs6` (JavaScript Backend)

**Recommended Path**: `Source -> Expr -> Decl -> Code (LCNF) -> JS Source`

### Rationale

LCNF provides the best balance of high-level optimization (inlining, CSE) and low-level lowering (lambda lifting, join point handling). Targetting LCNF ensures a performant and clean JS output without the burden of manual reference counting required by the `IR` path.

---

## Implementation Plan for `EmitEs6`

1. **Learning**: Study `LCNF/Basic.lean` and `LCNF/EmitC.lean`.
2. **Emitter**: Build `EmitM` for indentation/buffering.
3. **Mangling**: Map Lean names to JS.
4. **Code Gen**: Implement `emitCode` for LCNF `let`, `case`, and `jmp`.
5. **Runtime**: Provide a small JS library for core Lean types.
