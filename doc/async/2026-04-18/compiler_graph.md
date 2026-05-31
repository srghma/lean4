# Lean Compiler File Graph

This document provides a tree-like graph of the files in `src/Lean/Compiler` and descriptions of their purposes.

## File Graph

```text
src/Lean/Compiler/
├── BorrowedAnnotation.lean
├── CSimpAttr.lean
├── ClosedTermCache.lean
├── EmitEs6.lean_
├── ExportAttr.lean
├── ExternAttr.lean
├── FFI.lean
├── IR.lean
├── IR/
│   ├── Basic.lean
│   ├── Checker.lean
│   ├── CompilerM.lean
│   ├── EmitJavascript.lean_
│   ├── EmitLLVM.lean
│   ├── EmitUtil.lean
│   ├── Format.lean
│   ├── JsBasic.lean_
│   ├── LLVMBindings.lean
│   ├── Meta.lean
│   ├── NormIds.lean
│   ├── Sorry.lean
│   ├── ToIR.lean
│   ├── ToIRType.lean
│   └── UnboxResult.lean
├── ImplementedByAttr.lean
├── InitAttr.lean
├── InlineAttrs.lean
├── LCNF.lean
├── LCNF/
│   ├── AlphaEqv.lean
│   ├── AuxDeclCache.lean
│   ├── BaseTypes.lean
│   ├── Basic.lean
│   ├── Bind.lean
│   ├── CSE.lean
│   ├── Check.lean
│   ├── Closure.lean
│   ├── CoalesceRC.lean
│   ├── CompatibleTypes.lean
│   ├── CompilerM.lean
│   ├── ConfigOptions.lean
│   ├── DeclHash.lean
│   ├── DependsOn.lean
│   ├── ElimDead.lean
│   ├── ElimDeadBranches.lean
│   ├── EmitC.lean
│   ├── EmitUtil.lean
│   ├── ExpandResetReuse.lean
│   ├── ExplicitBoxing.lean
│   ├── ExplicitRC.lean
│   ├── ExtractClosed.lean
│   ├── FVarUtil.lean
│   ├── FixedParams.lean
│   ├── FloatLetIn.lean
│   ├── InferBorrow.lean
│   ├── InferType.lean
│   ├── Internalize.lean
│   ├── Irrelevant.lean
│   ├── JoinPoints.lean
│   ├── LCtx.lean
│   ├── LambdaLifting.lean
│   ├── Level.lean
│   ├── LiveVars.lean
│   ├── Main.lean
│   ├── MonadScope.lean
│   ├── MonoTypes.lean
│   ├── OtherDecl.lean
│   ├── PassManager.lean
│   ├── Passes.lean
│   ├── PhaseExt.lean
│   ├── PrettyPrinter.lean
│   ├── Probing.lean
│   ├── PropagateBorrow.lean
│   ├── PublicDeclsExt.lean
│   ├── PullFunDecls.lean
│   ├── PullLetDecls.lean
│   ├── PushProj.lean
│   ├── ReduceArity.lean
│   ├── ReduceJpArity.lean
│   ├── Renaming.lean
│   ├── ResetReuse.lean
│   ├── ScopeM.lean
│   ├── Simp.lean
│   ├── Simp/
│   │   ├── Basic.lean
│   │   ├── Config.lean
│   │   ├── ConstantFold.lean
│   │   ├── DefaultAlt.lean
│   │   ├── DiscrM.lean
│   │   ├── FunDeclInfo.lean
│   │   ├── InlineCandidate.lean
│   │   ├── InlineProj.lean
│   │   ├── JpCases.lean
│   │   ├── Main.lean
│   │   ├── SimpM.lean
│   │   ├── SimpValue.lean
│   │   └── Used.lean
│   ├── SimpCase.lean
│   ├── SimpleGroundExpr.lean
│   ├── SpecInfo.lean
│   ├── Specialize.lean
│   ├── SplitSCC.lean
│   ├── StructProjCases.lean
│   ├── ToDecl.lean
│   ├── ToExpr.lean
│   ├── ToImpure.lean
│   ├── ToImpureType.lean
│   ├── ToLCNF.lean
│   ├── ToMono.lean
│   ├── Toposort.lean
│   ├── Types.lean
│   ├── Util.lean
│   └── Visibility.lean
├── Main.lean
├── MetaAttr.lean
├── ModPkgExt.lean
├── NameDemangling.lean
├── NameMangling.lean
├── NeverExtractAttr.lean
├── NoncomputableAttr.lean
├── Old.lean
├── Options.lean
└── Specialize.lean
```

## Module Descriptions

### Root Modules
- **`BorrowedAnnotation.lean`**: Tracks `@[borrowed]` annotations for parameter ownership.
- **`CSimpAttr.lean`**: Logic for `@[csimp]` attribute.
- **`ClosedTermCache.lean`**: Cache for processing closed terms.
- **`EmitEs6.lean_`**: Experimental JavaScript ES6 emitter.
- **`ExportAttr.lean`**: Logic for `@[export]` attribute.
- **`ExternAttr.lean`**: Logic for `@[extern]` attribute.
- **`FFI.lean`**: Utilities for Foreign Function Interface.
- **`IR.lean`**: Entry point for the IR (Intermediate Representation) module.
- **`ImplementedByAttr.lean`**: Logic for `@[implemented_by]` attribute.
- **`InitAttr.lean`**: Logic for `@[init]` attribute.
- **`InlineAttrs.lean`**: Logic for `@[inline]` and related attributes.
- **`LCNF.lean`**: Entry point for LCNF (Lean Compiler Normal Form) module.
- **`Main.lean`**: The main compiler driver.
- **`MetaAttr.lean`**: Logic for `@[meta]` attribute.
- **`ModPkgExt.lean`**: Extensions for module/package management.
- **`NameDemangling.lean`**: Converts mangled names back to Lean names.
- **`NameMangling.lean`**: Converts Lean names into valid C identifiers.
- **`NeverExtractAttr.lean`**: Logic for `@[never_extract]` attribute.
- **`NoncomputableAttr.lean`**: Tracks declarations that are not computable.
- **`Old.lean`**: Legacy compiler components.
- **`Options.lean`**: Configuration options for the compiler.
- **`Specialize.lean`**: Logic for `@[specialize]` attribute.

### IR (Low-level IR)
- **`IR/Basic.lean`**: Basic data structures for the low-level IR.
- **`IR/Checker.lean`**: Type and consistency checker for IR.
- **`IR/CompilerM.lean`**: Monad for the IR compiler.
- **`IR/EmitJavascript.lean_`**: (Experimental) JS emitter from IR.
- **`IR/EmitLLVM.lean`**: Generates LLVM IR from Lean IR.
- **`IR/EmitUtil.lean`**: Utilities for code emission.
- **`IR/Format.lean`**: Pretty printer for the IR.
- **`IR/JsBasic.lean_`**: (Experimental) Basic definitions for JS emission.
- **`IR/LLVMBindings.lean`**: Lean bindings to the LLVM API.
- **`IR/Meta.lean`**: Metadata for IR declarations.
- **`IR/NormIds.lean`**: Normalizes identifiers in the IR.
- **`IR/Sorry.lean`**: Handles `sorry` in IR.
- **`IR/ToIR.lean`**: Lowering from LCNF to IR.
- **`IR/ToIRType.lean`**: Type mapping from Lean types to IR types.
- **`IR/UnboxResult.lean`**: Optimization to unbox result values.

### LCNF (Lean Compiler Normal Form)
- **`LCNF/AlphaEqv.lean`**: Alpha-equivalence for LCNF expressions.
- **`LCNF/AuxDeclCache.lean`**: Cache for auxiliary declarations.
- **`LCNF/BaseTypes.lean`**: Identification of primitive/base types.
- **`LCNF/Basic.lean`**: Core LCNF data structures (Code, Decl, Expr).
- **`LCNF/Bind.lean`**: Binding/composition of LCNF code blocks.
- **`LCNF/CSE.lean`**: Common Subexpression Elimination.
- **`LCNF/Check.lean`**: LCNF structural and type checker.
- **`LCNF/Closure.lean`**: Closure analysis and handling.
- **`LCNF/CoalesceRC.lean`**: Optimization of reference counting.
- **`LCNF/CompatibleTypes.lean`**: Checks for type compatibility.
- **`LCNF/CompilerM.lean`**: The LCNF compiler monad.
- **`LCNF/ConfigOptions.lean`**: Configurable options for LCNF passes.
- **`LCNF/DeclHash.lean`**: Hashing for LCNF declarations.
- **`LCNF/DependsOn.lean`**: Dependency analysis for variables.
- **`LCNF/ElimDead.lean`**: Elimination of dead variables and code.
- **`LCNF/ElimDeadBranches.lean`**: Removes unreachable case branches.
- **`LCNF/EmitC.lean`**: C++ code generation from LCNF.
- **`LCNF/EmitUtil.lean`**: Utilities for emitting C++ code.
- **`LCNF/ExpandResetReuse.lean`**: Lowers `reset`/`reuse` primitives.
- **`LCNF/ExplicitBoxing.lean`**: Inserts explicit boxing/unboxing operations.
- **`LCNF/ExplicitRC.lean`**: Inserts explicit reference counting operations.
- **`LCNF/ExtractClosed.lean`**: Extracts closed expressions into top-level constants.
- **`LCNF/FVarUtil.lean`**: Utilities for handling free variables.
- **`LCNF/FixedParams.lean`**: Identification of fixed parameters in recursive functions.
- **`LCNF/FloatLetIn.lean`**: Optimization to "float" let-bindings.
- **`LCNF/InferBorrow.lean`**: Analysis to infer borrowed parameters.
- **`LCNF/InferType.lean`**: Type inference for LCNF expressions.
- **`LCNF/Internalize.lean`**: Internalizes names and variables for processing.
- **`LCNF/Irrelevant.lean`**: Removal of computationally irrelevant code.
- **`LCNF/JoinPoints.lean`**: Logic for managing join points.
- **`LCNF/LCtx.lean`**: Local context management for LCNF.
- **`LCNF/LambdaLifting.lean`**: Converts nested functions to top-level ones.
- **`LCNF/Level.lean`**: Handling of universe levels.
- **`LCNF/LiveVars.lean`**: Variable liveness analysis.
- **`LCNF/Main.lean`**: Driver for LCNF compilation.
- **`LCNF/MonadScope.lean`**: Monadic scope management.
- **`LCNF/MonoTypes.lean`**: Type representation for monomorphization.
- **`LCNF/OtherDecl.lean`**: Handling of auxiliary/special declarations.
- **`LCNF/PassManager.lean`**: Framework for managing LCNF passes.
- **`LCNF/Passes.lean`**: Definition of the standard LCNF pass pipeline.
- **`LCNF/PhaseExt.lean`**: Support for different LCNF phases (Base, Mono, Impure).
- **`LCNF/PrettyPrinter.lean`**: Pretty printer for LCNF.
- **`LCNF/Probing.lean`**: Instrumentation for probing LCNF state.
- **`LCNF/PropagateBorrow.lean`**: Propagates borrowed status across calls.
- **`LCNF/PublicDeclsExt.lean`**: Tracks public declarations.
- **`LCNF/PullFunDecls.lean`**: Pulls function declarations out of nested scopes.
- **`LCNF/PullLetDecls.lean`**: Pulls let-declarations out.
- **`LCNF/PushProj.lean`**: Pushes projections into case branches.
- **`LCNF/ReduceArity.lean`**: Reduces the arity of functions.
- **`LCNF/ReduceJpArity.lean`**: Reduces the arity of join points.
- **`LCNF/Renaming.lean`**: Logic for renaming variables.
- **`LCNF/ResetReuse.lean`**: Optimization of memory reuse.
- **`LCNF/ScopeM.lean`**: Monad for tracking scope.
- **`LCNF/Simp.lean`**: Entry point for the simplifier.
- **`LCNF/SimpCase.lean`**: Specifically simplifies case expressions.
- **`LCNF/SimpleGroundExpr.lean`**: Identification of ground expressions.
- **`LCNF/SpecInfo.lean`**: Tracking of specialization information.
- **`LCNF/Specialize.lean`**: Function specialization logic.
- **`LCNF/SplitSCC.lean`**: Splits strongly connected components.
- **`LCNF/StructProjCases.lean`**: Optimization of structure projection patterns.
- **`LCNF/ToDecl.lean`**: High-level declaration to LCNF conversion.
- **`LCNF/ToExpr.lean`**: LCNF to Expr conversion (for debugging).
- **`LCNF/ToImpure.lean`**: Transition to the Impure LCNF phase.
- **`LCNF/ToImpureType.lean`**: Type mapping for the Impure phase.
- **`LCNF/ToLCNF.lean`**: The main Expr to LCNF conversion logic.
- **`LCNF/ToMono.lean`**: Monomorphization pass.
- **`LCNF/Toposort.lean`**: Topological sort of declarations.
- **`LCNF/Types.lean`**: Definition of primitive LCNF types.
- **`LCNF/Util.lean`**: General utilities for LCNF.
- **`LCNF/Visibility.lean`**: Logic for determining declaration visibility.

### LCNF Simp (Simplifier)
- **`LCNF/Simp/Basic.lean`**: Basic state and core of the simplifier.
- **`LCNF/Simp/Config.lean`**: Configuration for simplifier passes.
- **`LCNF/Simp/ConstantFold.lean`**: Constant folding rules.
- **`LCNF/Simp/DefaultAlt.lean`**: Handling of default alternatives in cases.
- **`LCNF/Simp/DiscrM.lean`**: Monad for tracking discriminants.
- **`LCNF/Simp/FunDeclInfo.lean`**: Analysis of function declaration usage.
- **`LCNF/Simp/InlineCandidate.lean`**: Heuristics for inlining.
- **`LCNF/Simp/InlineProj.lean`**: Inlining of projections.
- **`LCNF/Simp/JpCases.lean`**: Join point and case optimizations.
- **`LCNF/Simp/Main.lean`**: Main simplifier loop.
- **`LCNF/Simp/SimpM.lean`**: The simplifier monad.
- **`LCNF/Simp/SimpValue.lean`**: Value representations for simplification.
- **`LCNF/Simp/Used.lean`**: Tracking of used variables during simplification.
