/goal

in src/Lean4Lean You will find code of https://github.com/digama0/lean4lean which is a lean kernel implement in lean

I want You to delete kernel that is implemented in c++ src/kernel and replace it with that kernel implemented in lean

note that rn src/Lean4Lean contains dependency on batteries, which imports Prelude therefore maybe there is a cyclic dependency

I propose following approach:
find modules from which You should start. E.g. src/Lean4Lean/Environment/Basic.lean is a leaf

it uses
open private subsumesInfo Kernel.Environment.mk EnvironmentHeader.mk moduleNames
  moduleNameMap parts toEffectiveImport getData? from Lean.Environment

which will not work bc 1. depends on batteries package 2. open private doesnt work in lean files that uses `module` at the top. Probably functions from here should be moved to src/Lean/Environment.lean (check that adding new functions is really required, maybe they are already implemented)

then continue with other files that implement kernel

continue replacing c++ kernel with Lean4Lean kernel. In the end src/kernel should be removed. New kernel implemented in lean should probably live in src/Lean dir. Regenerate stage0 and run CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" test to test that everything still works

You can change location of Lean4Lean functions, but dont change their implementation unless absolutely necessarily required. Try to reuse current Lean4Lean implementation as much as possible. Why? Bc Lean4Lean kernel was already tested.

-------

Here is Lean4Lean Readme.md

```
# Lean-for-Lean

This is an implementation of the Lean 4 kernel written in (mostly) pure Lean 4.
It is derived directly from the C++ kernel implementation, and as such likely
shares some implementation bugs with it (it's not really an independent
implementation), although it also benefits from the same algorithmic performance
improvements existing in the C++ Lean kernel.

The project also houses some metatheory regarding the Lean
system, in the same general direction as the
[MetaCoq project](https://github.com/MetaCoq/metacoq/).

## Building

To compile the code, you will need [Lean](https://lean-lang.org/lean4/doc/quickstart.html), or more specifically `elan`, the Lean version manager, which will make sure you have the right version of lean as specified in the [lean-toolchain](lean-toolchain) file. Assuming you have elan, the project can be compiled with:

```
lake build
```

This builds all components but you can also build them separately:

* `lake build Lean4Lean` builds the `Lean4Lean` library interface, and does not include any of the proofs.
* `lake build lean4lean` (note the capitalization!) builds the `lean4lean` command line tool, again without building proofs.
* `lake build Lean4Lean.Theory` contains the Lean metatheory and properties.
* `lake build Lean4Lean.Verify` is the proof that the `Lean4Lean` implementation satisfies the `Lean4Lean.Theory` abstract specification.

## Running

After `lake build lean4lean`, the executable will be in `.lake/build/bin/lean4lean`. Because it requires some environment variables to be set for search paths which are provided by lake, you should evaluate it like `lake env .lake/build/bin/lean4lean`.

If you run this as is (with no additional arguments), it will check every olean in the `lean4lean` package itself, which is probably not what you want. To check a different Lean package you should navigate the directory of the target project, then use `lake env path/to/lean4lean/.lake/build/bin/lean4lean <args>` to run `lean4lean` in the context of the target project. The command line arguments are:

> `lean4lean [--fresh] [-v|--verbose] [--compare] [MOD]`

* `MOD`: an optional lean module name, like `Lean4Lean.Verify`. If provided, the specified module will be checked (single-threaded); otherwise, all modules on the Lean search path will be checked (multithreaded).
* `--fresh`: Only valid when a `MOD` is provided. In this mode, the module and all its imports will be rebuilt from scratch, checking all dependencies of the module. The behavior without the flag is to only check the module itself, assuming all imports are correct.
* `--verbose`: shows the name of each declaration before adding it to the environment. Useful to know if the kernel got stuck on something.
* `--compare`: If lean4lean takes more than a second on a given definition, we also check the C++ kernel performance to see if it is also slow on the same definition and report if lean4lean is abnormally slow in comparison.

## More documentation

* [bugs-found.md](bugs-found.md): A list of kernel bugs that the lean4lean project has uncovered.
* [divergences.md](divergences.md): A list of deliberate divergences between lean's kernel and the lean4lean kernel.

## (Selected) file breakdown

* `Main.lean`: command line app
* `Lean4Lean`: source files
  * `Environment.lean`: library entry point
  * `TypeChecker.lean`: main recursive function
  * `Inductive`
    * `Add.lean`: constructing inductive recursors
    * `Reduce.lean`: inductive iota rules
  * `Quot.lean`: quotient types handling
  * `Primitive.lean`: checking correctness of built-ins
  * `Std`: stuff that should exist upstream
  * `Theory`: lean metatheory
    * `VLevel.lean`: level expressions
    * `VExpr.lean`: expressions (boring de Bruijn variable theorems are here)
    * `VDecl.lean`: declarations
    * `VEnv.lean`: environment
    * `Meta.lean`: elaborator producing `VExpr`s
    * `Inductive.lean`: inductive types
    * `Quot.lean`: quotient types
    * `Typing`
      * `Basic.lean`: The typing relation itself
      * `Lemmas.lean`: theorems about the typing relation
      * `Meta.lean`: tactic for proving typing judgments
      * `Strong.lean`: proof that you can have all the inductive hypotheses
      * `UniqueTyping.lean`: conjectures about the typing relation
      * `Env.lean`: typing for environments
  * `Verify`: relation between the metatheory and the kernel
    * `Axioms.lean`: theorems about upstream opaques that shouldn't be opaque
    * `Expr.lean`: correctness of basics on `Expr`
    * `Level.lean`: correctness of basics on `Level`
    * `VLCtx.lean`: a "translation context" suitable for translating expressions
    * `LocalContext.lean`: properties of lean's `LocalContext` type
    * `NameGenerator.lean`: properties of the fresh name generator
    * `Typing`
      * `Expr.lean`: translating expressions (`TrExpr` is here)
      * `Lemmas.lean`: properties of `TrExpr`
      * `ConditionallyTyped.lean`: properties of expressions in caches that may be out of scope
    * `Environment`
      * `Basic.lean`: translating environments
      * `Lemmas.lean`: properties of `TrEnv`
    * `TypeChecker`
      * `Basic.lean`: typechecker invariants
      * `EquivManager.lean`: invariants for the union-find defeq cache
      * `InferType.lean`: correctness of `inferType`
      * `WHNF.lean`: correctness of `whnf`
      * `IsDefEq.lean`: correctness of `isDefEq`
    * `TypeChecker.lean`: top-level typechecker correctness
  * `Experimental`: work in progress formalizations and ideas
      * `Stratified.lean`: stratified typing judgment
      * `StratifiedUntyped.lean` another stratified typing judgment
      * `ParallelReduction.lean`: stuff related to church-rosser
      * `Stronger.lean`: a more heavily annotated typing judgment
```
-------

# Replace C++ Kernel With Lean Kernel

## Summary

Migrate the executable kernel code from src/Lean4Lean into bootstrapped src/Lean/Kernel/*, remove Batteries and open private dependencies, wire Lean kernel functions into Lean.Environment/Lean.AddDecl, then remove the C++ kern
el object library from the build.

## Key Changes

- Move only production kernel modules from src/Lean4Lean: environment basics, declaration helpers, level/expr/instantiate/local-context utilities, quotient support, primitive checks, inductive add/reduce, equiv manager, and
  type checker.
- Exclude src/Lean4Lean/Verify, Theory, and Experimental from the production kernel path.
- Convert moved files to core style:
    - module, blank line, prelude
    - explicit Init.* / Lean.* imports
    - no Batteries imports
    - no open private
- Promote required private helpers from Lean.Environment, Lean.Expr, Lean.Level, and instantiate utilities into public or kernel-internal APIs only when no public equivalent exists.

## Implementation

- Add src/Lean/Kernel/*.lean modules implementing:
    - Kernel.Environment.empty, import finalization helpers, contains, get, checkName, checkNoMVarNoFVar
    - Kernel.TypeChecker.check, whnf, isDefEq
    - Kernel.Environment.addDecl, including axioms, definitions, theorems, opaques, quotients, primitives, mutual definitions, and inductives
- Replace extern declarations in src/Lean/Environment.lean:
    - remove @[extern "lean_add_decl"] opaque addDeclCore
    - remove @[extern "lean_add_decl_without_checking"] opaque addDeclWithoutChecking
    - replace Kernel.isDefEq, Kernel.whnf, and Kernel.check with Lean implementations.
- Update src/Lean/AddDecl.lean to call the Lean implementation directly while preserving debug.skipKernelTC, heartbeat, cancel-token, async environment commit behavior, and error shapes.
- Keep the public Kernel.Environment data type stable so .olean import/export, async env state, diagnostics, and module metadata continue to work.
- Remove src/kernel from src/CMakeLists.txt.
- Relocate or replace non-typechecking C++ dependencies currently under src/kernel:
    - expression/level/declaration/local-context object wrappers still needed by C++ library code must move out of src/kernel before deleting the directory.
    - C++ construction code such as cases_on either keeps using relocated wrappers or is ported/wrapped separately.
- Add public import Lean.Kernel to the right point in Lean.lean/kernel-adjacent modules without creating an import cycle.

## Test Plan

- Add focused regression tests for kernel APIs:
    - direct Kernel.check, Kernel.whnf, Kernel.isDefEq
    - declaration add success/failure for axiom, theorem, def, opaque, mutual def, quotient, inductive
    - expected failures for metavariables, free variables, duplicate universe params, bad theorem type, invalid projection, bad inductive positivity
- Build:
    - make -j$(nproc) -C build/release
- Regenerate stage0:
    - make -C build/release update-stage0
- Full validation:
    - CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" test

## Assumptions

- The final state deletes src/kernel entirely, not just type_checker.cpp.
- C++ runtime/library code may retain object wrappers, but they must not live under src/kernel.
- The production kernel will not depend on Batteries, Lean4Lean.Verify, or experimental proof files.
- Existing kernel exception constructors and user-facing messages should remain compatible unless a test explicitly blesses a changed message.

------

Before You asked questions

Question 1/3 (2 unanswered)
After moving the production kernel into `src/Lean/*`, what should happen to the existing `Lean4Lean` namespace and files used by the standalone checker?

  1. Keep wrappers (Recommended)  Preserve `Lean4Lean` as a thin compatibility layer or re-export surface so `LeanChecker` and any local users keep building during the migration.
  2. Retire Lean4Lean             Move the production code into `Lean` and allow `Lean4Lean` library/CLI to break or be removed as part of this change.
  3. Keep checker only            Move kernel code into `Lean`, but keep enough `Lean4Lean` files for the standalone checker executable to continue working, without promising broader API compatibility.
› 4. None of the above            Optionally, add details in notes (tab).

Answer is 4. I dont care about Lean4Lean checker executable. Can safely remove this functionality. what is important is rewrite C++ kernel with Lean4Lean kernel implementation. And I think Lean4Lean namespace should be removed too and its code moved to src/Lean

When you say remove `src/kernel`, should the plan treat every C++ file there as in scope for removal now, including declaration/expr/level/local-context wrappers, or only the executable kernel logic with wrappers relocated if
still needed elsewhere?

› 1. Full removal (Recommended)  End state has no `src/kernel` directory; anything still needed in C++ must be relocated as part of this work.
  2. Logic only                  Remove typechecker/environment/inductive kernel logic, but allow low-level wrappers to remain under `src/kernel` temporarily.
  3. Two-step migration          Plan this as phase 1: switch to Lean kernel; phase 2: separately remove/relocate residual C++ wrappers from `src/kernel`.
  4. None of the above           Optionally, add details in notes (tab).

Answer is 1.

Question 3/3 (1 unanswered)
What performance bar should the migration plan assume for the first merged version of the Lean kernel?

› 1. Correctness first (Recommended)  Require clean build and test suite passing; accept regressions unless a focused kernel test becomes unusable or times out.
  2. No major regressions             Include targeted timing checks and treat obvious slowdowns in common workflows as blockers for the initial merge.
  3. Near parity                      Treat performance parity with the current C++ kernel as a hard requirement for the initial plan.
  4. None of the above                Optionally, add details in notes (tab).

Answer is 1.

Question 1/1 (1 unanswered)
How should the migration plan treat the existing `LeanChecker` target and its tests, which currently depend on `Lean4Lean`?

› 1. Remove them (Recommended)  Delete `LeanChecker` / `leanchecker` build targets and their dedicated tests as part of removing `Lean4Lean`.
  2. Retarget them              Keep the target and rewrite it to use the new in-tree Lean kernel implementation.
  3. Keep temporarily           Leave `LeanChecker` and its tests out of the first migration scope, even if that means `Lean4Lean` cannot be fully removed yet.
  4. None of the above          Optionally, add details in notes (tab).

Answer is 1. Bc I think the tests in ./tests dir are enough to confirm that new kernel works. What is important, again, is to not change Lean4Lean kernel implementation, because, again, it was working.

But preserve theorems, proofs about kernel. This will allow to ensure that our new kernel is implemented correctly even before running tests.

-----

new generated plan

# Replace C++ Kernel With Lean4Lean Kernel

## Summary

Replace the executable kernel implementation in src/kernel with the existing Lean4Lean implementation, moved into src/Lean/Kernel/* and wired into core Lean.Environment / Lean.AddDecl. Keep the Lean4Lean proofs and metatheory,
but stop using the Lean4Lean namespace for production kernel code. Remove the LeanChecker target and its dedicated tests as part of removing the old Lean4Lean runtime path.

## Key Changes

- Move the production Lean4Lean kernel code into core Lean modules under src/Lean/Kernel/*, preserving implementations as-is unless a change is required for bootstrapping or API fit.
- Retire the production Lean4Lean namespace and runtime entrypoints:
    - remove src/Lean4Lean.lean, src/Lean4LeanMain.lean, and the runtime-facing src/Lean4Lean/{Environment,TypeChecker,Primitive,Quot,Inductive/
      *,Expr,Level,LocalContext,Instantiate,ForEachExprV,EquivManager,PtrEq,Declaration}.lean files once their contents are moved
    - keep src/Lean4Lean/Theory, src/Lean4Lean/Verify, and related proof files, updating imports/names as needed so the proofs still talk about the moved kernel code
- Use core Lean APIs already present in src/Lean/Environment.lean for environment helpers (empty, contains, get, checkName, checkDuplicatedUnivParams, checkNoMVarNoFVar, isStructureLike) instead of reintroducing open private or
  Batteries-based shims.
- Add Lean kernel modules roughly along these subsystem boundaries:
    - environment/add-decl logic
    - typechecker / defeq / whnf
    - inductive add / inductive reduce
    - quotient initialization / primitive checks
    - small support utilities that the moved code needs (Expr, Level, instantiation, local context, ptr-eq, union-find/equiv manager)
- Replace C++ kernel extern hooks in src/Lean/Environment.lean and src/Lean/AddDecl.lean:
    - Kernel.Environment.addDeclCore
    - Kernel.Environment.addDeclWithoutChecking
    - Kernel.isDefEq
    - Kernel.whnf
    - Kernel.check
- Preserve existing public behavior at the Lean API boundary:
    - same declaration kinds and ConstantInfo layout
    - same async add-decl flow in Lean.AddDecl
    - same environment branching / .olean import-export behavior
    - same kernel exception shapes and, where practical, existing messages
- Remove all executable-kernel C++ code in src/kernel. If any low-level C++ support is still required by non-kernel code, relocate it out of src/kernel as part of this change so the directory can be deleted completely.
- Remove LeanChecker / leanchecker from:
    - src/lakefile.toml.in
    - src/stdlib.make.in
    - src/CMakeLists.txt
    - dedicated tests/pkg/leanchecker coverage

## Implementation Notes

- Start from leaf/support modules first, then build upward:
    1. support utilities (PtrEq, Declaration, Expr, Level, Instantiate, LocalContext, ForEachExprV, EquivManager)
    2. reduction helpers (Quot, Inductive.Reduce, Primitive)
    3. main checker (TypeChecker)
    4. declaration admission (Environment, Inductive.Add)
    5. Lean.Environment / Lean.AddDecl wiring
    6. CMake/Lake/test cleanup
- Convert moved modules to core style:
    - module
    - blank line
    - prelude
    - explicit Init.* / Lean.* imports only
    - no Batteries dependency
- Keep proof code compiling by retargeting it to the moved Lean.Kernel.* modules rather than preserving duplicate production code under Lean4Lean.
- Treat performance as non-blocking for v1 unless the migrated kernel makes existing core tests unusable or causes widespread timeouts.

## Test Plan

- Add focused kernel regression tests for:
    - Kernel.check, Kernel.whnf, Kernel.isDefEq
    - adding axioms, defs, theorems, opaques, mutual defs, quotients, and inductives
    - expected failures for metavariables, free variables, duplicate universe params, bad theorem type, invalid projections, and invalid inductives
- Keep the existing proof/metatheory build green after retargeting imports, so the preserved theorems still validate the moved implementation.
- Validation sequence:
    1. clean build with the documented build command
    2. regenerate stage0
    3. full ctest suite
- Success criteria:
    - build succeeds
    - relevant tests pass
    - src/kernel is gone
    - LeanChecker target/tests are removed
    - proof files are preserved and compile against the moved kernel code

## Assumptions

- Correctness is the acceptance bar for the first merge; performance parity with the current C++ kernel is not required.
- The Lean4Lean production implementation should be reused structurally and algorithmically, with only the minimum edits needed for bootstrapping, import hygiene, namespace relocation, and core API integration.
- Preserving proofs means keeping Theory / Verify source and adapting them to the moved kernel modules, not preserving the old Lean4Lean runtime namespace.

-----------

Last update was

• I moved the migration materially, but I did not finish the user goal. src/
kernel still exists, and the runtime is still hybrid.

What I changed:

- src/kernel/environment.cpp:147 now sends environment::add(declaration,
check) straight to the Lean kernel exports. The old native declaration-
admission path is no longer used there.
- src/kernel/kernel_exception.h:219 now converts Lean.Kernel.Exception
values back into the existing C++ exception classes, so the bridge can
preserve current exception behavior.
- src/Lean/Kernel/TypeChecker.lean:817 exports new Kernel.Environment-
based entrypoints for check, whnf, and isDefEq.
- src/kernel/type_checker.cpp:11 is now a thin shim over those Lean
exports. The old native checker body is gone from the runtime path.
- src/kernel/inductive.cpp:12 was reduced to the small utility surface
still used by library/* and the Lean kernel support code. The old native
inductive declaration-admission implementation was removed from that file.
- tests/elab/importStructure.lean:67 still includes the earlier
Lean.Kernel root fix.

What I verified:

- make -C build/release -j4 passes.
- make -C build/release update-stage0 -j4 passes.
- Focused regression coverage passes:
    - elab/importStructure.lean
    - elab/grind_lint_1.lean
    - elab/grind_lint_std_treemap.lean
    - elab/levenshtein.lean
    - compile/expr.lean
    - elab/doLogicTests.lean
- tests/bench/mvcgen/sym passes again, including test_vcgen and
vcgen_get_throw_set_grind.

I also started a full ctest sweep. Before I interrupted it, these early
high-signal tests had already passed:

- bench/mvcgen/sym
- pkg/frontend
- server_interactive/unknownIdentifierCodeActions.lean
- elab/grind_indexmap_trace.lean
- elab/grind_lint_1.lean

Why this is still incomplete:

- src/kernel has not been removed.
- src/kernel/CMakeLists.txt still builds the old kernel object library.
- The remaining wrapper/object files under src/kernel still need to be
split, relocated, or deleted before this counts as “replace C++ kernel
with Lean kernel”.

The next concrete step is to keep peeling src/kernel down to pure object-
wrapper/runtime support, then remove the directory from the build and
rerun the full test suite end to end.

────────────────────────────────────────────────────────────────────────────

• I found a real divergence from the original Lean4Lean implementation in
whnfCore': the lambda-application branch had been switched to
Expr.betaRev. For this benchmark, that is a much more plausible source of
runaway normalization than the raw fuel value, so I’m restoring the
original loop.
