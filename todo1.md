# Original task

./src/Init/Prelude.lean

./src/Lean/Compiler/JsExternInlinedAttr.lean

I want to implement js_extern_inlined , this is like extern attribute but instead of string I attach the subset of js code

after it works - I want to use it in
EmitEs6.lean
  to replace

if jsNameBase == "Nat$add" || jsNameBase == "lean_nat_add" || jsNameBase == "Int$add" || jsNameBase == "lean_int_add" || jsNameBase == "Float$add" ||
    jsNameBase == "String$append" || jsNameBase == "lean_string_append" || jsNameBase == "String$Internal$append" || jsNameBase == "USize$add" then
  if args.size == 2 then return JsExpr.binary args[0]! "+" args[1]!
  else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "+" allArgs[1]!
  else return ← mkNamedCall jsName
else if jsNameBase == "Nat$mul" || jsNameBase == "lean_nat_mul" || jsNameBase == "Int$mul" || jsNameBase == "lean_int_mul" || jsNameBase == "Float$mul" then
  if args.size == 2 then return JsExpr.binary args[0]! "*" args[1]!
  else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "*" allArgs[1]!
  else return ← mkNamedCall jsName
else if jsNameBase == "Int$sub" || jsNameBase == "lean_int_sub" || jsNameBase == "Float$sub" || jsNameBase == "USize$sub" then
  if args.size == 2 then return JsExpr.binary args[0]! "-" args[1]!
  else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "-" allArgs[1]!
  else return ← mkNamedCall jsName
else if jsNameBase == "Nat$sub" || jsNameBase == "lean_nat_sub" then
  if args.size == 2 then return JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "max") #[JsExpr.litNum "0", JsExpr.binary args[0]! "-" args[1]!]
  else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "max") #[JsExpr.litNum "0", JsExpr.binary allArgs[0]! "-" allArgs[1]!]
  else return ← mkNamedCall jsName


with definitions of functions inside of this js_external_inlined

why? what is the difference btw external and js_external_inlined?

external is how to implement ffi in c++ and js, js_external_inlined is fii for js only

if func has external only then after Xxx.lean is compiled to js - we will add `import { funcs } from 'Xxx.external.js` (if project is compiled using lake, in this case Xxx.js is copied into .lake dir but we new
extension .external.js instead of .js) or `import { funcs } from 'abspathto/Xxx.js` (if we build just using lean program, in this case we dont copy anything, but instead just render file with correct imports)

if func has external and js_external_inlined - we prefer js_external_inlined - we inline this code into generated code. why? it allows to partially of fully evaluate code, bc we know what js is doing!!, cool, right?

Goal:
1. make all es6 tests (one-file-tests in ./tests/es6/ + lake test in ./tests/lake/es6) pass

CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)"

./tests/es6/gen_expected_output.sh && CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" test ARGS="-R es6"

2. make EmitEs6 undertand js_external_inlined. if some modules have @[extern "xxx"] -> try to replace with js_external_inlined if function is simple or add ffi file Module.js if not simple

3. ./src/Init/Prelude.lean (and other modules) should use js_external_inlined if possible (just like rn. Only one function is complex and requires ffi)

NOTE: before we were using ./runnerjs-old.js which had many ffi functions globally. but we now should use extern or js_external_inlined. also remember that ghost variables should not be rendered (e.g. world should be rendered as
comment /* world */ (check current implmenetation of EmitEs6))

NOTE2: how to deal with IO functions.

- BaseIO should be generated to js code as ordinary js function (difference from pure functions? BaseIO funcs cannot be inlined like pure func)
- EIO - is a function that returns { tag: "EST$Out$ok", _1: value } or { tag: "EST$Out$error", _1: ... }
- IO is a function that returns { tag: "EST$Out$ok", _1: value } or { tag: "EST$Out$error", _1: ... } too


# then You did

I have implemented the core infrastructure for the `@[js_extern_inlined]` attribute and integrated it into the ES6 emitter. Here is a summary of the steps taken so far:

### 1. Attribute & AST Implementation
*   **Defined the JS Inline AST:** Created/refined the `JsInlineExpr` inductive type in `src/Lean/Compiler/JsExternInlinedAttr.lean` to support a wide range of JS constructs used in `Prelude`, including binary/unary operators, property access, array literals, and `new` expressions.
*   **Unified the Helper API:** Created a `JS` helper namespace that allows defining JS snippets in a structured way (e.g., `JS.add (JS.arg 0) (JS.arg 1)`).
*   **Safe Evaluation:** Implemented an evaluation path that converts the Lean terms provided to the attribute into the `JsInlineExpr` AST. I moved this into a safe interface using `@[implemented_by]` to avoid tainting the compiler with `unsafe` markers.

### 2. ES6 Emitter Integration
*   **Wired Attribute Lookup:** Updated `src/Lean/Compiler/LCNF/EmitEs6.lean` to check for `js_extern_inlined` before falling back to standard externs or hardcoded primitives.
*   **AST Rendering:** Taught the emitter how to render the full `JsInlineExpr` DSL into valid JavaScript code.
*   **Cleanup:** Removed the stale `Lean.Compiler.JS.Basic` import and updated the emitter to use the new structured attribute data.

### 3. Bootstrap & Prelude Migration
*   **Bootstrap Compatibility:** Because `Init/Prelude.lean` is compiled by the `stage0` (bootstrap) compiler, I pivoted the attribute syntax to use identifiers (e.g., `@[js_extern_inlined Lean.Compiler.JS.Impl.natAdd]`). This allowed the old compiler to parse the source while the new compiler recovers the structured JS data.
*   **Centralized JS Implementation:** Created `Lean.Compiler.JS.Impl` to hold the "truth" for how core functions like `Nat.add`, `Array.get`, and `Float.ofScientific` should be inlined in JS.
*   **Source Migration:** Updated `src/Init/Prelude.lean` and `src/Init/Data/OfScientific.lean` to replace dozens of hardcoded primitives with the new attribute.

### 4. Testing & Validation
*   **Added Regression Test:** Created `tests/es6/JsExternInlined01.lean` to verify that the attribute works for non-primitive, user-defined functions and correctly handles partial application (generating closures for inlined code).
*   **Refreshed Stage0:** Performed a full `update-stage0` cycle to ensure the new attribute parser and logic are baked into the bootstrap compiler.

### Current Status
The project is currently in a full rebuild with the restored `Prelude` annotations. Once this completes, the final steps will be:
1.  Verify all existing ES6 tests pass.
2.  Remove the remaining hardcoded "ladder" of JS primitives in `EmitEs6.lean`, as they are now fully driven by the attribute.
3.  Ensure the `.extern.js` sidecar file generation remains functional for functions that are *not* inlined.



# My request to change

I dont like that we replaced

-@[extern "lean_uint32_dec_le", implicit_reducible, js_extern_inlined (JS.le (JS.arg 0) (JS.arg 1))]
to

+@[extern "lean_uint32_dec_le", implicit_reducible, js_extern_inlined Lean.Compiler.JS.Impl.uint32DecLe]


and now we have to match by these functions names

+def resolveBuiltinJsExternInlined? : Name → Option JS.JsInlineExpr
+  | ``Lean.Compiler.JS.Impl.isScalarObj => some JS.Impl.isScalarObj

My idea was to write
@[extern "lean_uint32_dec_le", implicit_reducible, js_extern_inlined (JS.le (JS.arg 0) (JS.arg 1))]
  def UInt32.decLe (a b : UInt32) : Decidable (LE.le a b) :=


and then when we get the full name of function Init.Prelude.UInt32.decLe we find it in the Map of registered
inlined js implmeentations (HashMap FullFunctionName JsInlineExpr)
---
another idea (not ideal, if not possible to do by full lean function name as above) is to repeat the unique
extern id of function

@[extern "lean_uint32_dec_le", implicit_reducible, js_extern_inlined "lean_uint32_dec_le" (JS.le (JS.arg 0)
(JS.arg 1))]


# current state

CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" - ok


 ~/projects/lean4  ⇅ js ±✚  ./tests/es6/gen_expected_output.sh && CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" test ARGS="-R es6"
  CaseBoolean ... OK
  ...
make: Entering directory '/home/srghma/projects/lean4/build/release'
...
Compiling to JS
Running with Node
file:///home/srghma/projects/lean4/tests/es6/InlineCase01.lean.js:22
    const __uniq$7 = __uniq$2(__uniq$3._1);
                     ^

TypeError: __uniq$2 is not a function
    at maybe_u39_$__redArg (file:///home/srghma/projects/lean4/tests/es6/InlineCase01.lean.js:22:22)
    at test5$__redArg (file:///home/srghma/projects/lean4/tests/es6/InlineCase01.lean.js:26:97)
    at file:///home/srghma/projects/lean4/tests/es6/InlineCase01.lean.js:27:33
    at ModuleJob.run (node:internal/modules/esm/module_job:343:25)
    at async onImport.tracePromise.__proto__ (node:internal/modules/esm/loader:665:26)
    at async asyncRunEntryPointWithESMLoader (node:internal/modules/run_main:117:5)

Node.js v22.22.2
TEST FAILED: Failed to run InlineCase01.lean.js with Node

...
Compiling to JS
Running with Node
file:///home/srghma/projects/lean4/src/Init/System/IO.js:219
    const res = ma();
                ^

TypeError: ma is not a function
    at bind (file:///home/srghma/projects/lean4/src/Init/System/IO.js:219:17)
    at loop (file:///home/srghma/projects/lean4/src/Init/Data/List/Control.js:34:12)
    at List$forIn_u39_$loop$__redArg (file:///home/srghma/projects/lean4/src/Init/Data/List/Control.js:42:10)
    at diffWithIxE$__redArg (file:///home/srghma/projects/lean4/tests/es6/HalogenVDomST02.lean.js:115:23)
    at main (file:///home/srghma/projects/lean4/tests/es6/HalogenVDomST02.lean.js:346:20)
    at file:///home/srghma/projects/lean4/tests/es6/HalogenVDomST02.lean.js:372:1
    at ModuleJob.run (node:internal/modules/esm/module_job:343:25)
    at async onImport.tracePromise.__proto__ (node:internal/modules/esm/loader:665:26)
    at async asyncRunEntryPointWithESMLoader (node:internal/modules/run_main:117:5)

Node.js v22.22.2
TEST FAILED: Failed to run HalogenVDomST02.lean.js with Node

        Start 360: es6/EffectUnsafe01.lean
 15/173 Test #443: es6/STLoops02.lean .................................   Passed    0.61 sec
        Start 420: es6/PrimOpIntBit01.lean
 16/173 Test #376: es6/HalogenVDomST01.lean ...........................***Failed    0.67 sec
Compiling to JS
Running with Node
file:///home/srghma/projects/lean4/src/Init/System/IO.js:219
    const res = ma();
                ^

TypeError: ma is not a function
    at bind (file:///home/srghma/projects/lean4/src/Init/System/IO.js:219:17)
    at loop (file:///home/srghma/projects/lean4/src/Init/Data/List/Control.js:34:12)
    at List$forIn_u39_$loop$__redArg (file:///home/srghma/projects/lean4/src/Init/Data/List/Control.js:42:10)
    at diffWithIxE$__redArg (file:///home/srghma/projects/lean4/tests/es6/HalogenVDomST01.lean.js:116:23)
    at main (file:///home/srghma/projects/lean4/tests/es6/HalogenVDomST01.lean.js:409:20)
    at file:///home/srghma/projects/lean4/tests/es6/HalogenVDomST01.lean.js:435:1
    at ModuleJob.run (node:internal/modules/esm/module_job:343:25)
    at async onImport.tracePromise.__proto__ (node:internal/modules/esm/loader:665:26)
    at async asyncRunEntryPointWithESMLoader (node:internal/modules/run_main:117:5)

Node.js v22.22.2
TEST FAILED: Failed to run HalogenVDomST01.lean.js with Node

...
145/173 Test #383: es6/InlineCase02.lean ..............................***Failed    0.49 sec
Compiling to JS
Running with Node
file:///home/srghma/projects/lean4/tests/es6/InlineCase02.lean.js:9
    const __uniq$5 = __uniq$2(__uniq$3._1);
                     ^

TypeError: __uniq$2 is not a function
    at maybe$__redArg (file:///home/srghma/projects/lean4/tests/es6/InlineCase02.lean.js:9:22)
    at test2$__redArg (file:///home/srghma/projects/lean4/tests/es6/InlineCase02.lean.js:14:98)
    at file:///home/srghma/projects/lean4/tests/es6/InlineCase02.lean.js:20:33
    at ModuleJob.run (node:internal/modules/esm/module_job:343:25)
    at async onImport.tracePromise.__proto__ (node:internal/modules/esm/loader:665:26)
    at async asyncRunEntryPointWithESMLoader (node:internal/modules/run_main:117:5)

Node.js v22.22.2
TEST FAILED: Failed to run InlineCase02.lean.js with Node

...
158/173 Test   #2: tests/lake/examples/es6/test.sh ....................***Failed    4.24 sec
+ LAKE=lake
+ ./clean.sh
+ lake -d app build -v
info: app: no previous manifest, creating one from scratch
trace: app: updating 'ffi' with {}
info: toolchain not updated; no toolchain information found
warning: ffi: ignoring missing manifest:
  /home/srghma/projects/lean4/tests/lake/examples/es6/lib/lake-manifest.json
✔ [0/1] Ran app:extraDep
✔ [1/11] Ran job computation
✔ [2/11] Ran ffi:extraDep
ℹ [3/11] Built FFI.Static (376ms)
trace: .> LEAN_PATH=/home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean:/home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/lib/lean /home/srghma/projects/lean4/build/release/stage1/bin/lean /home/srghma/projects/lean4/tests/lake/examples/es6/lib/FFI/Static.l
ean -o /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean/FFI/Static.olean -i /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean/FFI/Static.ilean -c /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Static.c --setup /home/s
rghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Static.setup.json --json
ℹ [4/11] Built FFI.Shared (317ms)
trace: .> LEAN_PATH=/home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean:/home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/lib/lean /home/srghma/projects/lean4/build/release/stage1/bin/lean /home/srghma/projects/lean4/tests/lake/examples/es6/lib/FFI/Shared.l
ean -o /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean/FFI/Shared.olean -i /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean/FFI/Shared.ilean -c /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Shared.c --setup /home/s
rghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Shared.setup.json --json
ℹ [5/11] Built FFI.Shared:c.o (with exports) (134ms)
trace: .> /nix/store/4hkbjiddn4apfpdbi4ml2x43bwz71qvk-clang-wrapper-19.1.7/bin/clang -c -o /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Shared.c.o.export /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Shared.c -I /home/srghma/projects/lean4/b
uild/release/stage1/include -fstack-clash-protection -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden -Wno-unused-command-line-argument -O3 -DNDEBUG -DLEAN_EXPORTING
ℹ [6/11] Built FFI.Static:c.o (with exports) (197ms)
trace: .> /nix/store/4hkbjiddn4apfpdbi4ml2x43bwz71qvk-clang-wrapper-19.1.7/bin/clang -c -o /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Static.c.o.export /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI/Static.c -I /home/srghma/projects/lean4/b
uild/release/stage1/include -fstack-clash-protection -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden -Wno-unused-command-line-argument -O3 -DNDEBUG -DLEAN_EXPORTING
ℹ [7/11] Built FFI (380ms)
trace: .> LEAN_PATH=/home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean:/home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/lib/lean /home/srghma/projects/lean4/build/release/stage1/bin/lean /home/srghma/projects/lean4/tests/lake/examples/es6/lib/FFI.lean -o
/home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean/FFI.olean -i /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean/FFI.ilean -c /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI.c --setup /home/srghma/projects/lean4/tests/l
ake/examples/es6/lib/.lake/build/ir/FFI.setup.json --json
ℹ [8/11] Built FFI:c.o (with exports) (156ms)
trace: .> /nix/store/4hkbjiddn4apfpdbi4ml2x43bwz71qvk-clang-wrapper-19.1.7/bin/clang -c -o /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI.c.o.export /home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/ir/FFI.c -I /home/srghma/projects/lean4/build/release/s
tage1/include -fstack-clash-protection -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden -Wno-unused-command-line-argument -O3 -DNDEBUG -DLEAN_EXPORTING
ℹ [9/11] Built Main (405ms)
trace: .> LEAN_PATH=/home/srghma/projects/lean4/tests/lake/examples/es6/lib/.lake/build/lib/lean:/home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/lib/lean /home/srghma/projects/lean4/build/release/stage1/bin/lean /home/srghma/projects/lean4/tests/lake/examples/es6/app/Main.lean -o
 /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/lib/lean/Main.olean -i /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/lib/lean/Main.ilean -c /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/ir/Main.c --setup /home/srghma/projects/lean4/tes
ts/lake/examples/es6/app/.lake/build/ir/Main.setup.json --json
ℹ [10/11] Built Main:c.o (with exports) (161ms)
trace: .> /nix/store/4hkbjiddn4apfpdbi4ml2x43bwz71qvk-clang-wrapper-19.1.7/bin/clang -c -o /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/ir/Main.c.o.export /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/ir/Main.c -I /home/srghma/projects/lean4/build/release
/stage1/include -fstack-clash-protection -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden -Wno-unused-command-line-argument -O3 -DNDEBUG -DLEAN_EXPORTING
✖ [11/11] Building app:exe (521ms)
trace: .> /nix/store/4hkbjiddn4apfpdbi4ml2x43bwz71qvk-clang-wrapper-19.1.7/bin/clang -o /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/bin/app @/home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/bin/app.rsp
info: stderr:
ld.lld: error: undefined symbol: my_add
>>> referenced by Main.c
>>>               /home/srghma/projects/lean4/tests/lake/examples/es6/app/.lake/build/ir/Main.c.o.export:(_init_lp_app_main___closed__1)
clang: error: linker command failed with exit code 1 (use -v to see invocation)
error: external command '/nix/store/4hkbjiddn4apfpdbi4ml2x43bwz71qvk-clang-wrapper-19.1.7/bin/clang' exited with code 1
Some required targets logged failures:
- app:exe
error: build failed

....

97% tests passed, 5 tests failed out of 173

Label Time Summary:
es6    =  83.50 sec*proc (172 tests)

Total Test time (real) =   6.15 sec

The following tests FAILED:
         2 - tests/lake/examples/es6/test.sh (Failed)
        376 - es6/HalogenVDomST01.lean (Failed)                 es6
        377 - es6/HalogenVDomST02.lean (Failed)                 es6
        382 - es6/InlineCase01.lean (Failed)                    es6
        383 - es6/InlineCase02.lean (Failed)                    es6
Errors while running CTest
make[4]: *** [Makefile:71: test] Error 8
make[3]: *** [CMakeFiles/test.dir/build.make:70: CMakeFiles/test] Error 2
make[2]: *** [CMakeFiles/Makefile2:479: CMakeFiles/test.dir/all] Error 2
make[1]: *** [CMakeFiles/Makefile2:486: CMakeFiles/test.dir/rule] Error 2
make: *** [Makefile:299: test] Error 2
make: Leaving directory '/home/srghma/projects/lean4/build/release'


-----

# Gemini ai generated this but it was incorrect

diff --git a/src/Lean/Compiler/LCNF/EmitEs6.lean b/src/Lean/Compiler/LCNF/EmitEs6.lean
index bb90fdf9a4..08310384f3 100644
--- a/src/Lean/Compiler/LCNF/EmitEs6.lean
+++ b/src/Lean/Compiler/LCNF/EmitEs6.lean
@@ -17,9 +17,6 @@ import Lean.Compiler.InitAttr
 import Lean.Compiler.LCNF.Types
 import Lean.Compiler.JsExternInlinedAttr
 import Lean.Util.Path
-import Lean.Elab.Eval
-import Lean.Elab.Term
-import Lean.Meta.Eval

 namespace Lean.Compiler.LCNF

@@ -205,26 +202,34 @@ def isBoxedConstJsName (name : String) : Bool :=
 def isLikelyImpureJsName (_name : String) : Bool :=
   false

+def getLCtx : EmitM pu LCNF.LCtx := do
+  let s ← liftM (m := LCNF.CompilerM) get
+  return s.lctx

-def isRuntimeParamType (type : Expr) : Bool :=
+
+def isRuntimeParamType (lctx : LCNF.LCtx) (type : Expr) : Bool :=
   let type := type.headBeta
-  let _ := dbgTrace s!"isRuntimeParamType: {type}" fun _ => ()
-  if type.isAppOf ``lcErased || type.isAppOf ``lcAny || type.isAppOf ``lcVoid || maybeTypeFormerType type || isPredicateType type then
+  if type.isErased || isPredicateType type then
     false
   else
     match type.getAppFn with
+    | .sort .. => false
     | .const n .. =>
       let s := n.toString
-      !(s == "PUnit" || s == "Unit" || s == "Lean.PUnit" || s == "Lean.Unit" ||
-        s == "Void" || s == "Lean.Void" || s.endsWith ".Void" ||
-        s.contains "RealWorld" || s == "lcAny" || s == "lcVoid")
+      -- RealWorld and lcVoid are filtered to maintain the thunk-based IO model.
+      s != "RealWorld" && s != "Lean.RealWorld" && n != ``lcVoid
+    | .fvar fvarId =>
+      if let some decl := lctx.find? fvarId then
+        isTypeFormerType (Lean.Compiler.LCNF.LetDecl.type decl)
+      else
+        false
     | _ => true

-partial def getRuntimeArrowArity (type : Expr) : Nat :=
+partial def getRuntimeArrowArity (lctx : LCNF.LCtx) (type : Expr) : Nat :=
   match type.headBeta with
   | .forallE _ d b _ =>
-    let rest := getRuntimeArrowArity b
-    if isRuntimeParamType d then rest + 1 else rest
+    let rest := getRuntimeArrowArity lctx b
+    if isRuntimeParamType lctx d then rest + 1 else rest
   | _ => 0

 partial def isEffectResultType (type : Expr) : Bool :=
@@ -238,41 +243,59 @@ partial def isEffectResultType (type : Expr) : Bool :=
         s == "Real" || s.endsWith "RealWorld" || s.contains "RealWorld" || s.contains "IO" || s.contains "ST"
     | _ => false

-def getVisibleRuntimeArrowArity (type : Expr) : Nat :=
-  let arity := getRuntimeArrowArity type
+def getVisibleRuntimeArrowArity (lctx : LCNF.LCtx) (type : Expr) : Nat :=
+  let arity := getRuntimeArrowArity lctx type
   if isEffectResultType type && arity > 0 then
     arity - 1
   else
     arity

-def getVisibleRuntimeParams (type : Expr) (params : Array (Param .impure)) : Array (Param .impure) :=
-  let params := params.filter fun p => isRuntimeParamType p.type
+def getVisibleRuntimeParams (lctx : LCNF.LCtx) (type : Expr) (params : Array (Param .impure)) : Array (Param .impure) :=
+  let params := params.filter fun p => isRuntimeParamType lctx (_root_.Lean.Compiler.LCNF.Param.type (pu := .impure) p)
   if isEffectResultType type && !params.isEmpty then
     params.pop
   else
     params

 partial def getArity (n : Name) : EmitM pu Nat := do
+  let lctx ← getLCtx
   if let some decl ← getLocalImpureDecl? n then
-    return decl.params.size
+    return decl.params.foldl (init := 0) fun acc p =>
+      let ty : Expr := (Lean.Compiler.LCNF.Param.type p)
+      if isRuntimeParamType lctx ty then acc + 1 else acc
   else if let some sig ← getImpureSignature? n then
-    return sig.params.size
+    return sig.params.foldl (init := 0) fun acc p =>
+      let ty : Expr := (Lean.Compiler.LCNF.Param.type p)
+      if isRuntimeParamType lctx ty then acc + 1 else acc
   else
     let env ← getEnv
     if let some cinfo := env.find? n then
-      return cinfo.type.getForallArity
+      let ty : Expr := (ConstantInfo.type cinfo)
+      return getVisibleRuntimeArrowArity lctx ty
     else
-      if n.getString! == "_redArg" then
+      if n.isStr && n.getString! == "_redArg" then
         getArity n.getPrefix
       else
         if let some ty ← try some <$> liftM (LCNF.getType { name := n }) catch _ => pure none then
-          return getVisibleRuntimeArrowArity ty
+          return getVisibleRuntimeArrowArity lctx ty
         else
           return 0

-def getLCtx : EmitM pu LCtx := do
-  let s ← liftM (get : CompilerM LCNF.CompilerM.State)
-  return s.lctx
+def getRuntimeArity (n : Name) : EmitM pu Nat := do
+  let lctx ← getLCtx
+  if n == (← get).mainModName ++ `main then return 0
+  if let some decl ← getLocalImpureDecl? n then
+    return decl.params.foldl (init := 0) fun acc p =>
+      let ty : Expr := (Lean.Compiler.LCNF.Param.type p)
+      if isRuntimeParamType lctx ty then acc + 1 else acc
+  else if let some sig ← getImpureSignature? n then
+    return sig.params.foldl (init := 0) fun acc p =>
+      let ty : Expr := (Lean.Compiler.LCNF.Param.type p)
+      if isRuntimeParamType lctx ty then acc + 1 else acc
+  else if let some ty ← try some <$> liftM (LCNF.getType { name := n }) catch _ => pure none then
+    return getVisibleRuntimeArrowArity lctx ty
+  else
+    return ← getArity n

 def getVarName (fvarId : FVarId) : EmitM pu String := do
   return mangleString fvarId.name.toString
@@ -281,11 +304,12 @@ def isRedundantArg (a : Arg pu) : EmitM pu Bool := do
   match a with
   | .erased | .type .. => return true
   | .fvar fvarId =>
+    let lctx ← getLCtx
     let type ← try
       liftM <| LCNF.getType fvarId
     catch _ =>
       return false
-    return !isRuntimeParamType type
+    return !isRuntimeParamType lctx type

 def filterRedundantArgs (args : Array (Arg .impure)) : EmitM .impure (Array (Arg .impure)) :=
   args.filterM fun a => do return !(← isRedundantArg a)
@@ -864,40 +888,33 @@ def mkDynamicClosureFromLength (fnExpr : JsExpr) (supplied : Array JsExpr) : JsE
   let mkArrow (params : Array String) : JsExpr :=
     let extra := params.map JsExpr.ident
     JsExpr.arrow params #[JsStmt.return (JsExpr.call fnExpr (supplied ++ extra))]
-  -- diff === 0: all supplied args cover the function arity; wrap in zero-arg thunk
-  -- so the result is still a callable closure (e.g. for use as `cond` in whileE)
-  JsExpr.cond (JsExpr.binary diff "===" (JsExpr.litNum "0")) (mkArrow #[])
+  let closure := JsExpr.cond (JsExpr.binary diff "<=" (JsExpr.litNum "0")) (JsExpr.call fnExpr supplied)
     (JsExpr.cond (JsExpr.binary diff "===" (JsExpr.litNum "1")) (mkArrow #["x_1"])
       (JsExpr.cond (JsExpr.binary diff "===" (JsExpr.litNum "2")) (mkArrow #["x_1", "x_2"]) (mkArrow #["x_1", "x_2", "x_3"])))
-
-def mkResultClosureFromSupplied (resultType : Expr) (supplied : Array JsExpr) (k : Array JsExpr → JsExpr) : JsExpr :=
-  let resultArity := getRuntimeArrowArity resultType
-  if isEffectResultType resultType && resultArity == 1 then
-    JsExpr.arrowEffectful #[] #[JsStmt.return (k supplied)]
-  else
-    mkClosureFromSupplied resultArity supplied k
-
-def getRuntimeArity (n : Name) : EmitM .impure Nat := do
-  if n == (← get).mainModName ++ `main then return 1
-  if let some decl ← getLocalImpureDecl? n then
-    return decl.params.foldl (init := 0) fun acc p => if isRuntimeParamType p.type then acc + 1 else acc
-  else if let some sig ← getImpureSignature? n then
-    return sig.params.foldl (init := 0) fun acc p => if isRuntimeParamType p.type then acc + 1 else acc
-  else if let some ty ← try some <$> liftM (LCNF.getType { name := n }) catch _ => pure none then
-    return getVisibleRuntimeArrowArity ty
-  else
-    return ← getArity n
+  JsExpr.cond (JsExpr.binary (JsExpr.unary "typeof " fnExpr) "===" (JsExpr.litStr "function"))
+    closure
+    fnExpr

 def getKnownFVarArity? (fvarId : FVarId) : EmitM .impure (Option Nat) := do
+  let lctx ← getLCtx
   if let some decl ← liftM <| findFunDecl? (pu := .impure) fvarId then
-    return some <| decl.params.foldl (init := 0) fun acc p => if isRuntimeParamType p.type then acc + 1 else acc
+    return some <| decl.params.foldl (init := 0) fun acc (p : LCNF.Param .impure) => if isRuntimeParamType lctx ((_root_.Lean.Compiler.LCNF.Param.type p)) then acc + 1 else acc
   else
     try
       let type ← liftM <| LCNF.getType fvarId
-      return some <| getRuntimeArrowArity type
+      return some <| getRuntimeArrowArity lctx type
     catch _ =>
       return none

+def mkResultClosureFromSupplied (resultType : Expr) (supplied : Array JsExpr) (k : Array JsExpr → JsExpr) : EmitM .impure JsExpr := do
+  let lctx ← getLCtx
+  let resultArity := getRuntimeArrowArity lctx resultType
+  if isEffectResultType resultType && resultArity == 0 then
+    return JsExpr.arrow #[] #[JsStmt.return (k supplied)]
+  else
+    return mkClosureFromSupplied resultArity supplied k
+
+
 partial def toEmitJsExpr (e : JsInlineExpr) (args : Array JsExpr) : JsExpr :=
   match e with
   | .identifier name => .ident name
@@ -1194,6 +1211,8 @@ def mkCallLikeExpr (fnName : Name) (rawArgs : Array (Arg .impure)) : EmitM .impu
     return ← mkNamedCall jsName

 partial def mkLetValueExpr (v : LetValue .impure) (resultType? : Option Expr := none) : EmitM .impure JsExpr := do
+  if let some t := resultType? then
+    dbg_trace s!"mkLetValueExpr resultType: {t} isForall: {t.isForall}"
   let expr ← match v with
     | .lit (.nat n) => pure <| JsExpr.litNum (toString n)
     | .lit (.str s) => pure <| JsExpr.litStr s
@@ -1205,38 +1224,25 @@ partial def mkLetValueExpr (v : LetValue .impure) (resultType? : Option Expr :=
     | .const declName _ fnArgs _ => mkCallLikeExpr declName fnArgs
     | .fvar fvarId fnArgs =>
       let args ← mkArgsExprs fnArgs
-      if !fnArgs.isEmpty then
-        let expr := JsExpr.ident (← getVarName fvarId)
-        if let some resultType := resultType? then
-          let resultArity := getRuntimeArrowArity resultType
-          if resultArity > 0 then
-            pure <| mkResultClosureFromSupplied resultType #[] fun restArgs => JsExpr.call expr (args ++ restArgs)
-          else if let some arity ← getKnownFVarArity? fvarId then
-            if args.size < arity then
-              pure <| mkDynamicClosureFromLength expr args
-            else
-              pure <| JsExpr.call expr args
-          else
-            pure <| JsExpr.call expr args
-        else if let some arity ← getKnownFVarArity? fvarId then
-          if args.size < arity then
-            pure <| mkDynamicClosureFromLength expr args
-          else
-            pure <| JsExpr.call expr args
+      let expr := JsExpr.ident (← getVarName fvarId)
+      let arity? ← getKnownFVarArity? fvarId
+      match arity? with
+      | some arity =>
+        if arity > 0 && args.size < arity then
+          pure <| mkDynamicClosureFromLength expr args
         else
-          pure <| JsExpr.call expr args
-      else
-        if let some letDecl ← liftM <| findLetDecl? (pu := .impure) fvarId then
-          match letDecl.value with
-          | .const declName _ #[] _ =>
-            if (← getArity declName) == 0 && !isClosedName declName then
-              pure <| JsExpr.call (JsExpr.ident (← toJsName declName)) #[]
+          let call := JsExpr.call expr args
+          if let some rt := resultType? then
+            let lctx ← getLCtx
+            if isEffectResultType rt && getRuntimeArrowArity lctx rt == 0 then
+              pure <| JsExpr.arrow #[] #[JsStmt.return call]
             else
-              pure <| JsExpr.ident (← getVarName fvarId)
-          | _ =>
-            pure <| JsExpr.ident (← getVarName fvarId)
-        else
-          pure <| JsExpr.ident (← getVarName fvarId)
+              pure <| call
+          else
+            pure <| call
+      | none =>
+        -- Unknown arity (e.g. parameter). Use dynamic closure.
+        pure <| mkDynamicClosureFromLength expr args
     | .fap fn fnArgs _ | .pap fn fnArgs _ =>
       mkCallLikeExpr fn fnArgs
     | .ctor info ctorArgs _ =>
@@ -1251,8 +1257,9 @@ partial def mkLetValueExpr (v : LetValue .impure) (resultType? : Option Expr :=
         pure <| JsExpr.object fields
     | .proj _ i fvarId ..
     | .oproj i fvarId ..
-    | .uproj i fvarId .. =>
-      pure <| JsExpr.prop (JsExpr.ident (← getVarName fvarId)) s!"_{i+1}"
+    | .uproj i fvarId .. => do
+      let expr := JsExpr.prop (JsExpr.ident (← getVarName fvarId)) s!"_{i+1}"
+      pure <| mkDynamicClosureFromLength expr #[]
     | .sproj i offset fvarId .. =>
       pure <| JsExpr.prop (JsExpr.ident (← getVarName fvarId)) s!"_{i + offset + 1}"
     | .reuse _ info _ reuseArgs _ =>
@@ -1280,7 +1287,8 @@ partial def mkTailRecursiveJump? (decl : LetDecl .impure) (k : Code .impure) : E
   | .return fvarId, .fap declName args _ =>
     if fvarId == decl.fvarId && declName == currentDecl.name then
       let args ← filterRedundantArgs args
-      let params := currentDecl.params.filter fun (p : Param .impure) => isRuntimeParamType p.type
+      let lctx ← getLCtx
+      let params := currentDecl.params.filter fun (p : Param .impure) => isRuntimeParamType lctx ((_root_.Lean.Compiler.LCNF.Param.type p))
       let mut stmts := #[]
       for i in [:args.size] do
         stmts := stmts.push <| JsStmt.const s!"_tmp_{i}" (← mkArgExpr args[i]!)
@@ -1304,7 +1312,8 @@ partial def mkCode (code : Code .impure) : EmitM .impure (Array JsStmt) := do
       if let some stmts ← mkTailRecursiveJump? decl k then
         modify fun s => { s with knownBools := oldKnown }
         return optimizeStmts stmts
-      let stmt := JsStmt.const (← getVarName decl.fvarId) (← mkLetValueExpr decl.value (some decl.type))
+      let ty : Expr := LetDecl.type decl
+      let stmt := JsStmt.const (← getVarName decl.fvarId) (← mkLetValueExpr decl.value (some ty))
       let rest ← mkCode k
       modify fun s => { s with knownBools := oldKnown }
       return #[stmt] ++ rest
@@ -1335,7 +1344,17 @@ partial def mkCode (code : Code .impure) : EmitM .impure (Array JsStmt) := do
         else
           return optimizeStmts <| #[JsStmt.block body]
       | none =>
-        return #[JsStmt.return (JsExpr.call (JsExpr.ident (← getVarName fvarId)) (← mkArgsExprs args))]
+        let args ← mkArgsExprs args
+        let expr := JsExpr.ident (← getVarName fvarId)
+        let arity? ← getKnownFVarArity? fvarId
+        match arity? with
+        | some arity =>
+          if arity > 0 && args.size < arity then
+            return #[JsStmt.return (mkDynamicClosureFromLength expr args)]
+          else
+            return #[JsStmt.return (JsExpr.call expr args)]
+        | none =>
+          return #[JsStmt.return (mkDynamicClosureFromLength expr args)]
     | .jp decl k => do
       modifyLCtx fun lctx => lctx.addFunDecl decl
       modify fun s => { s with joinPoints := s.joinPoints.insert decl.fvarId decl }
@@ -1345,11 +1364,14 @@ partial def mkCode (code : Code .impure) : EmitM .impure (Array JsStmt) := do
       let oldLCtx ← getLCtx
       for p in decl.params do
         modifyLCtx fun lctx => lctx.addParam p
-      let params := decl.params.filter fun p => isRuntimeParamType p.type
+        let _ ← getVarName p.fvarId
+      let lctx ← getLCtx
+      let params := decl.params.filter fun (p : LCNF.Param .impure) => isRuntimeParamType lctx ((_root_.Lean.Compiler.LCNF.Param.type p))
       let paramNames ← params.mapM fun p => getVarName p.fvarId
       let valueBody ← mkCode decl.value
+      let ty : Expr := decl.type
       let value :=
-        if isEffectResultType decl.type then
+        if isEffectResultType ty then
           JsExpr.arrowEffectful paramNames valueBody
         else
           JsExpr.arrow paramNames valueBody
@@ -1410,7 +1432,13 @@ partial def mkCode (code : Code .impure) : EmitM .impure (Array JsStmt) := do
           let oldLCtx ← getLCtx
           for p in params do
             modifyLCtx fun lctx => lctx.addParam p
-          let body ← mkCode k
+            let _ ← getVarName p.fvarId
+          let lctx ← getLCtx
+          let params := params.filter fun (p : LCNF.Param .impure) => isRuntimeParamType lctx ((_root_.Lean.Compiler.LCNF.Param.type p))
+          let mut body := #[]
+          for i in [:params.size] do
+            body := body.push <| JsStmt.const (← getVarName params[i]!.fvarId) (JsExpr.prop discr s!"_{i+1}")
+          body := body ++ (← mkCode k)
           modifyLCtx fun _ => oldLCtx
           currentElse := mkBlock body
         | .default k =>
@@ -1433,7 +1461,9 @@ partial def mkCode (code : Code .impure) : EmitM .impure (Array JsStmt) := do
           let oldLCtx ← getLCtx
           for p in params do
             modifyLCtx fun lctx => lctx.addParam p
-          let params := params.filter fun (p : Param .impure) => isRuntimeParamType p.type
+            let _ ← getVarName p.fvarId -- Initialize name sequentially
+          let lctx ← getLCtx
+          let params := params.filter fun (p : Param .impure) => isRuntimeParamType lctx ((_root_.Lean.Compiler.LCNF.Param.type p))
           let mut body := #[]
           for i in [:params.size] do
             body := body.push <| JsStmt.const (← getVarName params[i]!.fvarId) (JsExpr.prop discr s!"_{i+1}")
@@ -1472,20 +1502,23 @@ def mkDecl? (decl : Decl .impure) : EmitM .impure (Option JsDecl) := do
     modify fun s => { s with currentDecl? := some decl, knownBools := {}, joinPoints := {} }
     for p in decl.params do
       modifyLCtx fun lctx => lctx.addParam p
+      let _ ← getVarName p.fvarId
+    let lctx ← getLCtx
     let exportName ← toJsName decl.name
     let isRecursive := hasTailRecursiveCall decl.name code
-    let params := decl.params.filter fun p => isRuntimeParamType p.type
+    let params := decl.params.filter fun p => isRuntimeParamType lctx (Lean.Compiler.LCNF.Param.type (pu := .impure) p)
     let paramNames ← params.mapM fun p => do
       let name ← getVarName p.fvarId
-      return s!"/* {p.type} */ {name}"
+      return s!"/* {Lean.Compiler.LCNF.Param.type (pu := .impure) p} */ {name}"
     let body ← mkCode code
     let body := if isRecursive then #[JsStmt.whileTrue body] else body
+      let ty : Expr := decl.type
       let value :=
         if params.isEmpty && isClosedName decl.name then
           match stmtsToExpr? body with
           | some expr => expr
           | none => JsExpr.call (JsExpr.paren (JsExpr.arrow #[] body)) #[]
-      else if isEffectResultType decl.type then
+      else if isEffectResultType ty then
         JsExpr.arrowEffectful paramNames body
       else
         JsExpr.arrow paramNames body


-----

# Also, I want to implement macros system for js_extern_inlined

something like

```
-- Step 1: declare a syntax category for JS inline expressions
declare_syntax_cat js_inline_expr

-- Terminals
syntax num : js_inline_expr              -- 42
syntax "#" noWs num : js_inline_expr     -- #0, #1, #2 (arg references)
syntax str : js_inline_expr              -- "hello"

-- Operators (low-to-high precedence, just like Lean's own)
syntax js_inline_expr " + "  js_inline_expr : js_inline_expr
syntax js_inline_expr " - "  js_inline_expr : js_inline_expr
syntax js_inline_expr " < "  js_inline_expr : js_inline_expr
syntax js_inline_expr " <= " js_inline_expr : js_inline_expr
syntax js_inline_expr " == " js_inline_expr : js_inline_expr

-- Property access: $0.length
syntax js_inline_expr noWs "." ident : js_inline_expr

-- Function call: new "Uint8Array" [#0]
syntax "new " str "[" js_inline_expr,* "]" : js_inline_expr

-- Step 2: macro to translate to JsInlineExpr terms
macro_rules
  | `(js_inline_expr| $n:num)         => `(JS.num $n)
  | `(js_inline_expr| $$($n:num))     => `(JS.arg $n)
  | `(js_inline_expr| $a < $b)        => `(JS.lt $(← expandJsExpr a) $(← expandJsExpr b))
  | `(js_inline_expr| $a.length)      => `(JS.property $(← expandJsExpr a) "length")
  | `(js_inline_expr| new $s:str [$args,*]) => ...

-- Step 3: attribute parser uses the new syntax category
syntax (name := js_extern_inlined) "js_extern_inlined " js_inline_expr : attr
```


should allow to write

```
@[js_extern_inlined #0 < $1]          -- → JS.lt (JS.arg 0) (JS.arg 1)
@[js_extern_inlined #0.length]        -- → JS.property (JS.arg 0) "length"
@[js_extern_inlined new Uint8Array(#0)]  -- → JS.new "Uint8Array" #[JS.arg 0]
```

I think we should check @src/Lean/Compiler/ExternAttr.lean on how to implement it correctly

-----

# Also, I saw You have added more ffi functions to src/**/*.js external files. I will describe what is the expected state
