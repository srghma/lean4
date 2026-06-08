I am trying to rewrite lean4 cpp implementation to rust.

we are rn at upstream/master + my changes

goal is:

```
1. stage0 is original cpp, just like in upstream/master. Never update it. It is using original cpp implementation and used to compile lean files into cpp code. we use stage0 to compile stage1.
  - check srghmascripts/order_of_review.md to get information about dependency tree of cpp/h files. Same level means that dependencies are parallel and can be reviewed in any order.
2. stage1 - this should have runtime of original cpp implementation (just like stage0), but here we should compile lean files not to cpp, but to rust. This is why I have removed EmitC and replaced it with EmitRust. But stage1 should not use ./src/rust/ yet which is/should be the port of original cpp directories `src/{kernel,util,shell,runtime,library,include,initialize}` (we want it but it is impossible at this stage, because src/rust/ probably has errors). This is why I have not yet removed original cpp directories.
3. stage2 - this is lean that should use rust port of original cpp + EmitRust too.
  - Rust should agressively replace c/cpp/h/hpp. No c/cpp/h/hpp files are allowed to be used. Because in future we want remove all c/cpp/h/hpp, completely from everywhere (should should not allow to use cpp even in 3d party plugins).

    - To achieve this we should use native rust libs:
        1. rm -rfd ./cadical -> use https://docs.rs/cadical-sys/latest/cadical_sys/ instead (it has same version)
        1. rm -rfd ./mimalloc -> dont use anything. we will use rust malloc instead
        1. replace libuv -> use https://github.com/bmatcuk/libuv-sys/ (libuv-sys2 = v1.52.2 which is libuv v1.52.2 too)
        1. <icu.h> -> https://github.com/google/rust_icu
        1. emscripten.h -> right now lets ignore this target. can disable tests. can remove emscripten support at all or comment functions to it
        1. zlib -> https://github.com/trifectatechfoundation/zlib-rs
        1. llvm-c -> llvm-sys (to load code produced by EmitLLVM)
        1. other deps that were originally in cpp (can check original cpp implementation at upstream/master):
          - Windows-specific APIs: <windows.h>, <psapi.h>, <bcrypt.h> (cryptography/entropy), and <ntdef.h>.
          - POSIX/Unix-specific APIs: <unistd.h>, <dlfcn.h> (dynamic loading), <dirent.h> (directory traversal), <pthread.h> (threading), and <link.h>.
          - Platform debugging: <execinfo.h> (for generating stack traces on Unix-like systems).
          -> for all of them - use rust native libs instead

    - Memory model (rc counting and etc) should not change.

  - Rust implementation is divided on lib (src/rust/lean_runtime. TODO: improve name) + executables.
    Executables are:
      - executables in ./src/rust. E.g. lean_shell. Maybe other should be ported. Check original cpp code.
      - there are also lean files that have entrypoint `def main`. For example in ./tests dir. (these test files should compile into rust.)
      - also tests use `#eval`. it should continue working during compilation and when using vscode-lean.

    We want to compile lib into cdynlib (as opposed to rlib/dynlib/staticlib. To allow `import MyModule; #eval MyModule.myFunction 5`.) In future, when all tests will pass, when we will rewrite on pure rust (no #[repr "C"], [extern "C"]. Inspired by src/rust/.still-nanoda/, which is unsutable for runtime bc there is no reference counting. but maybe can take some ideas from it.) - we will use stabby to still allow ABI-stability.


these tests should pass:
1. cd ./src/rust/lean_runtime/ && echo "cargo test -p lean_runtime" && cargo test -p lean_runtime && echo "cargo test -p lean_shell" && cargo test -p lean_shell && echo "cargo build -p lean_runtime" && cargo build -p lean_runtime && echo "cargo build -p lean_shell" && cargo build -p lean_shell
2. CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" test ARGS='-E bench/mvcgen/sym -R "elab/1921|elab/4306"' (I excluded bench/mvcgen/sym bc its olean files are stale, and selected two random tests) (uses stage1 cmake build — stage2 cmake build is not yet set up for the pure-Rust stage2. TODO: we should not test against stage0, stage1, we should test only against stage2 (rust runtime + cpp runtime))

When fixing issues in rust implementation - add rust unit tests.

NOTE that in path You have `nm`, `valgrind`, `xxhash-list` - these are tools for debugging. Use them.
```

dont change files in src/{kernel,util,shell,runtime,library,include,initialize}, bc these files should not affect our rust rewrite and will be removed
---

note errors like this

```
+lean: symbol lookup error: lean: undefined symbol: _ZN4core3str8converts9from_utf817h443dbfc000059306E
```

this problem is repeating often. and after each fix -> run again -> again new symbol. therefore many tokens are spent becuase of this ping-pong.
I have made make sh script to get all undefined symbols ./srghmascripts/check_symbols.sh. Can modifiy it if need

---

<!-- dont run CMAKE tests after `make -C build/release/stage1 clean-stdlib` and dont run all cmake tests at once. They take lot of time (10-20 min) and You will spend lots of tokens for watching for background task. Tell me. I will run myself -->

if You want to run CMAKE tests after `make -C build/release/stage1 clean-stdlib` or all cmake tests at once - dont run it as background task - run in foreground. Why? Because they take lot of time (10-20 min) and You will spend lots of tokens for watching for background task.

continue. very good job. You make rs files more pure by rewriting unsafe cpp-like code to rust-style while still preserving old cpp behavior, rc counting, memory model.

---

create a bash script (nixos) that will work on completely clean project (no ignored files):

1. check that stage0 is same as stage0 in upstream/master. if not - update stage0 to be same as stage0 in upstream/master.
2. create stage1
3. create stage2

----

I am worried that adding "get_loaded_libs" function is wrong, bc we want to use only rust libs from crate

Also I am worried that adding MpzObjectGmp and MpzObjectNonGmp is wrong too - doesnt it use c++ lib too instead of rust crate?


---------

Native Rust stdlib: per-package rlibs + proper use imports

Context

Replace the current include!-based 5-chunk lean_stdlib with a proper Rust crate structure
mirroring the C++ implementation. C++ produces libInit.a, libStd.a, libLean.a, libLake.a
(one per package). We do the same with rlibs: lean_init, lean_std, lean_lean, lean_lake.

Cargo builds them sequentially by dependency (lean_init → lean_std → lean_lean → lean_lake),
so only one rustc invocation runs at a time. Peak memory = memory of largest package.

Simultaneously, remove all extern "C" inter-module declarations and #[no_mangle] from
non-entry-point functions. Generated .rs files use use lean_PACKAGE::Mod::Path::* instead.
This mirrors how C++ .c files #include headers from other packages.

Risk: lean_lean has ~900 modules. With proper pub fn (not #[no_mangle] extern "C"),
rustc can eliminate dead code and avoids writing 900x~246 C symbols to the symbol table.
Likely lower memory than the current include! approach. Try it — fall back to sub-package
split if it OOMs.

---
File 1: src/Lean/Compiler/LCNF/EmitRust.lean

1a. Add package helper (new function, top-level)

def leanModuleToRustPackage (name : Name) : String :=
  let s := name.toString
  if s.startsWith "Init" then "lean_init"
  else if s.startsWith "Std"  then "lean_std"
  else if s.startsWith "Lean" then "lean_lean"
  else if s.startsWith "Lake" then "lean_lake"
  else "lean_runtime"

1b. emitFileHeader (line 268) — add use imports per import

After the existing emitLn "use lean_runtime::generated_abi::*;", add:

  let myPkg := leanModuleToRustPackage modName
  for imp in env.imports do
    let impPkg := leanModuleToRustPackage imp.module
    -- Build Rust path: Init.Data.List.Basic → Init::Data::List::Basic
    let rustPath := imp.module.components.map toString |>.intersperse "::" |>.foldl (· ++ ·) ""
    if impPkg == myPkg then
      emitLn s!"use crate::{rustPath}::*;"
    else
      emitLn s!"use {impPkg}::{rustPath}::*;"

env.imports is the same array already iterated at line 274 for the comment.

1c. emitFnDecls (line 566) — remove the extern "C" { } block

The entire extern "C" { ... } block (lines 566-582) that declares other-module functions
is no longer needed — those functions are now in scope via the use imports above.

Remove the emitLn "extern \"C\" {" ... emitLn "}" block.
The emitFnDecl/emitFnDeclAux calls for LOCAL functions (lines 584-587) stay unchanged
(they handle @[extern "name"] local functions).

1d. emitDecl (line 1142) — change function definition signature

Lines 1152-1154:
-- BEFORE
emit "#[no_mangle] pub unsafe extern \"C\" fn "
-- AFTER
emit "pub unsafe fn "
(Both branches of the if ps.isEmpty are identical, so change both.)

1e. Remove #[no_mangle] from statics

- Line 304: "#[no_mangle] pub static mut" → "pub static mut"
- Line 376: "#[no_mangle] pub static" → "pub static"
- Line 621: "#[no_mangle] pub static mut" → "pub static mut"

1f. Init functions: become pub unsafe fn

The emitInitFn at line 1247 emits #[no_mangle] pub unsafe extern "C" fn initialize_....
Change to pub unsafe fn initialize_....

The allExterns.forM block (lines 1374-1376) that declares dep init functions as extern "C"
can be removed entirely: dep init functions are now plain Rust pub unsafe fn and are
already in scope via the use crate::...::* / use lean_PACKAGE::...::* imports emitted
in step 1b. The init function body calls initialize_Dep(builtin) and that name resolves
through the glob imports — no extern declarations needed.

Summary of EmitRust changes

┌─────────────────────┬────────────────────────────────────────────────────┬──────────────────────────────────────────────┐
│        What         │                       Before                       │                    After                     │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ File header         │ use lean_runtime::generated_abi::*;                │ + use lean_PACKAGE::Mod::Path::*; per import │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Other-module decls  │ extern "C" { fn l_Mod_foo(); }                     │ removed                                      │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Dep init decls      │ extern "C" { fn initialize_Dep(u8); }              │ removed                                      │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Function definition │ #[no_mangle] pub unsafe extern "C" fn              │ pub unsafe fn                                │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Static definition   │ #[no_mangle] pub static mut                        │ pub static mut                               │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Init function       │ #[no_mangle] pub unsafe extern "C" fn initialize_M │ pub unsafe fn initialize_M                   │
├─────────────────────┼────────────────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Call sites          │ unchanged (bare name, already in scope)            │ unchanged                                    │
└─────────────────────┴────────────────────────────────────────────────────┴──────────────────────────────────────────────┘

Entry-point functions (main, _lean_main) keep #[no_mangle] pub unsafe extern "C" —
they are still called by the OS / lean_shell_main.
lean_shell_main also keeps #[no_mangle] extern "C" for now (Option A below).

---
File 2: setup.sh — replace 5-chunk workspace with 4-package workspace

Remove the section 5b/5c chunk generation. Replace with:

Package classification

declare -A PKG_FILES   # pkg_name → newline-separated list of .rs paths
for rs in "${ALL_RS_FILES[@]}"; do
  rel="${rs#$STAGE2_RS/}"
  case "$rel" in
    Init/*)  pkg="lean_init" ;;
    Std/*)   pkg="lean_std"  ;;
    Lean/*)  pkg="lean_lean" ;;
    Lake/*)  pkg="lean_lake" ;;
    *)       continue ;;   # Leanc.rs, LeanChecker.rs, LeanIR.rs handled as binaries
  esac
  PKG_FILES[$pkg]+="$rs"$'\n'
done

Per-package Cargo.toml deps

Dependencies follow the package DAG:
- lean_init: lean_runtime
- lean_std: lean_runtime, lean_init
- lean_lean: lean_runtime, lean_init, lean_std
- lean_lake: lean_runtime, lean_init, lean_std, lean_lean

Per-package lib.rs

Each package's lib.rs uses #[path] to point to generated files, organized into
the module hierarchy. Paths are relative from lean_PACKAGE/src/lib.rs:
../../../src/generated/Init/Prelude.rs
(lean_PACKAGE/src → lean_PACKAGE → lean_stdlib → stage2 → src/generated/…)

#![allow(warnings)]
pub mod Init {
    #[path = "../../../src/generated/Init/Prelude.rs"] pub mod Prelude;
    #[path = "../../../src/generated/Init/Core.rs"]    pub mod Core;
    pub mod Data {
        #[path = "../../../src/generated/Init/Data/List/Basic.rs"] pub mod Basic;
    }
}

setup.sh builds the nested pub mod tree by sorting paths and grouping by directory prefix.

Build order (sequential, respects DAG)

for pkg in lean_init lean_std lean_lean lean_lake; do
  cargo build --release -p "$pkg" --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"
done
cargo build --release -p lean_stdlib --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"

Workspace Cargo.toml

[workspace]
members = ["lean_init", "lean_std", "lean_lean", "lean_lake"]

[package]
name = "lean_stdlib"
crate-type = ["staticlib"]

[dependencies]
lean_runtime = { path = "../../../../src/rust/lean_runtime", features = ["export-runtime-ffi"] }
lean_init  = { path = "lean_init" }
lean_std   = { path = "lean_std" }
lean_lean  = { path = "lean_lean" }
lean_lake  = { path = "lean_lake" }

[profile.release]
opt-level = 1
codegen-units = 1
lto = false

---
File 3: src/rust/lean_shell/src/lib.rs

Option A (recommended for now): Keep lean_shell_main as
#[no_mangle] pub unsafe extern "C" fn in the generated Lean/Shell.rs (special-case
it or keep @[export] on it in Lean/Shell.lean). lean_shell's extern "C" call still works.
No change needed to lean_shell itself.

---
File 4: Test compilation (src/Leanc.lean)

Generated test .rs now contains use lean_init::... etc. rustc needs the rlibs.

Approach: Pass --extern flags for each package rlib. Add a new lean_runtime build var
LEAN_RUST_PACKAGE_RLIB_DIR (baked in via build.rs) pointing to $STAGE2_DIR/lib/lean/.
leanc runs:
rustc test.rs \
  --extern lean_runtime=.../liblean_runtime.rlib \
  --extern lean_init=.../liblean_init.rlib \
  --extern lean_std=.../liblean_std.rlib \
  --extern lean_lean=.../liblean_lean.rlib \
  --extern lean_lake=.../liblean_lake.rlib \
  -L .../lib/lean

---
Lib layout after build

Populate $STAGE2_DIR/lib/lean/:
liblean_runtime.rlib   (ABI stub, unchanged)
liblean_init.rlib
liblean_std.rlib
liblean_lean.rlib
liblean_lake.rlib
liblean_stdlib.a       (staticlib for binary link)

Copy from $LEAN_STDLIB_DIR/target/release/deps/lean_*.rlib.

---
Verification

# 1. Build lean_init alone (fast sanity check)
cargo build --release -p lean_init --manifest-path $BUILD/stage2/lean_stdlib/Cargo.toml

# 2. Full build
./setup.sh

# 3. Round-trip test
echo 'def main : IO Unit := IO.println "hello"' > /tmp/hello.lean
$BUILD/stage2/bin/lean --c=/tmp/hello.rs /tmp/hello.lean
$BUILD/stage2/bin/leanc -O3 -o /tmp/hello.out /tmp/hello.rs
/tmp/hello.out

# 4. CTest (user runs manually)
ctest --test-dir $BUILD/stage2 -j$(nproc) --output-on-failure -E bench

If lean_lean OOMs

Split Lean/* into semantic sub-packages by sub-namespace, e.g.:
- lean_lean_meta:  Lean/Meta/**
- lean_lean_elab:  Lean/Elab/**
- lean_lean_compiler: Lean/Compiler/**
- lean_lean_core: remaining Lean/**

Both leanModuleToRustPackage in EmitRust.lean and the classification in setup.sh use the
same mapping, so updating both in sync is sufficient.
