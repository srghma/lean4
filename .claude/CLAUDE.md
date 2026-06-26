We already rewritten cpp + h (that lived in `src/{kernel,util,shell,runtime,library,include,initialize}`) files to rust, now I want to do different tasks to improve code.

We are rn at origin/master + my changes

I did `mkdir -p origin-master-src && git archive origin/master:src/ | tar -x -C origin-master-src` so original cpp code is at now is at `./origin-master-src`. If You get error during porting - ALWAYS CHECK ORIGNAL CPP CODE FIRST. Our rust should just repeat cpp

How to run tests from AI? To preserve tokens stdoutput only Failures like `log="/tmp/lean4-test-output-$(date +%Y%m%d-%H%M%S).log"; set -o pipefail; CTEST_PARALLEL_LEVEL=$(nproc) make -C build/release test -j"$(nproc)" ARGS='-E bench/mvcgen/sym --timeout 240 --output-on-failure' 2>&1 | tee "$log" | grep -A5 -B20 -Ei 'fail(ed|ure)?|failure'; s=${PIPESTATUS[0]}; [ "$s" -eq 0 ] && git add -A && git commit -m 'feat: all tests pass' || { echo "Tests failed. Full log: $log"; exit "$s"; }` (or with `-R "..."'` to focus on some test or group of tests, e.g. `-R "elab"'`) (ignore `bench/mvcgen/sym` bc .olean files are deprecated). Use flag --timeout, one test cannot run more that 4 minutes.

NOTE: that `--quiet` flag makes `ctest` not output not only `Passed`, but `Failed` too, thus should not be used.

Can do `gaa && gc -m 'feat: all tests pass'` only if ALL tests have passed.

If want to run ALL tests - dont run, I will run myself (to preserve tokens), but before telling me that this is a time to run all tests - run 3-5 tests related to change to confirm that change doesnt break tests. NOTE: dont run whole groups of tests also (e.g. it bad to do `ARGS='-R "compiler|ir_interp|elab"` because too much tests), instead 3-5 tests (e.g. `ARGS='-R "compiler/testXXX|ir_interp/testXXX|elab/testXXX"`)

<!-- If want to run ALL tests - run only in background to preserve tokens (bc it will notify You, no need to recheck all the time) (to preserve tokens). can run all ctests Yourself, just make sure they output only failures to reduce number or tokens. Continue in automatic mode. Commit only after ALL tests have passed successfully. Commit message should contain short info about the change. -->

3. How kernel was rewritten? Since kernel depended on cpp exceptions and rust dont have them, we used Result<KernelException::X> approach instead of throwing of exceptions.

3. some tests may OOM - no problem, I am running `earlyoom` as daemon

4. info about over-free bug is in memory or at @.claude-acc2/projects/-home-srghma-projects-lean4/memory/kernel-type-checker-rs-refcount-bugs.md

5. additional regression harness is at `./srghmascripts/kernel_tc_suite.sh && ./srghmascripts/kernel_bulk_check.sh`

6. during porting we used TDD approach. made new tests (lean tests or bash scripts or rust tests)

7. Every time we do some change - we should should continue to consult original cpp implementation at `./origin-master-src`. RUST CODE SHOULD WORK SAME AS CPP!! (e.g. inc/dec should be same as in cpp)!!

----------

# Replace C Dependencies with Cargo Dependencies (Phase 1: mimalloc & libloading)

This plan replaces the C-compiled `mimalloc` and platform-specific dynamic loading (POSIX `dlopen` / Windows `LoadLibrary`) with their corresponding safe/standard Rust crates: `mimalloc` and `libloading`.

## Proposed Changes

### Cargo Dependencies

#### [MODIFY] [Cargo.toml](file:///home/srghma/projects/lean4/src/rust/lean_runtime/Cargo.toml)
- Add `mimalloc = "0.1"` dependency.
- Add `libloading = "0.8"` dependency.

### mimalloc Replacement

#### [MODIFY] [lib.rs](file:///home/srghma/projects/lean4/src/rust/lean_runtime/src/lib.rs)
- Wire `#[global_allocator] static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;` conditionally when `lean_has_mimalloc` is active.

#### [MODIFY] [CMakeLists.txt](file:///home/srghma/projects/lean4/CMakeLists.txt)
- Remove `FetchContent` download, configuration, and build setup of `mimalloc`.
- Keep `option(USE_MIMALLOC "use mimalloc" ON)` so that `lean_has_mimalloc` configuration can still be toggled.

#### [MODIFY] [CMakeLists.txt](file:///home/srghma/projects/lean4/src/CMakeLists.txt)
- Remove the `file(COPY ... mimalloc.h ...)` block.

#### [MODIFY] [CMakeLists.txt](file:///home/srghma/projects/lean4/src/runtime/CMakeLists.txt)
- Remove the compilation of `static.c` and inclusion of mimalloc directories when `USE_MIMALLOC` is true.
- Cargo will build, link, and export mimalloc automatically.

#### [MODIFY] [lean_header.template](file:///home/srghma/projects/lean4/src/include/lean/lean_header.template)
- Remove the `#ifdef LEAN_MIMALLOC` / `#include <lean/mimalloc.h>` block because C/C++ code no longer needs compile-time allocation redirection header logic (all object allocations are encapsulated in Rust runtime).

### libloading Replacement

#### [MODIFY] [library_dynlib.rs](file:///home/srghma/projects/lean4/src/rust/lean_runtime/src/library_dynlib.rs)
- Remove raw `extern "C"`/`extern "system"` imports of `dlopen`, `dlclose`, `dlsym`, `LoadLibraryA`, `FreeLibrary`, `GetProcAddress`.
- Define an opaque handle structure wrapping `libloading::Library`.
- Implement `lean_dynlib_load`, `lean_dynlib_get`, and `dynlib_finalizer` using `libloading` API.
  - To preserve the FFI structure, `lean_dynlib_load` will return a `*mut c_void` pointer pointing to a heap-allocated `libloading::Library` boxed instance.
  - `dynlib_finalizer` will drop the box, unloading the library safely.

## Verification Plan

### Automated Tests
- Build stage1 target:
  `make -C build/release lean_runtime_rust leancpp lean -j$(nproc)`
- Run focused FFI and plugin tests:
  `ARGS='-R "tests/lake/examples/ffi/test.sh|tests/lake/examples/reverse-ffi/test.sh|misc_dir/plugin" --timeout 240 --output-on-failure'`

----------

[CMakeLists.txt#L808-816](textBlock;file:///home/srghma/projects/lean4/src/CMakeLists.txt#L808-816) why we need to create empty.c file? will it be used? I think no. if no -remove

----------

# TASK:

Now we want to remove all .h files

Last one is

~/projects/lean4  ↱ rust-rewrite ✚  fd "\.h$" ./src
./src/include/lean/lean.h

I want to generate it using `cbindgen` like

```toml
language = "C"
style = "both"
include_guard = "LEAN_H"
autogen_warning = "/* Warning, this file is autogenerated by cbindgen. Don't modify this manually. */"

# after_includes is placed inside the include guard, after the standard
# #include <stdint.h> etc., but before any generated struct/function declarations.
# Only content that genuinely cannot be expressed as a Rust type belongs here.
after_includes = """
/* ── LEAN_EXPORT: visibility for symbols in EmitC.lean-generated C files ─── */
#if defined(_WIN32)
#  define LEAN_EXPORT __declspec(dllexport)
#elif defined(__GNUC__) || defined(__clang__)
#  define LEAN_EXPORT __attribute__((visibility("default")))
#else
#  define LEAN_EXPORT
#endif
"""

[export]
include = [
  "LeanArrayObject",
  "LeanStringObject",
  "LeanScalarArray",
  "LeanClosureObject",
  "LeanOnceCell",
  "LeanPromiseObject",
]
exclude = [
  # Internal Rust types with no C-visible role
  "LeanListCell",
  "LeanTaskObject",
  "NameGeneratorState",
  "SendPtr",
  "UvHandle",
  # C++ wrapper types
  "LeanName",
  "LeanOptions",
  "LeanOptionalName",
  "LeanNameGenerator",
]

[export.rename]
"LeanObject"         = "lean_object"
"LeanExternalClass"  = "lean_external_class"
"LeanExternalObject" = "lean_external_object"
"LeanThunkObject"    = "lean_thunk_object"
"LeanRefObject"      = "lean_ref_object"
"LeanPromiseObject"  = "lean_promise_object"
"LeanClosureObject"  = "lean_closure_object"
"LeanArrayObject"    = "lean_array_object"
"LeanStringObject"   = "lean_string_object"
"LeanScalarArray"    = "lean_sarray_object"
"LeanOnceCell"       = "lean_once_cell_t"

[parse]
parse_deps = false
```

I already started doing this


modified:   src/rust/Cargo.lock
modified:   src/rust/Cargo.toml
new file:   src/rust/lean_ffi_types/Cargo.toml
new file:   src/rust/lean_ffi_types/cbindgen.toml
new file:   src/rust/lean_ffi_types/src/lib.rs
new file:   src/rust/lean_runtime/cbindgen.toml
modified:   src/rust/lean_runtime/src/lib.rs


but

cbindgen ran but warned it can't handle AtomicPtr<LeanObject>  and AtomicI32.

review changes and continue

Why we want to have lean.h left?

bc it is imported in tests

tests/lake/examples/ffi/lib/c/ffi_shared.cpp
1:#include <lean/lean.h>

tests/lake/examples/reverse-ffi/main.c
2:#include <lean/lean.h>

tests/compile_bench/binarytrees.st.lean.c
4:#include <lean/lean.h>

but our rust code should not import any structures or functions from it.

all code should be inside of rust.

--------
After this feature is done and tests have passed we want to replace cpp deps with cargo deps


```
1. rm -rfd ./cadical -> cadical
1. rm -rfd ./mimalloc -> dont use standard rust allocator, use mimalloc allocator from crate
1. replace libuv -> libuv (dont use https://github.com/bmatcuk/libuv-sys/ (libuv-sys2 = v1.52.2 which is libuv v1.52.2 too))
1. <icu.h> -> icu crate (pure rust rewrite) (not https://github.com/google/rust_icu
1. emscripten.h -> just compile to wasm using rust
1. zlib -> flate2 + miniz_oxide ? OR  https://github.com/trifectatechfoundation/zlib-rs ?
1. llvm-c -> llvm-sys (to load code produced by EmitLLVM)
1. other deps that were originally in cpp (can check original cpp implementation at upstream/master):
  - Windows-specific APIs: <windows.h>, <psapi.h>, <bcrypt.h> (cryptography/entropy), and <ntdef.h>.
  - POSIX/Unix-specific APIs: <unistd.h>, <dlfcn.h> (dynamic loading), <dirent.h> (directory traversal), <pthread.h> (threading), and <link.h>.
  - Platform debugging: <execinfo.h> (for generating stack traces on Unix-like systems).
  -> for all of them - use rust native libs instead

<dlfcn.h> / LoadLibrary	-> libloading (safe cross-platform dynamic loading)
```

rust libs can be xxx-sys or xxx (safe wrapper around sys) - I want to use xxx libs. If my selection of libs is wrong - please fix me

I would start in this order:

1. mimalloc
    - Lowest-risk, global, and self-contained.
    - Use the mimalloc crate as the global allocator. That is the right choice for a Rust-owned allocator layer. mimalloc is explicitly a drop-in global allocator wrapper. source (https://docs.rs/mimalloc)

2. libloading
    - Also low-risk and lets you remove dlfcn.h / LoadLibrary style shims early.
    - This is the right “safe wrapper over sys” choice here. The crate is specifically a cross-platform dynamic loading API. source (https://docs.rs/libloading)

3. zlib
    - Prefer flate2 first if Lean only needs normal compress/decompress streams.
    - flate2 already defaults to a pure-Rust backend (miniz_oxide) and supports zlib/gzip. source (https://docs.rs/flate2)
    - If you need something closer to a low-level zlib engine, zlib-rs is the better fit, but it is lower-level and the crate itself says to use flate2 for a higher-level interface. source (https://docs.rs/zlib-rs)

4. icu
    - Move this after the basic infra because it tends to touch string/locale behavior and can spread into parsing/printing paths.
    - The icu meta-crate is the right Rust-side family for ICU4X-based functionality. source (https://docs.rs/icu)

5. llvm-c
    - Use llvm-sys.
    - This is the correct low-level crate for LLVM C API bindings. It is version-coupled to LLVM, so you want to line it up with the LLVM you actually build against. source (https://docs.rs/llvm-sys)

6. libuv
    - Use the safe libuv crate, not libuv-sys2, if your goal is Rust-facing APIs.
    - The libuv crate is a wrapper crate; its docs show it depends on libuv-sys2 under the hood, which is fine if you want the safe wrapper layer. source (https://docs.rs/libuv)
    - If you want to avoid low-level sys crates in your codebase, libuv is the right user-facing choice, but it still depends on a sys crate internally. That is normal.

7. Emscripten and platform-specific C headers
    - emscripten.h: leave this until later, because it is usually tied to the build target and not just a library swap.
    - Windows/POSIX/debug headers: replace with Rust-native APIs after the higher-level runtime pieces are stable.

So the practical starting point is:

- first: mimalloc, libloading
- then: zlib via flate2 or zlib-rs
- then: icu
- then: llvm-sys
- then: libuv
- last: target/platform shims like emscripten.h, windows.h, unistd.h, pthread.h, dlfcn.h, dirent.h, execinfo.h

That order is based on blast radius:

- allocator and dynamic loading are easiest to swap out cleanly
- compression and ICU are contained but more behavior-sensitive
- LLVM and libuv are core runtime dependencies and touch more of the system
- platform shims are best removed once the Rust replacements are already in place

One correction to your dependency preference:

- mimalloc: yes, use the mimalloc crate
- libloading: yes, use the safe wrapper crate
- libuv: yes, use the libuv crate, not libuv-sys2 directly
- zlib: I would start with flate2 unless you have a hard reason to need the lower-level zlib-rs
- icu: use the icu meta-crate family, but expect to choose specific subcrates later if you want tighter control

--------

but in next iteration we want to replace these shims

In the end we want to make rust code independent from libc and reimplement all unsafe structures/functions and have only small shim to make old/deprecated cpp code interact with our new safe rust kernel

- if rs file can be can have #![no_std] at top - lets add
- if rs file can be can have #![forbid(unsafe_code)] at top - lets add


----

# Generate lean.h With cbindgen

## Summary

Replace the last source header with a build-generated lean.h. Use lean_ffi_types as the cbindgen source for C ABI layouts, and preserve the existing Lean C runtime macro/static-inline layer through a generated template because
cbindgen cannot express it. The final state should make fd "\.h$" ./src return nothing.

## Key Changes

- Keep src/rust/lean_ffi_types as the cbindgen-only crate and make it the only cbindgen source.
    - Add missing C-visible layout types needed by emitted C, especially LeanCtorObject.
    - Correct public layout shadows to match current src/include/lean/lean.h and original origin-master-src/include/lean/lean.h, including lean_promise_object.m_result as a task pointer layout-compatible field.
    - Use #![no_std] and #![forbid(unsafe_code)] only for the shadow type crate if cbindgen accepts the function pointer types under that lint.

- Remove the staged lean_runtime cbindgen approach.
    - Delete src/rust/lean_runtime/cbindgen.toml.
    - Revert cbindgen-only visibility/comment changes in src/rust/lean_runtime/src/lib.rs unless a type is actually used by Rust runtime code.
    - Do not run cbindgen over lean_runtime; it contains AtomicPtr, AtomicI32, and internal state that should stay Rust-only.

- Generate the final header into the build tree only.
    - Add a small generator script, for example srghmascripts/generate_lean_h.sh, that runs:
      cbindgen src/rust/lean_ffi_types --config src/rust/lean_ffi_types/cbindgen.toml

    - Post-process known cbindgen array fields from [0] to flexible array members []; C++ rejects generated static string initializers with zero-length arrays.
    - Splice the generated typedef block into a non-.h template containing the existing macro, typedef, extern declaration, and static-inline runtime ABI layer.
    - Delete src/include/lean/lean.h; generate ${CMAKE_BINARY_DIR}/include/lean/lean.h.

- Update CMake.
    - Find cbindgen at configure/build time.
    - Add a generate_lean_h custom command/target before runtime, emitted C, tests, install/copy steps, and runtime_bc.
    - Replace file(COPY ${CMAKE_SOURCE_DIR}/include/lean ... *.h) for lean.h with the generated build artifact.
    - Change src/runtime/CMakeLists.txt so lean.h.bc reads ${CMAKE_BINARY_DIR}/include/lean/lean.h, not the deleted source header.

## Test Plan

- First validate generation only:
    - Run cbindgen into /tmp, inspect that no AtomicPtr/AtomicI32 warnings remain.
    - Compile a small C and C++ snippet including generated <lean/lean.h> with static lean_string_object and lean_ctor_object initializers.

- Build targets:
    - make -C build/release lean_runtime_rust leancpp lean -j"$(nproc)"
    - If LLVM is enabled in this build, also verify runtime_bc / lean.h.bc.

- Focused tests:
    - ARGS='-R "tests/lake/examples/ffi/test.sh|tests/lake/examples/reverse-ffi/test.sh|compile/strictAndOr.lean|compile/thunk.lean|misc_dir/plugin" --timeout 240 --output-on-failure'
    - Use the failure-filtered test command style from the user instructions.
    - Do not run the full suite; ask the user to run it after focused tests pass.

## Assumptions

- Generated lean.h should exist only under the build/include tree; no .h file should remain under src.
- The C inline ABI layer is allowed as template input because cbindgen cannot generate static inline functions/macros from Rust.
- Behavior and layout must match origin-master-src/include/lean/lean.h; Rust runtime must not include or depend on generated lean.h.
- Leave unrelated staged .claude/CLAUDE.md changes untouched.


----

I see its possible to make typings more talking/verbose/typesafe e.g. replace

-    pub m_result: *mut LeanObject,
with
+    pub m_result: *mut LeanTaskObject,

can we do it more?
maybe use Phantom fields?

1. Audit the object model and split types into two layers:
    - raw ABI types that must stay #[repr(C)] and pointer-compatible with C
    - Rust-only typed wrappers for ownership, borrowing, and invariants

2. Replace the most obvious broad pointers first:
    - *mut LeanObject fields inside concrete Rust structs should become the specific struct pointer when layout and usage are known, like *mut LeanTaskObject
    - keep *mut LeanObject only at true erased boundaries such as generic containers, dispatch points, and FFI entry points

3. Introduce lightweight wrapper types for typed access:
    - LeanObj<T> or similar for typed raw pointers
    - BorrowedLeanObj<'a, T> / OwnedLeanObj<T> where lifetime or ownership matters
    - these wrappers should be zero-cost and repr(transparent) where appropriate

4. Use PhantomData only for semantic state, not for layout:
    - encode borrow vs owned
    - encode “this pointer is logically a LeanTaskObject”
    - encode aliasing or mutability constraints where that prevents misuse
    - do not use it to model actual stored fields in C-facing structs

5. Tighten constructors and accessors:
    - make constructors return the precise type
    - make field accessors require the precise type
    - reduce unchecked casts by moving them into a few well-named conversion points

6. Leave the C ABI stable:
    - no changes to generated header layout unless the C-facing representation already permits it
    - no breaking changes to exported symbol names while the port is still in progress

7. Validate incrementally:
    - compile after each type-family conversion
    - run focused tests around the touched runtime paths
    - compare against origin-master-src whenever a mismatch appears

The practical rule is: use precise Rust types everywhere inside Rust, and only erase back to *mut LeanObject at the FFI boundary or in truly polymorphic runtime code. PhantomData is useful for ownership and lifetime encoding, but not as a substitute for concrete object typing.

----

there should be no lean_cxx_... functions, they were just temporary port

1. Remove the temporary lean_cxx_... symbol names from Rust entry points, keeping only the final names that match origin-master-src.
 - kernel_expr_eq_fn.rs
 - kernel_abstract.rs
 - kernel_expr.rs
 - kernel_trace.rs
 - kernel_num.rs

2. Split the remaining cases into two buckets.
 - Pure Rust implementations that should stay as real Rust functions, exported under the final C ABI names.
 - Compatibility-only wrappers that should disappear entirely once no caller needs the old names.

3. For kernel_num.rs, delete the placeholder lean_cxx_initialize_num / lean_cxx_finalize_num pair.
 - Check the original C++ num.cpp/equivalent in origin-master-src.
 - If there is no real work there, keep only the final no-op initialize_num / finalize_num symbols expected by the runtime.
 - Do not keep the lean_cxx_... aliases.

4. For kernel_trace.rs, rename the actual exported functions to the non-cxx names and keep their bodies in Rust.
 - lean_register_trace_class
 - lean_initialize_trace
 - lean_finalize_trace
 - lean_is_trace_class_enabled
 - lean_scope_trace_env_ctor_c1/c2
 - lean_scope_trace_env_dtor_c1/c2
   Then remove the lean_cxx_... spellings entirely.

5. For kernel_expr.rs, kernel_abstract.rs, and kernel_expr_eq_fn.rs, keep the Rust bodies but rename the exported ABI symbols to the final names only.
 - The comments that say “replaces lean_cxx_...” should be rewritten or removed after the rename.
 - There should be no symbol indirection through a lean_cxx_... function at all.

6. Search for every remaining lean_cxx_ reference after the rename.
 - Any remaining reference should be either:
  - an old comment, which should be cleaned up, or
  - a genuine external compatibility requirement, which should be checked against origin-master-src before keeping.

 - If it does not exist in the original C++ implementation, remove it.

7. Validate against origin-master-src.
 - For each function family, compare the Rust body and exported name to the original C++ implementation.
 - The goal is semantic parity, not a Rust-specific cleanup that changes behavior.

8. Then run a focused test slice around the touched areas.
 - expr equality / abstraction / loose bvar
 - trace registration and scope handling
 - num init/finalize if still present
 - any runtime tests that include those headers or call the affected exports

The key rule is: the final Rust runtime should export only the final ABI names, with no lean_cxx_... hop, and any remaining lean_cxx_... text should be treated as leftover scaffolding unless the original C++ really needs it.

----

I want You to write bun script that will:
1. extract from original `origin-master-src/include/lean/lean.h` list of all functions
2. write them into .md file , each item with checkbox [ ]
3. then for each of them - check that they are used in rust code (i.e. they are not only exported, but also actively used in rust or lean code)

Write a bun script that will show that functions are used AND used more than once.

It will output summary: used in rust code and/or used in lean generated code. not used anywere.

If function is not used - why not used? I this a mistake?

This will also allow to check that rust code doesnt use magic constants (e.g. number 1 which actually should be written as LEAN_XXX).

----

In our rust code we use xxx_initialize/finalize for modules

But can we replace them with rust-based approach Drop or etc? so that things are initialized/finalized automatically?

Note that we:
1. export (? right ?) some initializer/finalizers in lean.h, and it should continue to work
2. the user defined (in cpp, in tests) initializer/finalizers, should continue to work

1. Inventory all current *_initialize / *_finalize paths.
    - Classify each one as:
        - pure Rust-owned state
        - C++/test hook that must still be callable
        - no-op that can disappear

    - This gives the exact compatibility surface we must preserve in lean.h.

2. Introduce a Rust module registry.
    - Store per-module init state in Rust, keyed by module name or module ID.
    - Use OnceLock for one-time setup and a guarded runtime struct for cleanup.
    - Keep explicit initialize_xxx() / finalize_xxx() Rust functions, but make them operate on the registry instead of scattered global state.

3. Keep the exported C ABI unchanged.
    - lean.h continues to export the same initializer/finalizer symbols.
    - Those symbols become wrappers around the Rust registry.
    - That preserves both:
        - Lean-generated code that calls init/finalize functions
        - user-defined init/finalize functions used in tests or C++ glue

4. Add an owning runtime handle for automatic cleanup.
    - Build a top-level Rust Runtime / ModuleRuntime object that owns all module resources.
    - On process-side Rust entrypoints, create one and let Drop release internal state.
    - Do not rely on Drop for static globals at process exit; use it for owned runtime objects only.
    - Exported finalize_* functions should still exist and call the same cleanup path explicitly.

5. Preserve user-defined hooks.
    - Keep a registry of external initializer/finalizer callbacks.
    - Rust init should invoke registered user hooks in the same order as today.
    - Rust finalize should call them in reverse or existing order, matching current behavior.

6. Validate incrementally.
    - First port one module with clear state ownership.
    - Verify initialize/finalize symbols still link and tests still call custom hooks.
    - Then migrate the rest module-by-module.

Main constraint:

- Replace implicit global lifecycle with explicit Rust ownership internally.
- Do not remove the public init/finalize C ABI until the last consumer is gone.

If you want, I can turn this into a concrete migration sequence against the current src/rust/lean_runtime modules.

----

Check rust code, make as much as possible unsafe functions - safe

----

are all

~/projects/lean4  ↱ rust-rewrite ±✚  fd "\.rs$" ./src/rust/lean_runtime/src
/kernel_abstract.rs
/kernel_declaration.rs
/kernel_environment.rs
/kernel_equiv_manager.rs
/kernel_expr.rs
/kernel_expr_eq_fn.rs
/kernel_for_each_fn.rs
/kernel_instantiate.rs
/kernel_level.rs
/kernel_local_ctx.rs
/kernel_num.rs
/kernel_quot.rs
/kernel_replace_fn.rs
/kernel_trace.rs
/kernel_type_checker.rs
/lib.rs
/library_constants.rs
/library_dynlib.rs
/library_elab_environment.rs
/library_expr_lt.rs
/library_formatter.rs
/library_instantiate_mvars.rs
/library_ir_interpreter.rs
/library_llvm.rs
/library_module.rs
/library_print.rs
/library_time_task.rs
/library_util.rs
/runtime_alloc.rs
/runtime_apply.rs
/runtime_compact.rs
/runtime_compact_writer.rs
/runtime_debug.rs
/runtime_dns.rs
/runtime_event_loop.rs
/runtime_exception.rs
/runtime_float.rs
/runtime_interrupt.rs
/runtime_io_error.rs
/runtime_io_fs.rs
/runtime_io_handle.rs
/runtime_io_ref.rs
/runtime_io_stream.rs
/runtime_io_task.rs
/runtime_libuv.rs
/runtime_memory.rs
/runtime_mpn.rs
/runtime_mpz.rs
/runtime_mutex.rs
/runtime_net_addr.rs
/runtime_object_array.rs
/runtime_object_name.rs
/runtime_object_nat_int.rs
/runtime_object_panic.rs
/runtime_object_rc.rs
/runtime_object_size.rs
/runtime_object_string.rs
/runtime_object_task.rs
/runtime_once.rs
/runtime_process.rs
/runtime_sharecommon.rs
/runtime_signal.rs
/runtime_stack_info.rs
/runtime_stack_overflow.rs
/runtime_system.rs
/runtime_tcp.rs
/runtime_thread.rs
/runtime_timer.rs
/runtime_udp.rs

files used by each other?
