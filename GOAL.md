here is the current state

```
A  .codex/config.toml
M  .gitignore
M  CMakeLists.txt
M  CMakePresets.json
A  GOAL.md
M  flake.lock
M  flake.nix
A  resume_codex.ts
A  run_gdb.sh
M  src/CMakeLists.txt
M  src/Init/System/Platform.lean
R  src/Lean/Compiler/LCNF/EmitC.lean -> src/Lean/Compiler/LCNF/EmitRust.lean
M  src/Lean/Elab/BuiltinCommand.lean
M  src/Lean/LoadDynlib.lean
M  src/Lean/Meta/Constructions/CasesOn.lean
M  src/Lean/Shell.lean
M  src/LeanIR.lean
M  src/Leanc.lean
M  src/bin/leanc.in
M  src/cmake/Modules/FindGMP.cmake
D  src/cmake/Modules/FindWindowsSDK.cmake
D  src/cmake/Modules/README.md
M  src/cmake/run_checker.sh
M  src/config.h.in
M  src/lake/Lake/Config/Module.lean
M  src/lean.mk.in
A  src/rust/.gitignore
A  src/rust/.still-nanoda/.gitignore
A  src/rust/.still-nanoda/Cargo.lock
A  src/rust/.still-nanoda/Cargo.toml
A  src/rust/.still-nanoda/LICENSE
A  src/rust/.still-nanoda/README.md
A  src/rust/.still-nanoda/rustfmt.toml
A  src/rust/.still-nanoda/src/debug_printer.rs
A  src/rust/.still-nanoda/src/env.rs
A  src/rust/.still-nanoda/src/expr.rs
A  src/rust/.still-nanoda/src/inductive.rs
A  src/rust/.still-nanoda/src/level.rs
A  src/rust/.still-nanoda/src/lib.rs
A  src/rust/.still-nanoda/src/main.rs
A  src/rust/.still-nanoda/src/name.rs
A  src/rust/.still-nanoda/src/parser.rs
A  src/rust/.still-nanoda/src/pretty_printer.rs
A  src/rust/.still-nanoda/src/quot.rs
A  src/rust/.still-nanoda/src/tc.rs
A  src/rust/.still-nanoda/src/tests.rs
A  src/rust/.still-nanoda/src/tests/level.rs
A  src/rust/.still-nanoda/src/tests/natlit.rs
A  src/rust/.still-nanoda/src/tests/util.rs
A  src/rust/.still-nanoda/src/union_find.rs
A  src/rust/.still-nanoda/src/unique_hasher.rs
A  src/rust/.still-nanoda/src/util.rs
A  src/rust/.still-nanoda/test_resources/Empty/export
A  src/rust/.still-nanoda/test_resources/ProjFromProp/config.json
A  src/rust/.still-nanoda/test_resources/ProjFromProp/export
A  src/rust/Cargo.lock
A  src/rust/Cargo.toml
A  src/rust/cadical/Cargo.toml
A  src/rust/cadical/src/main.rs
A  src/rust/lean_runtime/Cargo.toml
A  src/rust/lean_runtime/build.rs
A  src/rust/lean_runtime/cbindgen.toml_
A  src/rust/lean_runtime/offset_test.rs
A  src/rust/lean_runtime/src/kernel_abstract.rs
A  src/rust/lean_runtime/src/kernel_declaration.rs
A  src/rust/lean_runtime/src/kernel_environment.rs
A  src/rust/lean_runtime/src/kernel_equiv_manager.rs
A  src/rust/lean_runtime/src/kernel_expr.rs
A  src/rust/lean_runtime/src/kernel_expr_cache.rs
A  src/rust/lean_runtime/src/kernel_expr_eq_fn.rs
A  src/rust/lean_runtime/src/kernel_for_each_fn.rs
A  src/rust/lean_runtime/src/kernel_inductive.rs
A  src/rust/lean_runtime/src/kernel_instantiate.rs
A  src/rust/lean_runtime/src/kernel_level.rs
A  src/rust/lean_runtime/src/kernel_local_ctx.rs
A  src/rust/lean_runtime/src/kernel_quot.rs
A  src/rust/lean_runtime/src/kernel_replace_fn.rs
A  src/rust/lean_runtime/src/kernel_trace.rs
A  src/rust/lean_runtime/src/kernel_type_checker.rs
A  src/rust/lean_runtime/src/lib.rs
A  src/rust/lean_runtime/src/library_annotation.rs
A  src/rust/lean_runtime/src/library_constants.rs
A  src/rust/lean_runtime/src/library_dynlib.rs
A  src/rust/lean_runtime/src/library_elab_environment.rs
A  src/rust/lean_runtime/src/library_expr_lt.rs
A  src/rust/lean_runtime/src/library_formatter.rs
A  src/rust/lean_runtime/src/library_instantiate_mvars.rs
A  src/rust/lean_runtime/src/library_llvm.rs
A  src/rust/lean_runtime/src/library_max_sharing.rs
A  src/rust/lean_runtime/src/library_module.rs
A  src/rust/lean_runtime/src/library_num.rs
A  src/rust/lean_runtime/src/library_print.rs
A  src/rust/lean_runtime/src/library_replace_visitor.rs
A  src/rust/lean_runtime/src/library_time_task.rs
A  src/rust/lean_runtime/src/library_util.rs
A  src/rust/lean_runtime/src/runtime_alloc.rs
A  src/rust/lean_runtime/src/runtime_apply.rs
A  src/rust/lean_runtime/src/runtime_compact.rs
A  src/rust/lean_runtime/src/runtime_compat_cxx.rs
A  src/rust/lean_runtime/src/runtime_debug.rs
A  src/rust/lean_runtime/src/runtime_dns.rs
A  src/rust/lean_runtime/src/runtime_event_loop.rs
A  src/rust/lean_runtime/src/runtime_exception.rs
A  src/rust/lean_runtime/src/runtime_float.rs
A  src/rust/lean_runtime/src/runtime_interrupt.rs
A  src/rust/lean_runtime/src/runtime_io.rs
A  src/rust/lean_runtime/src/runtime_libuv.rs
A  src/rust/lean_runtime/src/runtime_memory.rs
A  src/rust/lean_runtime/src/runtime_misc_exports.rs
A  src/rust/lean_runtime/src/runtime_mpn.rs
A  src/rust/lean_runtime/src/runtime_mpz.rs
A  src/rust/lean_runtime/src/runtime_mutex.rs
A  src/rust/lean_runtime/src/runtime_net_addr.rs
A  src/rust/lean_runtime/src/runtime_numeric_exports.rs
A  src/rust/lean_runtime/src/runtime_numeric_exports_int.rs
A  src/rust/lean_runtime/src/runtime_object_array.rs
A  src/rust/lean_runtime/src/runtime_object_nat_int.rs
A  src/rust/lean_runtime/src/runtime_object_panic.rs
A  src/rust/lean_runtime/src/runtime_object_rc.rs
A  src/rust/lean_runtime/src/runtime_object_string.rs
A  src/rust/lean_runtime/src/runtime_once.rs
A  src/rust/lean_runtime/src/runtime_process.rs
A  src/rust/lean_runtime/src/runtime_sharecommon.rs
A  src/rust/lean_runtime/src/runtime_signal.rs
A  src/rust/lean_runtime/src/runtime_stack_info.rs
A  src/rust/lean_runtime/src/runtime_stack_overflow.rs
A  src/rust/lean_runtime/src/runtime_system.rs
A  src/rust/lean_runtime/src/runtime_task.rs
A  src/rust/lean_runtime/src/runtime_tcp.rs
A  src/rust/lean_runtime/src/runtime_thread.rs
A  src/rust/lean_runtime/src/runtime_timer.rs
A  src/rust/lean_runtime/src/runtime_udp.rs
A  src/rust/lean_shell/Cargo.toml
A  src/rust/lean_shell/src/lib.rs
A  src/rust/lean_shell_main/Cargo.toml
A  src/rust/lean_shell_main/src/lib.rs
A  src/shell/lean_main.c
M  src/stdlib.make.in
D  src/stdlib_flags.h
A  srghmascripts/DepGraph.lean
A  srghmascripts/check_symbols.sh
A  srghmascripts/cpp_vs_rust_discrepancies/include/lean/lean.md
A  srghmascripts/cpp_vs_rust_discrepancies/include/lean/lean_gmp.md
A  srghmascripts/cpp_vs_rust_discrepancies/include/lean/lean_libuv.md
A  srghmascripts/cpp_vs_rust_discrepancies/initialize/init.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/abstract.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/declaration.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/environment.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/equiv_manager.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/expr.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/expr_cache.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/expr_eq_fn.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/expr_maps.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/expr_sets.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/find_fn.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/for_each_fn.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/inductive.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/init_module.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/instantiate.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/kernel_exception.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/level.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/local_ctx.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/quot.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/replace_fn.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/trace.md
A  srghmascripts/cpp_vs_rust_discrepancies/kernel/type_checker.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/annotation.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/bin_app.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/constants.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/constructions/cases_on.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/constructions/init_module.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/constructions/no_confusion.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/constructions/util.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/dynlib.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/elab_environment.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/expr_lt.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/expr_pair.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/expr_pair_maps.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/expr_unsigned_map.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/formatter.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/init_attribute.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/init_module.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/instantiate_mvars.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/ir_interpreter.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/ir_types.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/llvm.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/max_sharing.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/module.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/num.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/print.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/profiling.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/replace_visitor.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/scope_cache.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/suffixes.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/time_task.md
A  srghmascripts/cpp_vs_rust_discrepancies/library/util.md
A  srghmascripts/cpp_vs_rust_discrepancies/order_of_review.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/alloc.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/allocprof.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/apply.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/array_ref.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/buffer.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/byteslice.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/compact.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/debug.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/exception.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/flet.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/hash.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/init_module.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/int.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/interrupt.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/io.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/libuv.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/list_ref.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/memory.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/mpn.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/mpz.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/mutex.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/object.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/object_ref.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/option_ref.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/optional.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/pair_ref.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/platform.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/process.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/sharecommon.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/sstream.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/stack_overflow.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/stackinfo.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/string_ref.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/thread.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/utf8.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/dns.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/event_loop.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/net_addr.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/signal.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/system.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/tcp.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/timer.md
A  srghmascripts/cpp_vs_rust_discrepancies/runtime/uv/udp.md
A  srghmascripts/cpp_vs_rust_discrepancies/shell/lean.md
A  srghmascripts/cpp_vs_rust_discrepancies/shell/lean_js.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/alloc.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/ascii.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/bit_tricks.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/escaped.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/exception_with_pos.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/ffi.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/freset.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/init_module.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/io.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/kvmap.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/lbool.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/list.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/list_fn.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/macros.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/map_foreach.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/message_definitions.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/name.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/name_generator.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/name_hash_map.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/name_hash_set.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/name_map.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/name_set.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/nat.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/null_ostream.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/option_declarations.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/options.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/output_channel.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/pair.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/path.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/rb_map.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/rb_tree.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/rc.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/shell.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/test.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/timeit.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/timer.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/unit.md
A  srghmascripts/cpp_vs_rust_discrepancies/util/unlock_guard.md
A  srghmascripts/dep_graph.dot
A  srghmascripts/dep_graph.svg
A  srghmascripts/dep_graph.ts
D  tests/bench/rbmap_checkpoint_cpp_lean3.cpp
D  tests/bench/rbmap_checkpoint_cpp_std.cpp
A  tests/bench/rbmap_checkpoint_rust_lean3.rs
A  tests/bench/rbmap_checkpoint_rust_std.rs
D  tests/bench/rbmap_cpp_lean3.cpp
D  tests/bench/rbmap_cpp_std.cpp
A  tests/bench/rbmap_rust_lean3.rs
A  tests/bench/rbmap_rust_std.rs
D  tests/lake/examples/ffi/lib/c/ffi_shared.cpp
A  tests/lake/examples/ffi/lib/c/ffi_shared/Cargo.lock
A  tests/lake/examples/ffi/lib/c/ffi_shared/Cargo.toml
A  tests/lake/examples/ffi/lib/c/ffi_shared/src/lib.rs
M  tests/lake/examples/ffi/lib/lakefile.lean
```

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
2. CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release -j "$(nproc)" test ARGS='-E bench/mvcgen/sym -R "elab/1921|elab/4306"' (I excluded bench/mvcgen/sym bc its olean files are stale, and selected two random tests) (Is this command runs stage3? fix if no)

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
