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
2. CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release/stage2 -j "$(nproc)" test ARGS='-E bench/mvcgen/sym -R "elab/1921|elab/4306"' (I excluded bench/mvcgen/sym bc its olean files are stale, and selected two random tests) (Is this command runs stage3? fix if no)

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
