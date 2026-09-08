Yes, but not as a clean set of peer crates yet.

src/rust/lean_runtime is currently one strongly coupled crate that mirrors the old C++ runtime as modules. The natural top-level split is there, but the code is not fully layered:

- util, runtime, kernel, library, initialize are mutually interwoven through shared extern "C" symbols and shared raw object types.
- include is the bottom ABI layer, not a Rust crate boundary.
- shell is not really part of lean_runtime; it is more of a thin binary wrapper around the runtime.

So the dependency shape is closer to a semi-layered core with cycles than a clean linear stack.

What the current Rust crate looks like conceptually

- ffi_types or include: raw ABI structs and function-pointer types
- runtime_*: memory, object model, threading, IO, libuv, dynamic loading
- kernel_*: kernel expr/typechecker logic
- library_*: higher-level Lean library and elaboration helpers
- generated_abi: exported/imported Lean symbol glue
- initialize: module init/finalize glue

The main problem
The current code is not just “module A uses module B”. It also has:

- shared global symbols
- callbacks stored as raw function pointers
- cross-module extern "C" entry points
- raw LeanObject* being passed everywhere

That means if you split too early into separate crates, you will immediately need a shared ABI crate plus a glue crate, otherwise you get circular dependencies.

So: can it be split?
Yes, but the practical shape is:

- one small ABI crate
- one core runtime crate
- one kernel crate
- one library crate
- one glue/exports crate
- one shell binary crate

Not:

- runtime, kernel, library, util all as independent mutually dependent crates

Mermaid: current dependency shape

graph TD
  ffi[ABI / ffi_types]
  rt[runtime_*]
  ku[kernel_*]
  lib[library_*]
  init[initialize / module glue]
  gen[generated_abi]
  shell[shell wrapper]

  ffi --> rt
  ffi --> ku
  ffi --> lib
  ffi --> gen

  rt --> ku
  rt --> lib
  rt --> init

  ku --> rt
  ku --> lib

  lib --> rt
  lib --> ku

  init --> rt
  init --> ku
  init --> lib

  gen --> rt
  gen --> ku
  gen --> lib
  gen --> init

  shell --> gen
  shell --> rt

Interpretation

- ffi is the only true foundational layer.
- rt, ku, and lib are not a DAG today; they form a mutually dependent core.
- gen and init are glue layers, not stable business-logic crates.
- shell should stay separate and thin.

Recommended split order

1. lean_ffi_types
2. lean_abi or generated_abi for imported/exported Lean symbols
3. lean_runtime_core for allocation/object/thread/IO/libuv/dynlib
4. lean_kernel
5. lean_library
6. lean_initialize / glue crate
7. lean_shell binary

If you want, I can next produce:

1. a file-by-file crate split proposal for src/rust/lean_runtime/src/*.rs
2. a concrete dependency graph between those files
3. a minimal “first split” plan that would compile without changing behavior
