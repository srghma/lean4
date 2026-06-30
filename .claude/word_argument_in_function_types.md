C - fn - have, fn__boxed - have, fn___redArg - ??
Rust - fn - no, fn__boxed - have, fn___redArg - ??

-----

Yes, the variant set is broader.

Current pattern:

- `fn`
  - Real implementation, when emitted.
- `fn___boxed`
  - Wrapper that takes the full boxed ABI shape and forwards to `fn`.
  - It usually ignores erased/unused args.
- `fn___redArg`
  - Optimized entrypoint for calls where the function is known to be used in reduced form.
  - In Rust emission, this still exists for some functions.
- `fn___redArg___boxed`
  - Boxed wrapper for the `___redArg` variant.

So the corrected summary is:

- Old C-style output:
  - `fn`
  - `fn___boxed`
  - `fn___redArg`
  - `fn___redArg___boxed`
- Rust output today:
  - same family can still exist
  - but not every function gets every variant
  - some functions only have `fn` + `fn___boxed`
  - some also get `___redArg` variants

Other common generated variants you will see:

- `_init_...`
  - initializer helpers for closed terms
- `runtime_initialize_...`
  - runtime init hook for a module
- `meta_initialize_...`
  - meta init hook
- `initialize_...`
  - full module initializer that chains the others
- `l___private_...`
  - private helper functions generated from Lean
- `___lam__N`
  - lambda bodies lifted to named Rust functions
- `___spec__N`
  - specialization helpers created by the compiler
- `___closed__N`
  - cached closed terms / constants
- `___boxed__const__N`
  - boxed constant helpers

For your IO example specifically:

- the real function is `lean_io_eprintln(...)` / `l_IO_eprintln...`
- the `___boxed` wrapper has the extra erased argument and ignores it
- `___redArg` is only present when the compiler emits that reduced form for a function that needs it

If you want, I can give you a compact “generated function variants glossary” for this repo with exactly what each suffix means in practice.

---------

Glossary for the generated Lean-to-Rust function variants in this repo:

- `fn`
  - The actual implementation.
  - This is the function Rust code should usually call.

- `fn___boxed`
  - ABI wrapper around `fn`.
  - Takes the full boxed calling convention.
  - Drops erased/unused arguments and forwards to `fn`.

- `fn___redArg`
  - Reduced-argument entrypoint.
  - Used when the compiler can call the function in a partially reduced form.
  - Usually skips some wrapper overhead.

- `fn___redArg___boxed`
  - Boxed wrapper for the `___redArg` variant.
  - Same idea as `___boxed`, but for reduced-arg form.

- `fn___lam__N`
  - Lifted lambda body.
  - Lean lambda expressions become named helper functions.

- `fn___lam__N___boxed`
  - Boxed wrapper for a lifted lambda helper.

- `fn___spec__N`
  - Specialization helper.
  - Compiler-generated version for a specific call shape or optimization path.

- `fn___spec__N___boxed`
  - Boxed wrapper for the specialization helper.

- `_init_...`
  - Closed-term initializer.
  - Computes a cached constant or closure cell value.

- `runtime_initialize_...`
  - Module runtime init hook.
  - Sets up runtime-only state for a module.

- `meta_initialize_...`
  - Meta-layer init hook.
  - Used for meta/compile-time initialization state.

- `initialize_...`
  - Full module initializer.
  - Chains runtime, meta, and module-specific initialization.

- `l___private_...`
  - Private helper generated from Lean internals.
  - Not meant as a stable public API.

- `___closed__N`
  - Cached closed term storage.
  - Generated constant data or once-cell backing storage.

- `___closed__N_value`
  - The static value backing `___closed__N`.

- `___boxed__const__N`
  - Boxed constant helper, usually for preserved literal data or closures.

- `___aux__N`
  - Auxiliary helper introduced by the compiler.
  - Often from local `let`/`have`/pattern-matching lowering.

Practical rule in this codebase:

- Prefer calling `fn` when it exists.
- Use `fn___boxed` only when you are on the boxed ABI boundary.
- Treat `___redArg` as an optimization/compatibility entrypoint, not the canonical one.
- `___boxed` and `___redArg` variants exist for calling convention reasons, not because they are semantically different functions.

If you want, I can also map these variants to the exact code generation sites in `EmitRust.rs` and show which ones are emitted for `IO` functions, `init` functions, and regular pure functions.

-----

`io_world` is not part of the ordinary `fn / fn___boxed / fn___redArg` shape in the emitted module code.

What actually happens:

- `fn`
  - real implementation
  - usually no explicit `io_world`

- `fn___boxed`
  - ABI wrapper
  - may have extra erased args
  - those extra args are ignored

- `fn___redArg`
  - reduced-argument variant
  - still not the `io_world` token itself

- `io_world`
  - handled by the runtime, not usually surfaced as a normal function parameter in the generated module code
  - created with `lean_io_mk_world()`
  - used when entering/leaving the IO runtime boundary

Concrete stage1 C examples:

- [`_lean_main(lean_object* v_args_1_)`](/home/srghma/projects/lean4/build/release/stage1/lib/temp/LakeMain.c#L22)
  - no `io_world`
- [`l_main___boxed(lean_object* v_args_6_, lean_object* v_a_7_)`](/home/srghma/projects/lean4/build/release/stage1/lib/temp/LakeMain.c#L28)
  - extra erased argument `v_a_7_` is present and ignored
- [`main(...)`](/home/srghma/projects/lean4/build/release/stage1/lib/temp/LakeMain.c#L34)
  - the runtime initializes IO and then calls `lean_run_main`, which is where the IO boundary is handled

Old runtime-side world token:
- [`lean_io_mk_world()`](/home/srghma/projects/lean4/build/release/include/lean/lean.h#L1473)

So the answer is:

- `io_world` is not “the extra arg” on `___boxed`
- the extra arg on `___boxed` is just an erased compatibility argument
- `io_world` is a runtime token used at the IO boundary
- in normal generated C/Rust module functions, you usually do not see it as a direct explicit parameter

One exception:
- some backend-internal helpers, especially in EmitLLVM-generated code, do thread a `world` value explicitly for IR-level reasons
- that is not the same thing as the ordinary generated Lean function variants

If you want, I can next map:
- `___boxed` args
- `___redArg`
- `io_world`
- `lean_io_mk_world()`

into one exact table for this repo.
