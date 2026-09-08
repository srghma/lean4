# library_ir_interpreter.rs audit

Original C++:
- `origin-master-src/library/ir_interpreter.cpp`

Rust:
- `src/rust/lean_runtime/src/library_ir_interpreter.rs`

## 2026-06-25 — concurrency: non-persistent global option Name → over-free

**Symptom:** `server_interactive/cancellation_try_plain.lean` failed intermittently (~12% alone,
worse under the full parallel suite) with the file worker SIGSEGV'ing:
`Server process ... crashed, likely due to a stack overflow or a bug`. Minimal repro (no server,
no cancellation needed): `import Lean.Elab.Tactic.Try; example : UnsolvableProp := by try?` crashes
~15% of the time. `LEAN_NUM_THREADS=1`/`=2` never crash; default (20 workers) does → genuine
concurrency race. Reference C++ Lean v4.31.0 is stable (0/25). So it is a Rust-rewrite regression.

**Crash signature:** always `_mi_heap_delayed_free_partial` ← `_mi_malloc_generic` with a *varying*
frame #2 (mkLocalDecl / isDefEqEta / WHNF.cache / EnvExtension.modifyState …) = cross-thread heap
corruption; the malloc just trips over an earlier over-free. Many worker threads concurrently in
`LazyDiscrTree.createImportedEnvironmentSeq` (parallel import scan for `try?`/`exact?` library
search).

**Root cause (found with the dormant UAF detector, `UAF_DETECT=true` in runtime_object_rc.rs, plus a
poison-check added at the top of the exported `lean_dec_ref_cold` — MT-object decs from generated
code route through it):** `interpreter_prefer_native_name()` lazily builds the global Name
`interpreter.prefer_native` via `lean_name_mk_string` (a normal **ST** object, rc = 1) and caches it
in `G_INTERPRETER_PREFER_NATIVE_NAME`, but **never marks it persistent**. Every `Interpreter::new`
(reached from `lean_eval_const`, e.g. compiling a grind simproc, or any IR eval) does
`lean_inc(name_obj)` then `lean_options_get_bool(opts, name_obj, …)` which **consumes** (decs) it.
Those inc/dec are **non-atomic** because the Name is ST (rc > 0). Under parallel `try?` candidate
evaluation / library-search import scan / grind, many worker threads run `Interpreter::new`
concurrently → racing non-atomic refcount on the one shared global Name → lost updates → premature
free → use-after-free → mimalloc freelist corruption. The detector caught the exact object
(tag = 1 `Name.str`, free-site `lean_dec_ref_cold ← lean_options_get_bool ← Interpreter::new ←
lean_eval_const`), with 3 threads hitting it simultaneously.

**Fix:** `lean_mark_persistent(prefer_native_name)` BEFORE publishing it via the `compare_exchange`,
so its inc/dec become no-ops (rc = 0) and are thread-safe. Mirrors C++ `mark_persistent(g_verbose->raw())`
for global option names (`util/options.cpp:25-29`) and the kernel's `init_global_name`
(kernel_type_checker.rs) and `library_util.rs`'s `lean_mark_persistent` of BOOL_TRUE/FALSE/UTIL_FRESH.
On a lost init race the loser's copy is already persistent and leaks once (bounded, a few small Names
per process) — negligible.

**Audit note:** `interpreter_prefer_native_name` was the ONLY lazy-init global object cache in the
runtime missing `mark_persistent` — all `AtomicPtr<LeanObject>` globals were checked
(`library_util.rs` BOOL_TRUE/FALSE/UTIL_FRESH mark persistent at single-threaded module init; kernel
globals use `init_global_name` which marks persistent before store). General rule: any process-
lifetime global Lean object read/refcounted from worker threads MUST be `lean_mark_persistent`'d
before publication.

**Verification:** with fix, `try?` repro 0/40 crashes (was ~15%); `cancellation_try_plain.lean`
0/20 (was ~12%); detector-ON 0/15 UAF; ctest `cancellation*` + `try_user_suggestions` + `quotInd`
all pass.
