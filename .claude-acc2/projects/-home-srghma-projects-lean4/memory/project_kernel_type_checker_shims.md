---
name: project-kernel-type-checker-shims
description: How the Rust kernel_type_checker.rs resolves inline-C++ accessors + the refcount/ABI gotchas that caused crashes
metadata: 
  node_type: memory
  type: project
  originSessionId: 271a0796-989a-42da-b942-f9af6032e70d
---

`src/rust/lean_runtime/src/kernel_type_checker.rs` (included into lib.rs via `include!`) references ~66 functions that are **inline** in C++ headers (expr.h, declaration.h, level.h, local_ctx.h, lean.h) and thus NOT exported symbols. They must be provided as Rust `#[no_mangle] pub unsafe extern "C"` shims in that file (field reads via `lean_ctor_get`, tag checks via `lean_ptr_tag`).

Key gotchas discovered while making them link + pass:
- **Stale-binary trap:** kernel_type_checker.rs was missing from the `runtime/CMakeLists.txt` dependency list, so `lean_runtime.o` was not recompiled when it changed → old object masked latent link/runtime bugs. Adding the dep exposed everything. If a `.rs` change "has no effect", check it is in that DEPENDS list.
- **Field accessors return BORROWED** (like C++ `cnstr_get_ref`): do NOT inc; the caller incs where it retains the value.
- **Builders CONSUME their args** (Lean ABI `obj_arg`): `lean_name_mk_string`, `lean_expr_mk_const`, `lean_local_ctx_mk_local_decl`, `lean_expr_mk_fvar`, etc. Do NOT `lean_dec` after calling them. A double-dec here corrupts mimalloc's freelist and crashes in a LATER `mi_malloc_small` (was the `--version` startup crash; root cause was `build_lean_name` and the dont_care init dec'ing already-consumed args).
- **Two registrations of `_kernel_fresh`:** both `initialize_cxx_type_checker_globals()` (C++) and the Rust `initialize_type_checker` registered the name-generator prefix → duplicate-prefix assert. Only the C++ side should register it.
- **C++ `local_ctx::mk_binding<false>` (= mk_pi)** is bridged via `#[link_name="_ZNK4lean9local_ctx10mk_bindingILb0EEENS_4exprEjPKS2_RS3_b"]`. `expr` is non-trivially destructible → Itanium ABI returns it via a **hidden sret pointer as the FIRST arg**, pushing `this` to second: `(sret, this=&lctx, num, fvars, b=&body, remove_dead_let)`. `remove_dead_let` is false for infer_lambda, true for infer_let.
- `lean_local_ctx_mk_local_decl` / `_with_value` are written as module-local (NOT `#[no_mangle]`) Rust fns returning a `(fvar, new_lctx)` pair built from the real Lean exports (aliased via link_name), because `lean_local_ctx_mk_local_decl` is also a Lean stdlib export and an exported shim would collide.

## Session 2 — bugs that made Kernel.whnf/check/isDefEq fully pass (all originally-failing tests green)
The dominant bug class: several Lean `@[export]` fns take `Expr` **by value → CONSUME (decrement) it**, but the extern block declared them borrowing, so they decremented shared exprs → pervasive use-after-free. Fixed via `lean_inc`-before wrappers:
- `lean_expr_hash` (`def hashEx : Expr → UInt64`, also was declared `u32` not `u64`) — every `ExprKey` cache hash decremented the key. Wrapper `expr_hash`.
- `lean_expr_has_fvar` / `lean_expr_has_expr_mvar` (`Expr → Bool`) — wrappers `expr_has_fvar`/`expr_has_expr_mvar`.
Other fixes:
- **whnf_core `Let` branch used `get_binding_body` (field 2 = the *value*) instead of `get_let_body` (field 3)** → `let g := v; body` reduced to `v`. This one fix made Rat (`mul`/`div`) AND String (kernel2: `String.length`/`decEq`) work — all use `let`-telescopes. `Expr.letE` = [name,type,value,body]; Lambda/Pi body = field 2, Let body = field 3.
- **`lean_kernel_check` passed empty lparams** → rejected any universe param. Must use `check_ignore_undefined_universes` (m_lparams=null) to match C++ `check(expr)` one-arg overload. Fixed grind polymorphic "invalid reference to undefined universe level parameter".
- **beta in whnf_core**: instantiate the first `m` args (application order) via `instantiate_rev(body, m, args[0..m])`; earlier code sliced the wrong args + spurious `.rev()`.
- `reduce_bin_nat_op`/`reduce_nat_succ`: `get_nat_val` returns a BORROWED nat inside the literal — don't `lean_dec` it, and keep the literal alive while using it.
- `lean_lit_type`: must read the inner Literal tag (field 0) and return `Expr.const Nat/String`, NOT a bare Name.
Debugging technique that works despite layout-sensitive UAF (eprintln/alloc masks it): a raw `write(2)` no-heap refcount tracer (`dbg_rc`) + a global call-count window to catch infinite recursion. Harness: `srghmascripts/kernel_tc_suite.sh` (28 cases, each own process). All originally-failing tests pass: kernel1/kernel2/2672/isDefEqProjIssue/10475/cbv_*/grind_*/lake builtin-lint.

## Remaining to remove the 3 C++ files (NOT yet done)
type_checker.cpp still hosts `environment::add_axiom/add_definition/add_theorem/add_opaque/add_mutual` (lines ~158-260) + the `type_checker` C++ class (used by inductive.cpp's `add_inductive`) + `lean_cxx_add_*` bridges + `initialize_cxx_type_checker_globals` + `lean_kernel_local_ctx_mk_pi`. The add path is dispatched from kernel_environment.rs/library_elab_environment.rs `kernel_add_dispatch` → `lean_cxx_add_*`. To remove type_checker.cpp+inductive.cpp: port add_axiom/definition/theorem/opaque (use safety modes: unsafe defs add-then-check in new env; `check_constant_val` = check_name+check_dup_univ+check_no_metavar_no_fvar+check(type)+ensure_sort), port add_mutual + add_inductive (big, ~700 lines, nested-inductive elim), port add_quot, then switch dispatch to the Rust `add_*_impl`. `add_decl_impl` (Rust, line ~4217) is a NOT-WIRED draft and is buggy (treats `Declaration` as `ConstantInfo`; always SAFE). exception.cpp is used across all runtime/ → remove last. HIGH RISK: every declaration uses the add path; validate with a full test run.

## Session 3 — add-declaration path port (axiom/def/theorem/opaque) — PARTIAL
Ported `environment::add_axiom/add_definition/add_theorem/add_opaque` to Rust `add_decl_impl` in
kernel_type_checker.rs, plus helpers `check_constant_val`, `check_no_metavar_no_fvar`,
`check_name_dup` (via `env_find`), `check_duplicated_univ_params`, `check_decl_value`, and a
unified dispatcher `lean_rust_add_decl(env, decl, check)` (kinds 0-3 → Rust, 4/5/6 →
lean_cxx_add_quot/mutual/inductive_only). Both dispatch sites (kernel_environment.rs
`add_decl_dispatch`, library_elab_environment.rs `kernel_add_dispatch`) now just call
`lean_rust_add_decl`. Key facts learned:
- For decl kinds 0-3 a `Declaration` IS a `ConstantInfo` (C++ `constant_info(declaration)` reuses
  `d.raw()`); use the `lean_constant_info_*` accessors directly on `decl`.
- `*Val` layout NESTS `constant_val` at field 0; the **value of a def/thm/opaque is field 1 of
  the val** (`ci_to_val(decl).field[1]`), NOT field 3 — getting this wrong reads garbage-as-Expr
  and hangs `tc.check`. (`lean_constant_info_get_type` = `ci_constant_val.field[2]`, added as a
  shim — it was a phantom undefined extern.)
- `lean_environment_add` = Kernel.Environment.add (pure insert, consumes env+cinfo); use `env_find`
  for the dup check (don't trust the `lean_environment_check_name` extern). Empty lctx via
  `lean_mk_empty_local_ctx(lean_box(0))`. Unsafe defs: check type → add → check value in new env.
- Refcount contract: dispatch CONSUMES env, BORROWS decl. add_decl_impl: tc incs env (drops on
  `?`-return automatically), `lean_inc(decl)` before `lean_environment_add` (which consumes both),
  on error `lean_dec(env)` (the variant carries its own inc'd env).

STATUS: gated behind `const RUST_ADD_SIMPLE` in kernel_type_checker.rs (currently **false** =
C++ path = ALL GREEN: 28/28 harness, kernel1/2/2672/structure/cbv/grind fast). Flipping to **true**
crashes on `structure S where x : Nat` (fast minimal repro) — and the ROOT CAUSE is now localized
precisely (session 3b):
- Bisected via gated `do_check`/`check_constant_val`/`is_prop` toggles + a no-alloc `write(2)`
  `dbg_rc` tracer. Found: the crash is a **refcount over-decrement in the Rust infer path** for
  **Pi types (expr kind 7)** — `infer_type_core → infer_pi` decrements its argument `e` by 1 for
  certain Pi-typed exprs. It surfaces during the add path because `is_prop` (theorem check) and
  `check_constant_val`'s `tc.check(type)` both `infer` the declaration's type, which for most decls
  is a `∀`/arrow (Pi). `e` is borrowed (the elaborator's shared decl type) → over-free →
  latent heap corruption that crashes after many declarations (layout-sensitive; gdb/secure-mimalloc
  mask it; markers shift the crash). The kernel debugging suite never hit it because it only
  `Kernel.check`s small standalone exprs, not full Pi-typed declaration types.
- IMPORTANT: env/Declaration objects read a bogus NEGATIVE rc via the offset-0 `dbg_rc` (verified:
  toggle-FALSE/green shows the same -3/-2), so only trust rc DELTAS on plain Expr objects, and
  ignore absolute env/decl rc.
## Session 4 — CORRECTED diagnosis (the infer_pi theory from 3b was WRONG)
- **The 3b "infer_pi over-decs e_orig" theory was a MISREAD of multi-threaded refcounts.** A
  negative rc (e.g. -3) is an MT/atomic refcount stored NEGATED (magnitude = count); `lean_inc`
  makes it MORE negative (-3→-4 = count 3→4). Tracing e_orig across infer_pi shows 35/35 entry/exit
  pairs perfectly net-zero — infer_pi is balanced and is NOT the crash site.
- **The crash reproduces with RUST_ADD_SIMPLE=false (C++ add path)** via the kernel debugging API
  alone: `Kernel.check env {} ci.type` over real declaration TYPES cores after ~15-20 DIVERSE checks.
  So it is a latent bug in the COMMITTED-green Rust `Kernel.check`/infer path, not add-specific —
  the test suite just never stresses Kernel.check on complex types. Repro file: loop
  `for (_,ci) in env.constants.toList do Kernel.check env {} ci.type`. `[0:20]`→139, `[0:10]`→ok.
- **It is a layout-sensitive TRANSIENT double-free.** Checking ONE real type 60× is CLEAN; 20 DIVERSE
  types once each CRASHES (diverse freelist traffic surfaces the corrupted node). `∀x:Nat,Nat` 2000×
  and `mkConst List [0]` 200× are both CLEAN (so infer_pi + infer_constant + lparam-instantiate +
  lctx_mk_local_decl + Sort are all fine in isolation).
- **ALL standard tools MASK it:** default mimalloc release = crash; MI_SECURE / MI_DEBUG_FULL / gdb
  shift or hide it; valgrind with MI_TRACK_VALGRIND=ON runs CLEAN (no error reported, only ~71 leaked
  objs = the +1 leaks below). USE_MIMALLOC=OFF does NOT link (Rust runtime calls `mi_malloc_small`
  directly). mimalloc release does not self-report double-frees. So allocator tooling is a dead end;
  must find by refcount reasoning / no-alloc write(2) tracer.
- **Audited BALANCED (not the bug):** infer_pi, infer_app (both modes), infer_constant,
  lctx_mk_local_decl (wrapper at L1041 correctly incs lctx/id/name/ty before consuming exports),
  ensure_sort_core/ensure_pi_core, env_find (returns OWNED info; dec is correct),
  lean_instantiate_type_lparams (BORROWS info+levels, incs result), EquivManager add_equiv
  (to_node_ref incs before storing; local expr_hash reads the cached hash field, does NOT call the
  consuming lean_expr_hash), is_def_eq_core TOP LEVEL (every return decs t_n/s_n exactly once).
- **Found systematic +1 LEAKS (real, fixable, but NOT the crash — leaks raise rc, safe):**
  `ensure_sort_core`/`ensure_pi_core` BORROW their first arg (inc in the is_sort/is_pi fast path,
  whnf in the slow path) but EVERY caller treats them as CONSUMING — never decs the inferred input
  (infer_pi L2056 d_type & L2073 inst_type; infer_app L2096 fn_type; infer_lambda L2014 & infer_let
  L2184 discard the RESULT too; infer-only infer_app L2151 `inst`). Also `lean_kernel_check/whnf/
  is_def_eq` (L4174+) never dec their OWNED args `a`/`b`/`lctx` (opaque @[extern] passes args owned)
  → +1/call leak (confirmed: piE rc grows +1 per Kernel.check). Fix = make ensure_*_core consume
  (drop the fast-path inc, add lean_dec in the whnf branch) OR dec the inputs at call sites; and dec
  a/b/lctx in lean_kernel_*.
- **NEXT (the over-free):** must be inside an is_def_eq_core SUB-function reached by complex types:
  quick_is_def_eq, lazy_delta_reduction, whnf_core, is_def_eq_app, try_eta_expansion_core,
  try_eta_struct_core, lazy_delta_proj_reduction, is_def_eq_proof_irrel, reduce_recursor,
  unfold_definition. Look for `lean_dec` of a value obtained from a BORROWING accessor
  (get_app_fn/get_app_arg/get_binding_domain/body/get_proj_expr/list_head) without a prior inc, or a
  double-dec across a `&mut`-reassign helper (lazy_delta_*). Best method: no-alloc write(2) rc tracer
  on a candidate sub-fn while running the `[0:20]` repro (toggle OFF). add_mutual/add_inductive/
  add_quot still C++. Build MUST be restored to default before any test/commit: USE_MIMALLOC=ON,
  MI_TRACK_VALGRIND=OFF, MI_SECURE=OFF (verified green: 28/28 harness).

## Session 4b — leak fix DONE + validated; over-free still present, 20 fns audited
DONE (committable-quality, validated green: 28/28 harness + 18/18 ctest `kernel|isDefEq|2672|
leanchecker`): made `ensure_sort_core`/`ensure_pi_core` CONSUME their first arg (dropped the
fast-path `lean_inc(e)`, added `lean_dec(e)` after the `whnf(e)` borrow). Fixed the call sites that
DISCARD the result (infer_lambda L2016, infer_let L2186 → `lean_dec(tc.ensure_sort_core(...)?)`),
and REMOVED the now-double-free `lean_dec(sort)` in check_constant_val (ensure_sort_core consumes
`sort`). Also `lean_kernel_check`/`whnf`/`is_def_eq` (L4174+) now `lean_dec` their OWNED args
`a`/`b`/`lctx` (opaque @[extern] passes args owned — confirmed: piE rc grew +1/call before, flat
after). EFFECT: crash threshold for `Kernel.check env {} ci.type` over real types moved from ~20
constants to ~1000 (≈50× rarer) — i.e. the +1 leaks drove most of the freelist churn, but a
residual OVER-FREE remains ([0:2000] / [0:1000] / [1000:2000] still core-dump; [0:20] no longer).
ADDITIONAL leaks found but NOT yet fixed (same pattern, deeper/rarer paths): `to_cnstr_when_K_impl`
(L3926) BORROWS `e` (inc-to-return) in 4 branches but CONSUMES in the cnstr branch → inconsistent;
caller passes `major` OWNED so the borrow branches leak it (fix: drop the 4 `lean_inc(e)` so it
consistently passes `e` through = consume, matching `to_cnstr_when_structure_impl`).
`try_eta_expansion_core` (L3089) leaks `s_inferred` (infer_type then whnf, never decs s_inferred).
AUDITED BALANCED (no over-free): infer_pi/app/constant/lambda/let, lctx_mk_local_decl, ensure_*,
env_find, instantiate_type/value/expr_lparams, add_equiv/EquivManager, is_def_eq_core(top),
quick_is_def_eq, is_def_eq_binding/args/app/proof_irrel/unit_like, whnf_core (incl. beta + recursor
inc/dec pair — reduce_recursor/inductive_reduce_rec_impl BORROW `e`), unfold_definition,
reduce_proj_core, reduce_recursor, to_cnstr_when_structure_impl, mk_nullary_cnstr_impl.
STILL UNAUDITED (candidates for the residual over-free): whnf_fvar, lazy_delta_reduction_step,
lazy_delta_proj_reduction, try_eta_struct_core, expand_eta_struct_impl, to_cnstr_when_structure's
`is_constructor_app_impl`, reduce_nat/reduce_bin_nat_op (claimed fixed earlier — re-verify), the
quot reduction (STUBBED in reduce_recursor L2466 — "fall through", may mis-handle quot types),
infer_proj. Repro (toggle OFF): `for (_,ci) in (←getEnv).constants.toList do Kernel.check env {}
ci.type` over [0:2000] cores. Tools STILL mask it (valgrind/MI_TRACK_VALGRIND clean). Hypothesis to
test: fixing ALL remaining leaks may push the threshold past any real workload, OR there is one
genuine over-free in an unaudited fn (look for `lean_dec` of a value from a BORROWING accessor
without a prior inc, or a `&mut`-reassign helper that decs the old value AND the caller decs too).

## Session 4c — TDD regression harness for the kernel type-checker
Two regression layers now protect fixed problems and track the open one:
- `srghmascripts/kernel_tc_suite.sh` (GREEN, 31/31): 28 small-expr whnf/check/isDefEq cases
  (protect the session-2 refcount fixes) + NEW `check-pi`/`check-lam`/`check-let` cases that
  exercise infer_pi/infer_lambda/infer_let + ensure_sort_core/ensure_pi_core — these guard the
  session-4 CONSUME-semantics leak fix (a revert reintroduces the +1 leaks and these would change
  behavior). Expected outputs: check-pi=`Sort.{imax 1 1}`, check-lam=`Nat -> Nat`, check-let=`Nat`.
- `srghmascripts/kernel_bulk_check.sh` (RED — the over-free TDD target): sweeps
  `Kernel.check env {} ci.type` over real `import Lean` constant types in ranges (default 200 1000)
  and asserts each range completes (`DONE`) with no core dump. Currently ALL ranges FAIL. Must go
  GREEN when the residual over-free is fixed. Also guards the leak fix (reverting it collapses the
  crash threshold so even small ranges fail). 90s/range timeout keeps it under the 4-min budget.
- NEW symptom observed: `[0:50]` HANGS (240s timeout) instead of core-dumping, while `[0:200]`+
  core-dump (SIGSEGV) — the same layout-sensitive corruption manifests as either a reduction hang
  or a segfault depending on which constants are hit. So a constant in toList[0:50] of `import Lean`
  is a good focused repro for tracing (it hangs → easier to attach/observe than a fast crash).

## Session 4d — FOUND a real over-free: infer_proj wrong-order mk_proj
`infer_proj` (kernel_type_checker.rs ~L2336, the dependent-field skip loop, `has_loose_bvars(body)`
branch) built `proj_i = lean_expr_mk_proj(proj_sname, nat, proj_e)` and THEN did
`lean_inc(proj_sname); lean_inc(proj_e)` — but mk_proj CONSUMES its args and proj_sname/proj_e are
BORROWED from `e`. So mk_proj decremented them FIRST (possibly to 0 → freed) and the inc then wrote
to freed memory → freelist corruption. FIX: moved the two `lean_inc` BEFORE the mk_proj call.
Reached only when checking a type with a DEPENDENT structure projection (field type mentions an
earlier field via `self.field`, e.g. `Fin (n+1)` in `structure Dep where n; v : Fin (n+1)`) at
field idx ≥ 1 — rare among declaration types → matches the rare/probabilistic bulk crash.
General lesson / scan: the anti-pattern is "`X = lean_*_mk_*(borrowed args...)` followed by
`lean_inc(those borrowed args)`". A grep for a `mk_` builder line immediately followed by `lean_inc`
found only this site + a false positive in try_eta_expansion_core (there the incs precede mk_lambda,
the actual consumer — correct).
NOTE: a hand-built repro `structure P where a:Nat; b:Nat; c:Nat` FAILS TO PARSE (the `;` inline) →
P.mk undefined → checking `Expr.proj P i (P.mk..)` then tests the UNKNOWN-CONST error path (also
crashes/hangs — possibly a separate error-path bug, unverified), NOT real proj inference. Use
newline-separated fields. Valid proj checks return correctly (`(P.mk 1 2 3).i` → `Nat`).
VALIDATED: infer_proj fix passes 96/96 ctest (`kernel|isDefEq|2672|leanchecker|struct|proj|Sigma`)
+ 32/32 harness. Regression test added: `kernel_tc_suite.sh` `check-dep-proj` (loops `CW depProj`
300× where depProj = `(Sigma.mk Nat (fun _=>Nat) 1 2).snd` = a valid dependent proj hitting the
fixed mk_proj branch; whnfs to `Nat`). Added `CW` helper (check then whnf the result type).
BUT the BULK over-free is STILL PRESENT after the infer_proj fix (full type stress over 203951 real
types still cores at ~120-220s) — so infer_proj was a genuine but DIFFERENT bug; the bulk crash
cause is still unfound. Error-path over-free RULED OUT (hammering Kernel.check on FunExpected /
UnknownConstant / AppTypeMismatch / loose-bvar exprs 1500× each = all clean). The bulk over-free
remains: rare, probabilistic (ASLR-dependent — same binary/range crashes some runs, completes
others), manifests as either SIGSEGV or a 0%-cpu sleep-hang; gdb masks it (layout differs). Captured
by `kernel_bulk_check.sh`. Remaining unaudited over-free candidates: get_rec_rule_for_impl (does it
return BORROWED rule? `lean_dec(rule)` would over-free a shared env recursor rule — diverse
recursors deplete), lazy_delta_proj_reduction, try_eta_struct_core/expand_eta_struct_impl, the quot
reduction stub, whnf_fvar value branch.

## Session 4e — 4 more defeq-path leaks fixed; ENTIRE Rust surface audited; over-free still unfound
Fixed 4 more clear leaks (missing dec of an owned value handed to a borrowing fn); validated
176/176 ctest (`kernel|isDefEq|2672|leanchecker|string|eta|proj|struct`) + 32/32 harness:
lazy_delta_proj_reduction (dec t_proj/s_proj), try_string_lit_expansion_core (dec whnf_ctor),
whnf_fvar (dec val), try_eta_expansion_core (dec s_inferred). The previously-listed "candidates"
above are now all AUDITED CLEAN: get_rec_rule_for_impl incs the rule (OK); try_eta_struct_core and
expand_eta_struct_impl order their mk_proj incs CORRECTLY (incs before the call — only infer_proj had
the wrong order, fixed in 4d). So the WHOLE kernel_type_checker.rs type-checking surface is audited;
the bulk over-free is NOT a refcount mistake in this file.
PROOF leaks ≠ the over-free (they only shift layout): under `setarch -R` (ASLR off) the same
`[0:8000]` went 4/4 crash → 0/6 after these leak fixes, yet the FULL env (203951 types) still crashes
3/3 (now 17-49s, earlier than the pre-fix 122-214s). Crash TIME varies even with ASLR off → also
multithread-scheduling sensitive. `kernel_bulk_check.sh` now defaults to `all` (sweep every constant
type) which reproduces RELIABLY (~50s); numeric ranges are flaky.
WHERE THE OVER-FREE MUST BE (not yet checked): (a) a #[no_mangle] *Val-accessor SHIM with a wrong
field OFFSET for a rare layout (lean_recursor_val_get_* / lean_inductive_val_get_* /
lean_constructor_val_get_* / lean_constant_info_to_*_val) — reads garbage → used as ptr → corrupt;
(b) the C++ sret mk_binding ABI (lean_local_ctx_mk_pi); (c) a borrowed/owned mismatch in a trusted
`lean_*` extern impl in another rs file (kernel_expr.rs/kernel_instantiate.rs/kernel_environment.rs).
DECISIVE TOOL NOT YET TRIED: AddressSanitizer (poison-on-free + quarantine catches the UAF at the
exact load, layout-independent). valgrind/gdb/secure-mimalloc all MASK it. Blocker: USE_MIMALLOC=OFF
won't link (Rust calls mi_malloc_small directly); need USE_MIMALLOC=ON + MI_TRACK_ASAN=ON +
`-fsanitize=address` on C++ runtime AND `-Zsanitizer=address` (nightly rustc) on the Rust runtime.

## Session 5 — over-free detector built; bulk crash hunted hard, NOT fully fixed (reverted clean)
GOAL was the bulk `Kernel.check` over-free (the layout-sensitive UAF; `kernel_bulk_check.sh [all]`
cores). Built a deterministic **over-free detector** in the Rust runtime (all reverted — rebuild
from this recipe if resuming):
- `runtime_object_rc.rs`: gate `const UAF_DETECT`. Hook the PHYSICAL free choke points
  `lean_dealloc` + `lean_free_small_object`: instead of freeing, POISON `(*o).rc = i32::MIN` and
  park the block in a bounded quarantine (open-addressing set `QSET` 2^21 + ring `QRING` 2^18;
  evict oldest via `mi_free`). Hook at physical-free (NOT at `lean_dec_ref_cold`) so children are
  already dec'd → only raw blocks parked → bounded ~30MB (parking earlier retained whole subtrees →
  OOM). Capture free-site glibc `backtrace()` for the suspect shape (tag 0, other==3) into a side
  ring for the report.
- `lib.rs`: in the Rust hot paths `lean_inc_ref_n` / `lean_dec_ref`, `if (*o).rc==i32::MIN
  {report_uaf}` → catches a later inc/dec of a parked (freed) object = use-after-free. Plus a
  thread-local `UAF_CUR_FN` + RAII `UafFnMark` set at the entry of marked fns (infer_type_core,
  whnf_core, is_def_eq_core, instantiate1/rev, lazy_delta_step, reduce_recursor, lean_kernel_check
  whole-fn, the kcheck epilogue decs, TC::new incs) → report names where the over-decrement happened.
- Symbolization: the `.so` is STRIPPED of DWARF (`readelf -S` shows no .debug_*; addr2line/
  llvm-symbolizer give `??`). Only `#[no_mangle]` syms are in the table → nearest-symbol is
  MISLEADING (everything resolves to lean_stack_has_space/lean_box_uint64/scope_max_heartbeat_push).
  Use glibc `backtrace_symbols_fd` for `binary(+0xfileoffset)`; named C frames (lean_kernel_check,
  lean_apply_7, l_Lean_Elab_*) DO resolve. gdb masks the crash (different layout). `setarch -R`
  (ASLR off) makes the native crash far more deterministic but crash TIME still varies (thread
  scheduling). USE_MIMALLOC=OFF won't link (Rust calls mi_malloc_small directly).
FINDINGS:
- Over-free #1 (detector-confirmed): `lean_dec(kernel_env)` in lean_kernel_check decs an
  already-freed object. BUT the ABI says kernel_env is OWNED: `elab_add_decl_impl` comment +
  code prove `lean_elab_environment_to_kernel_env` (= `toKernelEnv env := env.checked.get`)
  CONSUMES env and returns an OWNED kernel env (it `lean_inc_ref(elab_env)` before the call to
  survive the consume, and passes the result to the consuming add). So removing the dec only LEAKS
  it and did NOT fix the native crash. DEBATED/unresolved → reverted.
- Over-free #2 (the dominant one): victim is a shared **tag 0, 3-obj-field** ctor
  `[ptr, ptr, boxed-1]` (rc poisoned to 0x80000000 confirmed). REAL + kernel-triggered: env
  iteration (`for ci in env.constants.toList`) and `ci.type` access are CLEAN under the detector;
  only adding `Kernel.check env {} ci.type` cores → discriminating test C. Freed by the ELABORATOR's
  `lean_dec_ref_cold`→`lean_del_core` (a legit dec of an under-referenced object), NOT inside
  lean_kernel_check (whole-fn marker never caught the free). So it's a MISSING INC (no call-site for
  the detector to point at).
- RULED OUT for #2: `env_find` (incs env+name to feed find?'s consume — balanced),
  `lean_environment_find` (= `Environment.find? := env.constants.find?' n`, @[export], consumes
  env+n), `to_kernel_env`, and — decisively — `kernel_env.constants` (field 0 of Kernel.Environment)
  rc is NEVER net-changed across a Kernel.check call (tracked rc before/after; 0 deltas even in the
  crashing full-env run). So the kernel's env handling is balanced; #2 is elsewhere.
NEXT IDEAS for #2: the victim is likely the ELAB `Environment.constants` SMap (a DIFFERENT object
than kernel_env.constants) or another shared 3-field struct; audit the ported runtime helpers the
elaborator/kernel share (kernel_expr.rs/kernel_instantiate.rs/kernel_environment.rs/library_elab_
environment.rs and SMap/Task ops), or do a full AddressSanitizer build (USE_MIMALLOC=ON +
MI_TRACK_ASAN=ON + -fsanitize=address on C++; Rust crate needs nightly `-Zsanitizer=address` which
this toolchain lacks — partial C++/mimalloc ASan may still catch it). `kernel_bulk_check.sh` now
defaults to `all` (reliable repro). Tree restored to committed-green (8e151e209e), 32/32 harness.

See [[feedback-no-full-tests]].
