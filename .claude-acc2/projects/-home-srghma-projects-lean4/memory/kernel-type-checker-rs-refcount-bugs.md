---
name: kernel-type-checker-rs-refcount-bugs
description: Status + root causes for the Rust kernel type-checker port (rust-rewrite branch)
metadata:
  type: project
---

`src/rust/lean_runtime/src/kernel_type_checker.rs` (port of `src/kernel/type_checker.cpp`,
staged change) was added in one big swoop and had pervasive ownership/ABI bugs causing
segfaults/hangs in `Kernel.whnf/check/isDefEq` (elab/kernel1,kernel2, elab_bench/cbv_*, etc.).

Regression harness: `srghmascripts/kernel_tc_suite.sh` (each case in its own process). As of
last session: **14/15 pass**; only `whnf-rec-strlen` fails. Real tests: kernel1, elab/2672,
elab/isDefEqProjIssue now PASS. Remaining failures: kernel2 (String), elab/10475 +
elab_bench/cbv_* + grind_* (heavy-term crash, suspected OOM from leaks — fixes in progress).

## Confirmed conventions (ground truth)
- `Except` tags: `error`=0, `ok`=1. (C++ catch_kernel_exceptions: mk_cnstr(1,a)=ok, mk_cnstr(0,..)=error.)
- ALL `lean_expr_mk_*`/`lean_level_mk_*`/`lean_name_mk_*`/mk_proj/mk_bvar **CONSUME** every object arg (obj_arg). So inc borrowed args before; NEVER `lean_dec` an arg after handing it to a mk_*.
- `lean_environment_find` CONSUMES env+name, returns **Option ConstantInfo** (must unwrap `.some`). Wrapper `env_find` does inc+unwrap.
- `lean_nat_*` arithmetic BORROW. `lean_instantiate_value/type_lparams`, `instantiate`/`instantiate1`/`instantiate_rev`/`abstract` BORROW (@&).
- `instantiate` takes Array; single subst = `lean_expr_instantiate1`. `instantiate_rev`/`abstract` (e,n,ptr) link to `_ptr` symbols.
- `lean_expr_mk_bvar` takes a **Nat object** (obj_arg), not u32.
- `lean_expr_get_app_fn` = ONE app layer, NOT the spine head. Use helper `app_head(e)` (walks `while is_app`) wherever C++ `get_app_fn` (recursive head) is meant: get_rec_rule_for, to_cnstr_when_K/structure, is_delta, try_eta_struct, try_unfold_proj_app, is_constructor_app, is_eager_reduce_expr, lazy-delta t_fn/s_fn, infer_proj I.
- `mk_bool` must return `Expr.const Bool.true/false` (globals G_EXPR_BOOL_TRUE/FALSE), NOT a Bool scalar.
- Cache-INSERT paths: `OwnedLean::new(r)` already inc's for the cache; return the ORIGINAL owned ref — do NOT `lean_inc` again (that leaks 1 per cached expr → OOM on big reductions). Cache-HIT paths DO inc (correct).

## Fixed (verified): Except tags, SORT double-free, env_find consume+Option-unwrap, instantiate1/instantiate_rev_ptr/abstract_ptr, mk_bvar Nat, get_app_fn→app_head (recursor + ~8 sites), mk_app/mk_lambda/mk_proj/mk_imax spurious-dec across whnf_core/unfold/recursor/eta/ctor-rebuild/infer_pi, mk_bool as Expr.const, recursor get_rec_rule head bug (the key fix that made recursors reduce), cache-insert leaks (infer/whnf/unfold) + recursor `rule` leak.

## Additional fixes (this session, all verified)
- **fvar lookup over-decrement** (the big one for any term with a non-empty local context): `lean_local_ctx_find_local_decl` shim passed lctx+fvar_id (borrowed) to `lean_local_ctx_find` which CONSUMES both → corrupted the shared lctx. Fixed by inc'ing both. This unblocked elab/10475 + the cbv/heavy tests.
- **level normalization** was fundamentally broken (caused "kernel application type mismatch", e.g. `Type (max 0 0)` vs `Type`): (a) `normalize_level` MAX branch only dedup'd *equal* args, not *subsumed* ones — rewrote to port C++ `normalize` (level.h): flatten+normalize+re-flatten, sort by is_norm_lt, drop subsumed (same base⇒keep max offset; explicit/numeral dropped if subsumed), added `is_explicit_level` helper. (b) double-frees in SUCC/IMAX/MAX-reduce branches: `lean_dec` after `mk_succ`/`mk_max`/`mk_imax` which CONSUME their args (the `imax l 0`→0 path is fine, decs release owned). Fixing these made cbv_decide PASS.
- cache-insert leaks (infer/whnf/unfold) + recursor `rule` leak — removed extra `lean_inc` before returning the original owned ref.

## Scorecard (originally-failing 12)
PASS now: kernel1, elab/2672, elab/isDefEqProjIssue, elab/10475, elab_bench/cbv_decide (+harness 14/15).
Still failing: **kernel2** (String), **grind_10489/grind_clean_den/grind_linarith_2** (Rat), cbv_divisors/leroy/merge_sort (re-test — likely pass now).

## Updated scorecard: 8/12 originally-failing pass (kernel1, 2672, isDefEqProjIssue, 10475, cbv_decide/divisors/leroy/merge_sort). Harness `kernel_tc_suite.sh` now has 28 cases (level/recursor/Rat/String added): **24 pass, 4 fail**.

## Remaining (pinpointed by harness; both domain-specific reduction completeness)
1. **Rat** (grind_10489/clean_den/linarith_2): `whnf-rat-litden` fails. `whnf (Rat.div (1:Rat) (2:Rat))` AND `whnf (Rat.mul (1:Rat) (2:Rat))` BOTH → `Expr.lit 1` (WRONG). But `(1:Rat)`→`Rat.mk'`, `Rat.inv (2:Rat)`→`Rat.mk'`, `Rat.divInt 1 2`→`Rat.mk'` all correct. So the bug is in `Rat.mul`/`Rat.div` → they go through `Rat.normalize`/`Rat.maybeNormalize` which computes `Nat.gcd (natAbs num) den` (e.g. gcd(2,1)=1); that gcd is surfacing as the whnf HEAD (reduce_nat fires → `lit 1`) instead of being a field of the resulting `Rat.mk'`. UPDATE: `whnf (Rat.normalize (Int.ofNat 2) 1)` → `Rat.mk' 2 1` CORRECTLY, and `Nat.gcd 2 1`→`lit 1` correct. So core Rat works; the bug is specific to **`Rat.mul`/`Rat.div`** reduction (both → `lit 1`) — likely their multi-gcd fast-path definition surfaces an intermediate `Nat.gcd` as the whnf head. Trace `whnf (Rat.mul (1:Rat) (2:Rat))` with eprintln in the whnf loop to see which unfold/reduce step yields the bare gcd.
2. **String** (kernel2): `whnf-str-len` (`"hi".length`)→`(List.brecOn.go ... (String.toList "hi") ...).1` and `whnf-str-eq` (`decide ("hello"="world")`)→`Decidable.rec ... (instDecidableEqString ...)` both stall. `String.toList "h"`→`(String.Internal.toArray "h").1` doesn't bottom out (modern ByteArray String). List.length on a *direct* list works (`[10,20,30].length`→3). Issue is the String-literal→Array→List chain.
Also: quotient (Quot.lift) reduction is still a stub in reduce_recursor.

Repro tips: minimal `Kernel.whnf/isDefEq` via `mkConst`/`mkApp*` + `ofExceptKernelException` printing `r.ctorName`; `RUST_BACKTRACE=1`; harness `srghmascripts/kernel_tc_suite.sh`; gdb `-batch -ex run -ex 'bt N'`. Level tests: `Kernel.isDefEq env {} (Expr.sort L1) (Expr.sort L2)`. NOTE: recursor-based defs in shared harness PRELUDE must be `noncomputable` (Bool.rec won't code-gen).
