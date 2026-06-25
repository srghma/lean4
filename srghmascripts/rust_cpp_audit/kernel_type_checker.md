# kernel_type_checker.rs audit

Original C++:
- `origin-master-src/kernel/type_checker.cpp`
- `origin-master-src/kernel/type_checker.h`
- recursor helper reference: `origin-master-src/kernel/inductive.h`

Rust:
- `src/rust/lean_runtime/src/kernel_type_checker.rs`

## 2026-06-25 findings

- `is_def_eq_app`: C++ `get_app_args` stores arguments in application order. Rust peeled app arguments from the outside in and compared without reversing, so it compared arguments in reverse order. Fixed by reversing `t_args`/`s_args` before comparing.
- `lazy_delta_reduction_step`: C++ checks same regular definition with `is_eqp(*d_t, *d_s)` over constant infos. Rust was comparing raw name pointers. Since Rust/Lean wrappers may produce distinct name objects for the same name, this can miss the same-definition argument shortcut. Fixed by using `lean_name_eq`.
- Temporary owned-result decrements after `reduce_nat`, `reduce_native`, `nat_pred`, and `reduce_proj_core` caused `elab/try_user_suggestions.lean` to segfault. Reverted. These paths intentionally still leak/retain temporaries until the exact C++ RAII/equiv-cache ownership interaction is proven safe.
- `is_eager_reduce_expr`: C++ stores `g_eager_reduce` as an `Expr.const`, but Rust stores `G_EAGER_REDUCE` as a bare `Name`. Rust incorrectly called `lean_expr_get_const_name` on the `Name`, so `eagerReduce (Eq.refl true)` arguments did not enable eager reduction. This caused `grind` certificates with huge UInt literals to unfold `Nat.beq` structurally. Fixed by comparing the application head name directly with the stored `Name`.
- `inductive_reduce_rec_impl`: C++ checks `length(const_levels(rec_fn)) == length(rec_info->get_lparams())` before `instantiate_lparams`. Rust skipped this guard. Fixed to return `None` on level-arity mismatch.

## Remaining timeout diagnosis

- `tests/elab/grind_9854.lean` was hitting a kernel deterministic timeout before the `eagerReduce` fix.
- Small repro:
  ```lean
  module
  set_option diagnostics true
  set_option maxHeartbeats 2000000
  example (x : Nat) : (2^16 : Nat) - x < (2^17 : Nat) := by
    grind only
  ```
- C++ stage0 profile keeps `Nat.rec` around 38 and does not structurally unfold `Nat.beq`.
- Broken Rust stage1 profile scaled with the literal: `Nat.rec`, `Nat.casesOn`, `Nat.beq._f`, and `Nat.beq.match_1`.
- Temporary instrumentation showed the bad Rust path first sees `Nat.beq` candidates with `has_fvar=true`; native `reduce_nat` is skipped, then lazy delta unfolds `Nat.beq` structurally.
- Direct kernel `rfl` tests for large `Nat.beq` literals are cheap in both C++ and Rust, so the remaining issue is higher-level defeq path selection or expression construction around the `Int.beq'`/`Int.Linear` proof, not the basic `Nat.beq` global.
- Forcing `eager_reduce = true` made the Rust profile match C++. The real fix was restoring `eagerReduce` detection.

## Focused tests

Passed after the retained parity edits:

```bash
CTEST_PARALLEL_LEVEL=1 ctest --test-dir build/release/stage1 \
  -R 'elab/(sync_channel|try_user_suggestions|quotInd|discrTreeIota|binop_binrel_perf_issue)\.lean|^pkg/leanchecker$' \
  --timeout 240 --output-on-failure
```

Passed after the `eagerReduce` fix:

```bash
CTEST_PARALLEL_LEVEL=1 ctest --test-dir build/release/stage1 \
  -R 'elab/(grind_9854|mvcgenTutorial|sync_channel|try_user_suggestions|quotInd)\.lean' \
  --timeout 240 --output-on-failure
```
