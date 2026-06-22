---
name: kernel-type-checker-rs-refcount-bugs
description: Root causes of segfaults in the Rust kernel type-checker port (rust-rewrite branch)
metadata:
  type: project
---

`src/rust/lean_runtime/src/kernel_type_checker.rs` (port of `src/kernel/type_checker.cpp`)
was added in one big swoop and has pervasive ownership/ABI bugs. Tests crash in
`Kernel.check/whnf/isDefEq` (elab/kernel1.lean, kernel2.lean, elab_bench/cbv_*).

**Confirmed conventions (ground truth):**
- `Except` ctor tags: `error` = 0, `ok` = 1 (error is declared first). C++ `catch_kernel_exceptions` uses `mk_cnstr(1,a)` for ok, `mk_cnstr(0,...)` for error.
- ALL `lean_expr_mk_*` / `lean_level_mk_*` / `lean_name_mk_*` constructors take `obj_arg` — they **CONSUME** every object arg. (expr.h/level.h). So: inc borrowed args before; NEVER `lean_dec` an arg after passing it to a mk_*.
- `lean_environment_find` CONSUMES env+name and returns **`Option ConstantInfo`** (must unwrap `.some` before using accessors that expect a bare ConstantInfo).
- `lean_nat_*` arithmetic BORROW (`b_obj_arg`). `lean_instantiate_value/type_lparams` BORROW. `lean_expr_instantiate`/`instantiate1`/`instantiate_rev`/`abstract` BORROW (`@&`).
- `Expr.instantiate` takes `Array Expr`; single-subst needs `lean_expr_instantiate1`. `instantiate_rev`/`abstract` with (e,n,ptr) must link to the `_ptr` C symbols.
- `lean_expr_get_app_fn` shim = ONE app layer (immediate fn), NOT the spine head. C++ `get_app_fn` is the recursive head — walk `while is_app {}` when the head is needed (e.g. unfold_definition).

**Bug pattern:** author treated mk_* as borrowing → wrote `inc(arg); mk(...); dec(arg)` or `mk(owned); dec(owned)`. Every `dec` after a consuming mk_* is spurious → premature free / heap corruption (layout-sensitive; adding eprintln changes crash). Sites are INCONSISTENT — some compensate with `inc` AFTER mk (correct), some `dec` (buggy) — so audit each.

**Fixed so far:** Except tags (mk_except_ok + EXCEPT_*_TAG consts), SORT branch double-free, env_find (consume+Option unwrap), instantiate1/instantiate_rev_ptr/abstract_ptr link names, get_app_fn head walk in unfold_definition, 3 mk_app rebuild loops (whnf_core beta+else, unfold_definition).
**Still buggy (spurious decs):** infer_pi (~L2017/2022 mk_imax/mk_sort), eta site (~L3045 mk_app/mk_lambda), is_def_eq proj (~L3100 dec proj_idx), reduce_recursor rebuild (~L3832/3842/3851 dec rhs), ctor rebuilds (~L3973 dec app, ~L4014/4024 dec result/proj). Plus isDefEq logic still returns wrong results.

Verify with: `build/release/stage1/bin/lean /tmp/wz.lean` style minimal repros + `gdb -batch -ex run -ex bt`. Harness flags that expose crashes: `-DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true -Dcompiler.postponeCompile=false`.
