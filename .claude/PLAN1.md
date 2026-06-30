src/rust/leanh/src/lib.rs should contain only these functions (structures - dont change) (they are hardcoded into EmitRust)

Which are: lean_alloc_closure lean_alloc_ctor lean_apply_1 lean_apply_2 lean_apply_3 lean_apply_4 lean_apply_... lean_apply_m lean_box lean_box_float lean_box_float32 lean_box_uint32 lean_box_uint64 lean_box_usize lean_closure_set lean_cstr_to_nat lean_ctor_get lean_ctor_get_float lean_ctor_get_float32 lean_ctor_get_uint8 lean_ctor_get_uint16 lean_ctor_get_uint32 lean_ctor_get_uint64 lean_ctor_get_usize lean_ctor_release lean_ctor_set lean_ctor_set_float lean_ctor_set_float32 lean_ctor_set_tag lean_ctor_set_uint16 lean_ctor_set_uint32 lean_ctor_set_uint64 lean_ctor_set_uint8 lean_ctor_set_usize lean_dec lean_dec_ref lean_dec_ref_known lean_del_object lean_float_once lean_float32_once lean_inc lean_inc_n lean_inc_ref lean_inc_ref_n lean_io_result_is_error lean_io_result_mk_ok lean_is_exclusive lean_is_scalar lean_mark_persistent lean_mk_string_unchecked lean_obj_once lean_obj_tag lean_uint16_once lean_uint32_once lean_uint64_once lean_uint8_once lean_unbox lean_unbox_float lean_unbox_float32 lean_unbox_uint32 lean_unbox_uint64 lean_unbox_usize lean_unsigned_to_nat lean_usize_once lean_io_result_get_value lean_setup_args lean_initialize lean_initialize_runtime_module lean_mk_string lean_io_mark_end_initialization lean_io_result_is_ok lean_init_task_manager lean_run_main lean_finalize_task_manager lean_io_result_show_error

Move all other public helper implementations out of leanh into src/rust/runtime/src/leanh_extra.rs

, then fix imports (ffi/**/*.rs, srghmascripts/regenerate_module_tree.ts) so generated crates do not depend on runtime-only helpers through crate::leanh.

(they were extracted from src/rust/runtime/src/{runtime,kernel,library} and later will return there)

Regard current dir structure as correct and dont do any renamings/movings (If found error - tell user)

EmitRust before was generating `use crate::lean_imports_rust::path::to::current::file::{f1,f2}` but now should just use top level ffi.rs file that per crate. which is `use create::ffi::{f1,f2}`

NOTE that we are fully moving from cpp, we should not use extern "C" or [no_mangle] (the only extern "C" allowed is for `uv_*` or `__gmp`)

## Test Plan

- Run focused Rust checks from src/rust:
  - cargo check -p leanh
  - cargo check -p gen_init
  - cargo check -p gen_std
  - cargo check -p gen_lean
  - cargo check -p runtime (rn it doesnt depend on gen_init, but will be)
  - cargo check -p lake
  - cargo check -p lean_checker
  - cargo check -p lean_ir
  - cargo check -p lean_shell
  - cargo check -p leanc

## Assumptions

- runtime and runtime::leanh_extra should depend on leanh create
- gen_*/src/ffi{.rs,**/*.rs} may depend on leanh and runtime::leanh_extra

------------

# Split leanh ABI From Runtime Helpers

## Summary

Keep the current directory layout (src/rust/{leanh,runtime,gen_init,gen_std,gen_lean,lake,...}) and make leanh the small ABI crate used by EmitRust. Move every public helper not in the user-approved ABI list from leanh/src/
lib.rs into runtime/src/leanh_extra.rs, then update generated import plumbing so extra helpers are reached via crate::ffi::{...} and FFI modules may call runtime::leanh_extra.

Current repo errors to fix as part of this:

- Workspace still lists stale members like lean_gen_init, lean_runtime, lean_runtime_common.
- Several Cargo.toml files still use old package/path names.
- leanh/Cargo.toml is currently copied from lean_gen_std.
- gen_*/src/lib.rs still includes generated files from old ../../lean_runtime/src/gen/... paths.

## Key Changes

- Fix Cargo metadata without moving directories:
  - Workspace members become leanh, runtime, gen_init, gen_std, gen_lean, lake, lean_checker, lean_ir, lean_shell, leanc.
  - Package names become the names used by the test plan: leanh, runtime, gen_init, gen_std, gen_lean, lake, lean_checker, lean_ir, lean_shell, leanc.
  - Remove all lean_runtime_common dependencies.
  - Add leanh dependency everywhere generated/runtime code needs crate::leanh.
  - Add runtime dependency only to generated crates that need runtime::leanh_extra.
  - For this task, do not make runtime depend on gen_*; otherwise gen_* -> runtime -> gen_* becomes a Cargo cycle.

- Split leanh/src/lib.rs:
  - Keep ABI layout structs/types/constants required by the retained functions.
  - Keep only the approved public ABI functions, including generated lean_apply_5 through lean_apply_16 plus lean_apply_m.
  - Move all other public helper functions to runtime/src/leanh_extra.rs.
  - Move any private helper used only by moved functions into leanh_extra.rs; keep private helpers in leanh only when needed by retained ABI functions.
  - In runtime/src/lib.rs, add pub mod leanh_extra; and pub mod leanh { pub use leanh::*; }.

- Fix generated crate imports:
  - Replace pub use lean_runtime_common::leanh::*with pub use leanh::*.
  - Remove lean_imports_rs module usage from crate roots where it only existed for old generated imports.
  - Update srghmascripts/regenerate_module_tree.ts so generated imports use use crate::ffi::{f1, f2};, not crate::lean_imports_rs::....
  - Update generated ffi/**/*.rs files to import ABI items from crate::leanh and runtime-only helpers from runtime::leanh_extra.
  - Keep extern "C" / #[no_mangle] out of this layer, except existing allowed low-level uv_* / __gmp bindings.

- Fix generated module roots:
  - gen_init/src/lib.rs, gen_std/src/lib.rs, gen_lean/src/lib.rs, and lake/src/lib.rs should expose pub mod gen; from local src/gen.rs.
  - Their local gen.rs files should describe the local src/gen/... tree and have the existing allow attributes at the top.
  - Replace stale include!("../../lean_runtime/src/gen/...") with local module paths under each crate’s own src/gen.

## Test Plan

Run from src/rust:

- cargo check -p leanh
- cargo check -p gen_init
- cargo check -p gen_std
- cargo check -p gen_lean
- cargo check -p runtime
- cargo check -p lake
- cargo check -p lean_checker
- cargo check -p lean_ir
- cargo check -p lean_shell
- cargo check -p leanc

Also run audits:

- rg "lean_runtime_common|lean_imports_rs|lean_imports_rust" src/rust srghmascripts
- rg "extern \"C\"|no_mangle|export_name" src/rust/{gen_init,gen_std,gen_lean,lake,runtime,leanh}/src
- Script-check that public leanh functions exactly match the approved ABI list.

## Assumptions

- Directory names are authoritative and should not be moved.
- Cargo package names should match the requested cargo check -p ... names.
- Generated crates may depend on runtime::leanh_extra; therefore runtime must not depend on generated crates in this same step.
- Any later runtime-to-generated dependency needs a separate design to avoid a Cargo cycle.
