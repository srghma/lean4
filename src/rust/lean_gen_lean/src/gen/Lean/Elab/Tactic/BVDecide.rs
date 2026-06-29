// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide
// Imports: Lean.Elab.Tactic.BVDecide.BVDecide Lean.Elab.Tactic.BVDecide.Normalize Lean.Elab.Tactic.BVDecide.BVTrace Lean.Elab.Tactic.BVDecide.BVCheck
use crate::r#gen::Lean::Elab::Tactic::BVDecide::BVCheck::{
    initialize_Lean_Elab_Tactic_BVDecide_BVCheck,
    runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck,
};
use crate::r#gen::Lean::Elab::Tactic::BVDecide::BVDecide::{
    initialize_Lean_Elab_Tactic_BVDecide_BVDecide,
    runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide,
};
use crate::r#gen::Lean::Elab::Tactic::BVDecide::BVTrace::{
    initialize_Lean_Elab_Tactic_BVDecide_BVTrace,
    runtime_initialize_Lean_Elab_Tactic_BVDecide_BVTrace,
};
use crate::r#gen::Lean::Elab::Tactic::BVDecide::Normalize::{
    initialize_Lean_Elab_Tactic_BVDecide_Normalize,
    runtime_initialize_Lean_Elab_Tactic_BVDecide_Normalize,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BVDecide(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BVDecide(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_BVDecide(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BVDecide(builtin);
}
