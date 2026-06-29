// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint
// Imports: Lean.Elab.PreDefinition.PartialFixpoint.Eqns Lean.Elab.PreDefinition.PartialFixpoint.Main Lean.Elab.PreDefinition.PartialFixpoint.Induction
use crate::r#gen::Lean::Elab::PreDefinition::PartialFixpoint::Eqns::{
    initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns,
    runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns,
};
use crate::r#gen::Lean::Elab::PreDefinition::PartialFixpoint::Induction::{
    initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction,
    runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction,
};
use crate::r#gen::Lean::Elab::PreDefinition::PartialFixpoint::Main::{
    initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main,
    runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_PartialFixpoint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
}
