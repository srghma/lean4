// Lean compiler output
// Module: Lean.Elab.PreDefinition
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural Lean.Elab.PreDefinition.Main Lean.Elab.PreDefinition.MkInhabitant Lean.Elab.PreDefinition.WF Lean.Elab.PreDefinition.EqnsUtils Lean.Elab.PreDefinition.Eqns Lean.Elab.PreDefinition.EqUnfold
use crate::r#gen::Lean::Elab::PreDefinition::Basic::{
    initialize_Lean_Elab_PreDefinition_Basic, runtime_initialize_Lean_Elab_PreDefinition_Basic,
};
use crate::r#gen::Lean::Elab::PreDefinition::EqUnfold::{
    initialize_Lean_Elab_PreDefinition_EqUnfold,
    runtime_initialize_Lean_Elab_PreDefinition_EqUnfold,
};
use crate::r#gen::Lean::Elab::PreDefinition::Eqns::{
    initialize_Lean_Elab_PreDefinition_Eqns, runtime_initialize_Lean_Elab_PreDefinition_Eqns,
};
use crate::r#gen::Lean::Elab::PreDefinition::EqnsUtils::{
    initialize_Lean_Elab_PreDefinition_EqnsUtils,
    runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils,
};
use crate::r#gen::Lean::Elab::PreDefinition::Main::{
    initialize_Lean_Elab_PreDefinition_Main, runtime_initialize_Lean_Elab_PreDefinition_Main,
};
use crate::r#gen::Lean::Elab::PreDefinition::MkInhabitant::{
    initialize_Lean_Elab_PreDefinition_MkInhabitant,
    runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::{
    initialize_Lean_Elab_PreDefinition_Structural,
    runtime_initialize_Lean_Elab_PreDefinition_Structural,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::{
    initialize_Lean_Elab_PreDefinition_WF, runtime_initialize_Lean_Elab_PreDefinition_WF,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Eqns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_EqUnfold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Eqns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_EqUnfold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition(builtin);
}