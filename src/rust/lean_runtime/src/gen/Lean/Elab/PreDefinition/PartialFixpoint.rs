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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
}
