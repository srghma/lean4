// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide
// Imports: Lean.Meta.Tactic.BVDecide.External Lean.Meta.Tactic.BVDecide.LRAT Lean.Meta.Tactic.BVDecide.Normalize Lean.Meta.Tactic.BVDecide.Attr Lean.Meta.Tactic.BVDecide.Prover Lean.Meta.Tactic.BVDecide.Counterexample Lean.Meta.Tactic.BVDecide.Reflect Lean.Meta.Tactic.BVDecide.Main Lean.Meta.Tactic.BVDecide.TacticContext
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::{
    initialize_Lean_Meta_Tactic_BVDecide_Attr, runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Counterexample::{
    initialize_Lean_Meta_Tactic_BVDecide_Counterexample,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::External::{
    initialize_Lean_Meta_Tactic_BVDecide_External,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_External,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::{
    initialize_Lean_Meta_Tactic_BVDecide_LRAT, runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Main::{
    initialize_Lean_Meta_Tactic_BVDecide_Main, runtime_initialize_Lean_Meta_Tactic_BVDecide_Main,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Prover::{
    initialize_Lean_Meta_Tactic_BVDecide_Prover,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::TacticContext::{
    initialize_Lean_Meta_Tactic_BVDecide_TacticContext,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_LRAT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Prover(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide(builtin);
}
