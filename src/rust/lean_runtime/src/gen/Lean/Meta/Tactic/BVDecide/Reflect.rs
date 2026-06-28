// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical Lean.Meta.Tactic.BVDecide.Reflect.Basic Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred Lean.Meta.Tactic.BVDecide.Reflect.ReifiedLemmas Lean.Meta.Tactic.BVDecide.Reflect.Reify
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVExpr::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVLogical::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVPred::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedLemmas::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Reify::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::SatAtBVLogical::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
}
