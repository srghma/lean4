// Lean compiler output
// Module: Lean.Meta.Constructions
// Imports: Lean.Meta.Constructions.CasesOn Lean.Meta.Constructions.NoConfusion Lean.Meta.Constructions.RecOn Lean.Meta.Constructions.BRecOn Lean.Meta.Constructions.CasesOnSameCtor Lean.Meta.Constructions.SparseCasesOn Lean.Meta.Constructions.SparseCasesOnEq
use crate::r#gen::Lean::Meta::Constructions::BRecOn::{
    initialize_Lean_Meta_Constructions_BRecOn, runtime_initialize_Lean_Meta_Constructions_BRecOn,
};
use crate::r#gen::Lean::Meta::Constructions::CasesOn::{
    initialize_Lean_Meta_Constructions_CasesOn, runtime_initialize_Lean_Meta_Constructions_CasesOn,
};
use crate::r#gen::Lean::Meta::Constructions::CasesOnSameCtor::{
    initialize_Lean_Meta_Constructions_CasesOnSameCtor,
    runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor,
};
use crate::r#gen::Lean::Meta::Constructions::NoConfusion::{
    initialize_Lean_Meta_Constructions_NoConfusion,
    runtime_initialize_Lean_Meta_Constructions_NoConfusion,
};
use crate::r#gen::Lean::Meta::Constructions::RecOn::{
    initialize_Lean_Meta_Constructions_RecOn, runtime_initialize_Lean_Meta_Constructions_RecOn,
};
use crate::r#gen::Lean::Meta::Constructions::SparseCasesOn::{
    initialize_Lean_Meta_Constructions_SparseCasesOn,
    runtime_initialize_Lean_Meta_Constructions_SparseCasesOn,
};
use crate::r#gen::Lean::Meta::Constructions::SparseCasesOnEq::{
    initialize_Lean_Meta_Constructions_SparseCasesOnEq,
    runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_NoConfusion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_RecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_BRecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Constructions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_NoConfusion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_RecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_BRecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions(builtin);
}
