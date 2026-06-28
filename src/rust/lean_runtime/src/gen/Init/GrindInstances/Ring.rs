// Lean compiler output
// Module: Init.GrindInstances.Ring
// Imports: Init.GrindInstances.Ring.Nat Init.GrindInstances.Ring.Int Init.GrindInstances.Ring.UInt Init.GrindInstances.Ring.SInt Init.GrindInstances.Ring.Fin Init.GrindInstances.Ring.BitVec Init.GrindInstances.Ring.Rat
use crate::r#gen::Init::GrindInstances::Ring::BitVec::{
    initialize_Init_GrindInstances_Ring_BitVec, runtime_initialize_Init_GrindInstances_Ring_BitVec,
};
use crate::r#gen::Init::GrindInstances::Ring::Fin::{
    initialize_Init_GrindInstances_Ring_Fin, runtime_initialize_Init_GrindInstances_Ring_Fin,
};
use crate::r#gen::Init::GrindInstances::Ring::Int::{
    initialize_Init_GrindInstances_Ring_Int, runtime_initialize_Init_GrindInstances_Ring_Int,
};
use crate::r#gen::Init::GrindInstances::Ring::Nat::{
    initialize_Init_GrindInstances_Ring_Nat, runtime_initialize_Init_GrindInstances_Ring_Nat,
};
use crate::r#gen::Init::GrindInstances::Ring::Rat::{
    initialize_Init_GrindInstances_Ring_Rat, runtime_initialize_Init_GrindInstances_Ring_Rat,
};
use crate::r#gen::Init::GrindInstances::Ring::SInt::{
    initialize_Init_GrindInstances_Ring_SInt, runtime_initialize_Init_GrindInstances_Ring_SInt,
};
use crate::r#gen::Init::GrindInstances::Ring::UInt::{
    initialize_Init_GrindInstances_Ring_UInt, runtime_initialize_Init_GrindInstances_Ring_UInt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GrindInstances_Ring_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_SInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Fin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Rat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GrindInstances_Ring(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GrindInstances_Ring_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_SInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_Fin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_Ring_Rat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring(builtin);
}
