// Lean compiler output
// Module: Init.Internal.Order
// Imports: Init.Internal.Order.Basic Init.Internal.Order.Lemmas Init.Internal.Order.MonadTail Init.Internal.Order.While Init.Internal.Order.Tactic
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
use crate::r#gen::Init::Internal::Order::Lemmas::{
    initialize_Init_Internal_Order_Lemmas, runtime_initialize_Init_Internal_Order_Lemmas,
};
use crate::r#gen::Init::Internal::Order::MonadTail::{
    initialize_Init_Internal_Order_MonadTail, runtime_initialize_Init_Internal_Order_MonadTail,
};
use crate::r#gen::Init::Internal::Order::Tactic::{
    initialize_Init_Internal_Order_Tactic, runtime_initialize_Init_Internal_Order_Tactic,
};
use crate::r#gen::Init::Internal::Order::While::{
    initialize_Init_Internal_Order_While, runtime_initialize_Init_Internal_Order_While,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_MonadTail(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Internal_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Internal_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_MonadTail(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Internal_Order(builtin);
}
