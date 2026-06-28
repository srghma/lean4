// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Total
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_IterM_ensureTermination___redArg(
    mut v_it_13_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_13_);
    return v_it_13_;
}
pub unsafe fn l_Std_IterM_ensureTermination___redArg___boxed(
    mut v_it_14_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_15_: *mut LeanObject = core::ptr::null_mut();
    v_res_15_ = l_Std_IterM_ensureTermination___redArg(v_it_14_);
    lean_dec(v_it_14_);
    return v_res_15_;
}
pub unsafe fn l_Std_IterM_ensureTermination(
    mut v_00_u03b1_16_: *mut LeanObject,
    mut v_00_u03b2_17_: *mut LeanObject,
    mut v_m_18_: *mut LeanObject,
    mut v_it_19_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_19_);
    return v_it_19_;
}
pub unsafe fn l_Std_IterM_ensureTermination___boxed(
    mut v_00_u03b1_20_: *mut LeanObject,
    mut v_00_u03b2_21_: *mut LeanObject,
    mut v_m_22_: *mut LeanObject,
    mut v_it_23_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_24_: *mut LeanObject = core::ptr::null_mut();
    v_res_24_ = l_Std_IterM_ensureTermination(v_00_u03b1_20_, v_00_u03b2_21_, v_m_22_, v_it_23_);
    lean_dec(v_it_23_);
    return v_res_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Total(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Total(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
}
