// Lean compiler output
// Module: Init.Data.Iterators.Producers.List
// Imports: Init.Data.Iterators.Producers.Monadic.List
use crate::r#gen::Init::Data::Iterators::Producers::Monadic::List::{
    initialize_Init_Data_Iterators_Producers_Monadic_List,
    runtime_initialize_Init_Data_Iterators_Producers_Monadic_List,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_List_iter___redArg(mut v_l_9_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_l_9_);
    return v_l_9_;
}
pub unsafe fn l_List_iter___redArg___boxed(mut v_l_10_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_11_: *mut LeanObject = core::ptr::null_mut();
    v_res_11_ = l_List_iter___redArg(v_l_10_);
    lean_dec(v_l_10_);
    return v_res_11_;
}
pub unsafe fn l_List_iter(
    mut v_00_u03b1_12_: *mut LeanObject,
    mut v_l_13_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_l_13_);
    return v_l_13_;
}
pub unsafe fn l_List_iter___boxed(
    mut v_00_u03b1_14_: *mut LeanObject,
    mut v_l_15_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_16_: *mut LeanObject = core::ptr::null_mut();
    v_res_16_ = l_List_iter(v_00_u03b1_14_, v_l_15_);
    lean_dec(v_l_15_);
    return v_res_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Producers_List(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Producers_List(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Producers_List(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Producers_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Producers_List(builtin);
}
