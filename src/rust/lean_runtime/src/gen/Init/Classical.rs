// Lean compiler output
// Module: Init.Classical
// Imports: Init.PropLemmas
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_Classical_decidable__of__decidable__not___redArg(mut v_h_16_: u8) -> u8 {
    if v_h_16_ == 0 {
        let mut v___x_17_: u8 = 0;
        v___x_17_ = 1;
        return v___x_17_;
    } else {
        let mut v___x_18_: u8 = 0;
        v___x_18_ = 0;
        return v___x_18_;
    }
}
pub unsafe fn l_Classical_decidable__of__decidable__not___redArg___boxed(
    mut v_h_19_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h_boxed_20_: u8 = 0;
    let mut v_res_21_: u8 = 0;
    let mut v_r_22_: *mut LeanObject = core::ptr::null_mut();
    v_h_boxed_20_ = (lean_unbox(v_h_19_) as u8);
    v_res_21_ = l_Classical_decidable__of__decidable__not___redArg(v_h_boxed_20_);
    v_r_22_ = lean_box((v_res_21_) as usize);
    return v_r_22_;
}
pub unsafe fn l_Classical_decidable__of__decidable__not(
    mut v_p_23_: *mut LeanObject,
    mut v_h_24_: u8,
) -> u8 {
    let mut v___x_25_: u8 = 0;
    v___x_25_ = l_Classical_decidable__of__decidable__not___redArg(v_h_24_);
    return v___x_25_;
}
pub unsafe fn l_Classical_decidable__of__decidable__not___boxed(
    mut v_p_26_: *mut LeanObject,
    mut v_h_27_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h_boxed_28_: u8 = 0;
    let mut v_res_29_: u8 = 0;
    let mut v_r_30_: *mut LeanObject = core::ptr::null_mut();
    v_h_boxed_28_ = (lean_unbox(v_h_27_) as u8);
    v_res_29_ = l_Classical_decidable__of__decidable__not(v_p_26_, v_h_boxed_28_);
    v_r_30_ = lean_box((v_res_29_) as usize);
    return v_r_30_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Classical(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Classical(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Classical(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Classical(builtin);
}
