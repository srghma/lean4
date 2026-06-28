// Lean compiler output
// Module: Init.Data.Function
// Imports: Init.Grind.Tactics
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Function_curry___redArg(
    mut v_f_27_: *mut LeanObject,
    mut v_a_28_: *mut LeanObject,
    mut v_b_29_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    v___x_30_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_30_, 0, v_a_28_);
    lean_ctor_set(v___x_30_, 1, v_b_29_);
    v___x_31_ = lean_apply_1(v_f_27_, v___x_30_);
    return v___x_31_;
}
pub unsafe fn l_Function_curry(
    mut v_00_u03b1_32_: *mut LeanObject,
    mut v_00_u03b2_33_: *mut LeanObject,
    mut v_00_u03c6_34_: *mut LeanObject,
    mut v_f_35_: *mut LeanObject,
    mut v_a_36_: *mut LeanObject,
    mut v_b_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    v___x_38_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_38_, 0, v_a_36_);
    lean_ctor_set(v___x_38_, 1, v_b_37_);
    v___x_39_ = lean_apply_1(v_f_35_, v___x_38_);
    return v___x_39_;
}
pub unsafe fn l_Function_uncurry___redArg(
    mut v_f_40_: *mut LeanObject,
    mut v_a_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v_fst_42_ = lean_ctor_get(v_a_41_, 0);
    lean_inc(v_fst_42_);
    v_snd_43_ = lean_ctor_get(v_a_41_, 1);
    lean_inc(v_snd_43_);
    lean_dec_ref(v_a_41_);
    v___x_44_ = lean_apply_2(v_f_40_, v_fst_42_, v_snd_43_);
    return v___x_44_;
}
pub unsafe fn l_Function_uncurry(
    mut v_00_u03b1_45_: *mut LeanObject,
    mut v_00_u03b2_46_: *mut LeanObject,
    mut v_00_u03c6_47_: *mut LeanObject,
    mut v_f_48_: *mut LeanObject,
    mut v_a_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_50_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    v_fst_50_ = lean_ctor_get(v_a_49_, 0);
    lean_inc(v_fst_50_);
    v_snd_51_ = lean_ctor_get(v_a_49_, 1);
    lean_inc(v_snd_51_);
    lean_dec_ref(v_a_49_);
    v___x_52_ = lean_apply_2(v_f_48_, v_fst_50_, v_snd_51_);
    return v___x_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Function(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Function(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Function(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Function(builtin);
}
