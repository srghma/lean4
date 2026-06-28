// Lean compiler output
// Module: Init.Data.Function
// Imports: Init.Grind.Tactics
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
pub unsafe fn l_Function_curry___redArg(
    mut v_f_27_: *mut crate::leanh::LeanObject,
    mut v_a_28_: *mut crate::leanh::LeanObject,
    mut v_b_29_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_30_, 0, v_a_28_);
    crate::leanh::lean_ctor_set(v___x_30_, 1, v_b_29_);
    v___x_31_ = crate::leanh::lean_apply_1(v_f_27_, v___x_30_);
    return v___x_31_;
}
pub unsafe fn l_Function_curry(
    mut v_00_u03b1_32_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_33_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_34_: *mut crate::leanh::LeanObject,
    mut v_f_35_: *mut crate::leanh::LeanObject,
    mut v_a_36_: *mut crate::leanh::LeanObject,
    mut v_b_37_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_38_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_38_, 0, v_a_36_);
    crate::leanh::lean_ctor_set(v___x_38_, 1, v_b_37_);
    v___x_39_ = crate::leanh::lean_apply_1(v_f_35_, v___x_38_);
    return v___x_39_;
}
pub unsafe fn l_Function_uncurry___redArg(
    mut v_f_40_: *mut crate::leanh::LeanObject,
    mut v_a_41_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_42_ = crate::leanh::lean_ctor_get(v_a_41_, 0);
    crate::leanh::lean_inc(v_fst_42_);
    v_snd_43_ = crate::leanh::lean_ctor_get(v_a_41_, 1);
    crate::leanh::lean_inc(v_snd_43_);
    crate::leanh::lean_dec_ref(v_a_41_);
    v___x_44_ = crate::leanh::lean_apply_2(v_f_40_, v_fst_42_, v_snd_43_);
    return v___x_44_;
}
pub unsafe fn l_Function_uncurry(
    mut v_00_u03b1_45_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_46_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_47_: *mut crate::leanh::LeanObject,
    mut v_f_48_: *mut crate::leanh::LeanObject,
    mut v_a_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_50_ = crate::leanh::lean_ctor_get(v_a_49_, 0);
    crate::leanh::lean_inc(v_fst_50_);
    v_snd_51_ = crate::leanh::lean_ctor_get(v_a_49_, 1);
    crate::leanh::lean_inc(v_snd_51_);
    crate::leanh::lean_dec_ref(v_a_49_);
    v___x_52_ = crate::leanh::lean_apply_2(v_f_48_, v_fst_50_, v_snd_51_);
    return v___x_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Function(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Function(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Function(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Function(builtin);
}
