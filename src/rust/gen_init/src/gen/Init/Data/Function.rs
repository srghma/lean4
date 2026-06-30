// Lean compiler output
// Module: Init.Data.Function
// Imports: Init.Grind.Tactics
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
pub unsafe fn l_Function_curry___redArg(
    mut v_f_27_: *mut leanh::LeanObject,
    mut v_a_28_: *mut leanh::LeanObject,
    mut v_b_29_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_30_, 0, v_a_28_);
    leanh::lean_ctor_set(v___x_30_, 1, v_b_29_);
    v___x_31_ = leanh::lean_apply_1(v_f_27_, v___x_30_);
    return v___x_31_;
}
pub unsafe fn l_Function_curry(
    mut v_00_u03b1_32_: *mut leanh::LeanObject,
    mut v_00_u03b2_33_: *mut leanh::LeanObject,
    mut v_00_u03c6_34_: *mut leanh::LeanObject,
    mut v_f_35_: *mut leanh::LeanObject,
    mut v_a_36_: *mut leanh::LeanObject,
    mut v_b_37_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_38_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_38_, 0, v_a_36_);
    leanh::lean_ctor_set(v___x_38_, 1, v_b_37_);
    v___x_39_ = leanh::lean_apply_1(v_f_35_, v___x_38_);
    return v___x_39_;
}
pub unsafe fn l_Function_uncurry___redArg(
    mut v_f_40_: *mut leanh::LeanObject,
    mut v_a_41_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_42_ = leanh::lean_ctor_get(v_a_41_, 0);
    leanh::lean_inc(v_fst_42_);
    v_snd_43_ = leanh::lean_ctor_get(v_a_41_, 1);
    leanh::lean_inc(v_snd_43_);
    leanh::lean_dec_ref(v_a_41_);
    v___x_44_ = leanh::lean_apply_2(v_f_40_, v_fst_42_, v_snd_43_);
    return v___x_44_;
}
pub unsafe fn l_Function_uncurry(
    mut v_00_u03b1_45_: *mut leanh::LeanObject,
    mut v_00_u03b2_46_: *mut leanh::LeanObject,
    mut v_00_u03c6_47_: *mut leanh::LeanObject,
    mut v_f_48_: *mut leanh::LeanObject,
    mut v_a_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_50_ = leanh::lean_ctor_get(v_a_49_, 0);
    leanh::lean_inc(v_fst_50_);
    v_snd_51_ = leanh::lean_ctor_get(v_a_49_, 1);
    leanh::lean_inc(v_snd_51_);
    leanh::lean_dec_ref(v_a_49_);
    v___x_52_ = leanh::lean_apply_2(v_f_48_, v_fst_50_, v_snd_51_);
    return v___x_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Function(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Function(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Function(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Function(builtin);
}