// Lean compiler output
// Module: Init.Data.Fin.OverflowAware
// Imports: Init.Data.Fin.Basic Init.Data.Fin.Lemmas
use crate::ffi::{lean_nat_add, lean_nat_dec_lt};
use crate::r#gen::Init::Data::Fin::Basic::{
    initialize_Init_Data_Fin_Basic, runtime_initialize_Init_Data_Fin_Basic,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
pub unsafe fn l_Fin_addNat_x3f(
    mut v_n_12_: *mut leanh::LeanObject,
    mut v_i_13_: *mut leanh::LeanObject,
    mut v_m_14_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_15_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_16_: u8 = 0;
    v___x_15_ = lean_nat_add(v_i_13_, v_m_14_);
    v___x_16_ = lean_nat_dec_lt(v___x_15_, v_n_12_);
    if v___x_16_ == 0 {
        let mut v___x_17_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_15_);
        v___x_17_ = leanh::lean_box(0);
        return v___x_17_;
    } else {
        let mut v___x_18_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_18_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_18_, 0, v___x_15_);
        return v___x_18_;
    }
}
pub unsafe fn l_Fin_addNat_x3f___boxed(
    mut v_n_19_: *mut leanh::LeanObject,
    mut v_i_20_: *mut leanh::LeanObject,
    mut v_m_21_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_22_ = l_Fin_addNat_x3f(v_n_19_, v_i_20_, v_m_21_);
    leanh::lean_dec(v_m_21_);
    leanh::lean_dec(v_i_20_);
    leanh::lean_dec(v_n_19_);
    return v_res_22_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_OverflowAware(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Fin_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_OverflowAware(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_OverflowAware(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Fin_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_OverflowAware(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Fin_OverflowAware(builtin);
}