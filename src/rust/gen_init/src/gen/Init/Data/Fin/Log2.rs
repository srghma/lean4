// Lean compiler output
// Module: Init.Data.Fin.Log2
// Imports: Init.Prelude Init.Data.Nat.Log2
use crate::ffi::lean_nat_log2;
use crate::r#gen::Init::Data::Nat::Log2::{
    initialize_Init_Data_Nat_Log2, runtime_initialize_Init_Data_Nat_Log2,
};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub unsafe fn l_Fin_log2___redArg(
    mut v_n_11_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12_ = lean_nat_log2(v_n_11_);
    return v___x_12_;
}
pub unsafe fn l_Fin_log2___redArg___boxed(
    mut v_n_13_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_14_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_14_ = l_Fin_log2___redArg(v_n_13_);
    leanh::lean_dec(v_n_13_);
    return v_res_14_;
}
pub unsafe fn l_Fin_log2(
    mut v_m_15_: *mut leanh::LeanObject,
    mut v_n_16_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_17_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_17_ = lean_nat_log2(v_n_16_);
    return v___x_17_;
}
pub unsafe fn l_Fin_log2___boxed(
    mut v_m_18_: *mut leanh::LeanObject,
    mut v_n_19_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_20_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_20_ = l_Fin_log2(v_m_18_, v_n_19_);
    leanh::lean_dec(v_n_19_);
    leanh::lean_dec(v_m_18_);
    return v_res_20_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_Log2(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Log2(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_Log2(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_Log2(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Log2(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Log2(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_Log2(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Fin_Log2(builtin);
}