// Lean compiler output
// Module: Init.Data.UInt.Log2
// Imports: Init.Prelude Init.Data.Fin.Log2 Init.Data.UInt.BasicAux
use crate::r#gen::Init::Data::Fin::Log2::{
    initialize_Init_Data_Fin_Log2, runtime_initialize_Init_Data_Fin_Log2,
};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    initialize_Init_Data_UInt_BasicAux, runtime_initialize_Init_Data_UInt_BasicAux,
};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::ffi::{
    lean_uint8_log2, lean_uint16_log2, lean_uint32_log2, lean_uint64_log2, lean_usize_log2,
};
pub unsafe fn l_UInt8_log2___boxed(
    mut v_a_27_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_28_: u8 = 0;
    let mut v_res_29_: u8 = 0;
    let mut v_r_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_28_ = (crate::leanh::lean_unbox(v_a_27_) as u8);
    v_res_29_ = lean_uint8_log2(v_a_boxed_28_);
    v_r_30_ = crate::leanh::lean_box((v_res_29_) as usize);
    return v_r_30_;
}
pub unsafe fn l_UInt16_log2___boxed(
    mut v_a_32_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_33_: u16 = 0;
    let mut v_res_34_: u16 = 0;
    let mut v_r_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_33_ = (crate::leanh::lean_unbox(v_a_32_) as u16);
    v_res_34_ = lean_uint16_log2(v_a_boxed_33_);
    v_r_35_ = crate::leanh::lean_box((v_res_34_) as usize);
    return v_r_35_;
}
pub unsafe fn l_UInt32_log2___boxed(
    mut v_a_37_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_38_: u32 = 0;
    let mut v_res_39_: u32 = 0;
    let mut v_r_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_38_ = crate::leanh::lean_unbox_uint32(v_a_37_);
    crate::leanh::lean_dec(v_a_37_);
    v_res_39_ = lean_uint32_log2(v_a_boxed_38_);
    v_r_40_ = crate::leanh::lean_box_uint32(v_res_39_);
    return v_r_40_;
}
pub unsafe fn l_UInt64_log2___boxed(
    mut v_a_42_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_43_: u64 = 0;
    let mut v_res_44_: u64 = 0;
    let mut v_r_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_43_ = crate::leanh::lean_unbox_uint64(v_a_42_);
    crate::leanh::lean_dec_ref(v_a_42_);
    v_res_44_ = lean_uint64_log2(v_a_boxed_43_);
    v_r_45_ = crate::leanh::lean_box_uint64(v_res_44_);
    return v_r_45_;
}
pub unsafe fn l_USize_log2___boxed(
    mut v_a_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_48_: usize = 0;
    let mut v_res_49_: usize = 0;
    let mut v_r_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_48_ = crate::leanh::lean_unbox_usize(v_a_47_);
    crate::leanh::lean_dec(v_a_47_);
    v_res_49_ = lean_usize_log2(v_a_boxed_48_);
    v_r_50_ = crate::leanh::lean_box_usize(v_res_49_);
    return v_r_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_UInt_Log2(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_UInt_Log2(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_UInt_Log2(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_UInt_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_UInt_Log2(builtin);
}
