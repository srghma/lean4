// Lean compiler output
// Module: Init.Data.Char.Lemmas
// Imports: Init.Data.Char.Basic Init.Data.Char.Basic Init.Ext Init.Data.UInt.Lemmas
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
pub static mut l_Char_leTrans: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_ltTrans: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_notLTTrans: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Char_leTrans() -> *mut crate::leanh::LeanObject {
    let mut v___x_4_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4_ = crate::leanh::lean_box(0);
    return v___x_4_;
}
pub unsafe fn _init_l_Char_ltTrans() -> *mut crate::leanh::LeanObject {
    let mut v___x_5_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5_ = crate::leanh::lean_box(0);
    return v___x_5_;
}
pub unsafe fn _init_l_Char_notLTTrans() -> *mut crate::leanh::LeanObject {
    let mut v___x_6_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6_ = crate::leanh::lean_box(0);
    return v___x_6_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Char_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Char_leTrans = _init_l_Char_leTrans();
    l_Char_ltTrans = _init_l_Char_ltTrans();
    l_Char_notLTTrans = _init_l_Char_notLTTrans();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Char_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Char_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Char_Lemmas(builtin);
}
