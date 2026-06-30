// Lean compiler output
// Module: Std.Data.HashSet.Lemmas
// Imports: Std.Data.HashMap.Lemmas Std.Data.HashSet.Basic
use crate::r#gen::Std::Data::HashMap::Lemmas::{
    initialize_Std_Data_HashMap_Lemmas, runtime_initialize_Std_Data_HashMap_Lemmas,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
pub unsafe fn l_Std_HashSet_Equiv_instTrans(
    mut v_00_u03b1_9_: *mut leanh::LeanObject,
    mut v_x_10_: *mut leanh::LeanObject,
    mut v_x_11_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12_ = leanh::lean_box(0);
    return v___x_12_;
}
pub unsafe fn l_Std_HashSet_Equiv_instTrans___boxed(
    mut v_00_u03b1_13_: *mut leanh::LeanObject,
    mut v_x_14_: *mut leanh::LeanObject,
    mut v_x_15_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_16_ = l_Std_HashSet_Equiv_instTrans(v_00_u03b1_13_, v_x_14_, v_x_15_);
    leanh::lean_dec_ref(v_x_15_);
    leanh::lean_dec_ref(v_x_14_);
    return v_res_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Lemmas(
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
pub unsafe fn initialize_Std_Data_HashSet_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Lemmas(builtin);
}