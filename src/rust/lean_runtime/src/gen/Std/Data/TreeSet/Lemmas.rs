// Lean compiler output
// Module: Std.Data.TreeSet.Lemmas
// Imports: Std.Data.TreeMap.Lemmas Std.Data.DTreeMap.Lemmas Init.Data.Array.Perm Std.Data.TreeSet.AdditionalOperations
use crate::r#gen::Init::Data::Array::Perm::{
    initialize_Init_Data_Array_Perm, runtime_initialize_Init_Data_Array_Perm,
};
use crate::r#gen::Std::Data::DTreeMap::Lemmas::{
    initialize_Std_Data_DTreeMap_Lemmas, runtime_initialize_Std_Data_DTreeMap_Lemmas,
};
use crate::r#gen::Std::Data::TreeMap::Lemmas::{
    initialize_Std_Data_TreeMap_Lemmas, runtime_initialize_Std_Data_TreeMap_Lemmas,
};
use crate::r#gen::Std::Data::TreeSet::AdditionalOperations::{
    initialize_Std_Data_TreeSet_AdditionalOperations,
    runtime_initialize_Std_Data_TreeSet_AdditionalOperations,
};
pub unsafe fn l_Std_TreeSet_Equiv_instTrans(
    mut v_00_u03b1_7_: *mut crate::leanh::LeanObject,
    mut v_cmp_8_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9_ = crate::leanh::lean_box(0);
    return v___x_9_;
}
pub unsafe fn l_Std_TreeSet_Equiv_instTrans___boxed(
    mut v_00_u03b1_10_: *mut crate::leanh::LeanObject,
    mut v_cmp_11_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_12_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_12_ = l_Std_TreeSet_Equiv_instTrans(v_00_u03b1_10_, v_cmp_11_);
    crate::leanh::lean_dec_ref(v_cmp_11_);
    return v_res_12_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Lemmas(builtin);
}
