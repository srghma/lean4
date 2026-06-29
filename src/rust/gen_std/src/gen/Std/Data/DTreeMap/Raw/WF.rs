// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.WF
// Imports: Std.Data.DTreeMap.Raw.AdditionalOperations
use crate::r#gen::Std::Data::DTreeMap::Raw::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
};
pub unsafe fn l_Std_DTreeMap_Raw_WF_instCoeTypeForall(
    mut v_00_u03b1_3_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4_ = crate::leanh::lean_box(0);
    return v___x_4_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Raw_WF(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Raw_WF(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Raw_WF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Raw_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Raw_WF(builtin);
}
