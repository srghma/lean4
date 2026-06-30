// Lean compiler output
// Module: Std.Data.HashMap.AdditionalOperations
// Imports: Std.Data.DHashMap.AdditionalOperations Std.Data.HashMap.Basic Std.Data.HashMap.Raw
use crate::r#gen::Std::Data::DHashMap::AdditionalOperations::{
    initialize_Std_Data_DHashMap_AdditionalOperations,
    runtime_initialize_Std_Data_DHashMap_AdditionalOperations,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_map___redArg,
};
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
pub unsafe fn l_Std_HashMap_filterMap___redArg(
    mut v_f_39_: *mut leanh::LeanObject,
    mut v_m_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_39_, v_m_40_);
    return v___x_41_;
}
pub unsafe fn l_Std_HashMap_filterMap(
    mut v_00_u03b1_42_: *mut leanh::LeanObject,
    mut v_00_u03b2_43_: *mut leanh::LeanObject,
    mut v_00_u03b3_44_: *mut leanh::LeanObject,
    mut v_inst_45_: *mut leanh::LeanObject,
    mut v_inst_46_: *mut leanh::LeanObject,
    mut v_f_47_: *mut leanh::LeanObject,
    mut v_m_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_49_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_49_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_47_, v_m_48_);
    return v___x_49_;
}
pub unsafe fn l_Std_HashMap_filterMap___boxed(
    mut v_00_u03b1_50_: *mut leanh::LeanObject,
    mut v_00_u03b2_51_: *mut leanh::LeanObject,
    mut v_00_u03b3_52_: *mut leanh::LeanObject,
    mut v_inst_53_: *mut leanh::LeanObject,
    mut v_inst_54_: *mut leanh::LeanObject,
    mut v_f_55_: *mut leanh::LeanObject,
    mut v_m_56_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Std_HashMap_filterMap(
        v_00_u03b1_50_,
        v_00_u03b2_51_,
        v_00_u03b3_52_,
        v_inst_53_,
        v_inst_54_,
        v_f_55_,
        v_m_56_,
    );
    leanh::lean_dec_ref(v_inst_54_);
    leanh::lean_dec_ref(v_inst_53_);
    return v_res_57_;
}
pub unsafe fn l_Std_HashMap_map___redArg(
    mut v_f_58_: *mut leanh::LeanObject,
    mut v_m_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_60_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_58_, v_m_59_);
    return v___x_60_;
}
pub unsafe fn l_Std_HashMap_map(
    mut v_00_u03b1_61_: *mut leanh::LeanObject,
    mut v_00_u03b2_62_: *mut leanh::LeanObject,
    mut v_00_u03b3_63_: *mut leanh::LeanObject,
    mut v_inst_64_: *mut leanh::LeanObject,
    mut v_inst_65_: *mut leanh::LeanObject,
    mut v_f_66_: *mut leanh::LeanObject,
    mut v_m_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_66_, v_m_67_);
    return v___x_68_;
}
pub unsafe fn l_Std_HashMap_map___boxed(
    mut v_00_u03b1_69_: *mut leanh::LeanObject,
    mut v_00_u03b2_70_: *mut leanh::LeanObject,
    mut v_00_u03b3_71_: *mut leanh::LeanObject,
    mut v_inst_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
    mut v_f_74_: *mut leanh::LeanObject,
    mut v_m_75_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_HashMap_map(
        v_00_u03b1_69_,
        v_00_u03b2_70_,
        v_00_u03b3_71_,
        v_inst_72_,
        v_inst_73_,
        v_f_74_,
        v_m_75_,
    );
    leanh::lean_dec_ref(v_inst_73_);
    leanh::lean_dec_ref(v_inst_72_);
    return v_res_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_AdditionalOperations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_AdditionalOperations(
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
pub unsafe fn initialize_Std_Data_HashMap_AdditionalOperations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_AdditionalOperations(builtin);
}