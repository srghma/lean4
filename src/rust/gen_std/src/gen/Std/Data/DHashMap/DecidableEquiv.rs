// Lean compiler output
// Module: Std.Data.DHashMap.DecidableEquiv
// Imports: Std.Data.DHashMap.Internal.RawLemmas
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_beq___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::RawLemmas::{
    initialize_Std_Data_DHashMap_Internal_RawLemmas,
    runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas,
};
pub unsafe fn l_Std_DHashMap_instDecidableEquivOfLawfulBEq___redArg(
    mut v_inst_35_: *mut leanh::LeanObject,
    mut v_inst_36_: *mut leanh::LeanObject,
    mut v_inst_37_: *mut leanh::LeanObject,
    mut v_m_u2081_38_: *mut leanh::LeanObject,
    mut v_m_u2082_39_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_this_40_: u8 = 0;
    v_this_40_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_35_,
        v_inst_36_,
        v_inst_37_,
        v_m_u2081_38_,
        v_m_u2082_39_,
    );
    return v_this_40_;
}
pub unsafe fn l_Std_DHashMap_instDecidableEquivOfLawfulBEq___redArg___boxed(
    mut v_inst_41_: *mut leanh::LeanObject,
    mut v_inst_42_: *mut leanh::LeanObject,
    mut v_inst_43_: *mut leanh::LeanObject,
    mut v_m_u2081_44_: *mut leanh::LeanObject,
    mut v_m_u2082_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_DHashMap_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_41_,
        v_inst_42_,
        v_inst_43_,
        v_m_u2081_44_,
        v_m_u2082_45_,
    );
    v_r_47_ = leanh::lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Std_DHashMap_instDecidableEquivOfLawfulBEq(
    mut v_00_u03b1_48_: *mut leanh::LeanObject,
    mut v_00_u03b2_49_: *mut leanh::LeanObject,
    mut v_inst_50_: *mut leanh::LeanObject,
    mut v_inst_51_: *mut leanh::LeanObject,
    mut v_inst_52_: *mut leanh::LeanObject,
    mut v_inst_53_: *mut leanh::LeanObject,
    mut v_inst_54_: *mut leanh::LeanObject,
    mut v_m_u2081_55_: *mut leanh::LeanObject,
    mut v_m_u2082_56_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_this_57_: u8 = 0;
    v_this_57_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_50_,
        v_inst_52_,
        v_inst_53_,
        v_m_u2081_55_,
        v_m_u2082_56_,
    );
    return v_this_57_;
}
pub unsafe fn l_Std_DHashMap_instDecidableEquivOfLawfulBEq___boxed(
    mut v_00_u03b1_58_: *mut leanh::LeanObject,
    mut v_00_u03b2_59_: *mut leanh::LeanObject,
    mut v_inst_60_: *mut leanh::LeanObject,
    mut v_inst_61_: *mut leanh::LeanObject,
    mut v_inst_62_: *mut leanh::LeanObject,
    mut v_inst_63_: *mut leanh::LeanObject,
    mut v_inst_64_: *mut leanh::LeanObject,
    mut v_m_u2081_65_: *mut leanh::LeanObject,
    mut v_m_u2082_66_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_67_: u8 = 0;
    let mut v_r_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_67_ = l_Std_DHashMap_instDecidableEquivOfLawfulBEq(
        v_00_u03b1_58_,
        v_00_u03b2_59_,
        v_inst_60_,
        v_inst_61_,
        v_inst_62_,
        v_inst_63_,
        v_inst_64_,
        v_m_u2081_65_,
        v_m_u2082_66_,
    );
    v_r_68_ = leanh::lean_box((v_res_67_) as usize);
    return v_r_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_DecidableEquiv(
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
pub unsafe fn initialize_Std_Data_DHashMap_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
}