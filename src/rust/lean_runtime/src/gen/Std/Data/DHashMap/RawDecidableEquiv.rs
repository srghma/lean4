// Lean compiler output
// Module: Std.Data.DHashMap.RawDecidableEquiv
// Imports: Std.Data.DHashMap.Internal.RawLemmas
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_beq___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::RawLemmas::{
    initialize_Std_Data_DHashMap_Internal_RawLemmas,
    runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas,
};
pub unsafe fn l_Std_DHashMap_Raw_instDecidableEquiv___redArg(
    mut v_inst_39_: *mut crate::leanh::LeanObject,
    mut v_inst_40_: *mut crate::leanh::LeanObject,
    mut v_inst_41_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_42_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_43_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_44_: u8 = 0;
    v___x_44_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_39_,
        v_inst_40_,
        v_inst_41_,
        v_m_u2081_42_,
        v_m_u2082_43_,
    );
    return v___x_44_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableEquiv___redArg___boxed(
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_inst_46_: *mut crate::leanh::LeanObject,
    mut v_inst_47_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_48_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_50_: u8 = 0;
    let mut v_r_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Std_DHashMap_Raw_instDecidableEquiv___redArg(
        v_inst_45_,
        v_inst_46_,
        v_inst_47_,
        v_m_u2081_48_,
        v_m_u2082_49_,
    );
    v_r_51_ = crate::leanh::lean_box((v_res_50_) as usize);
    return v_r_51_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_52_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_53_: *mut crate::leanh::LeanObject,
    mut v_inst_54_: *mut crate::leanh::LeanObject,
    mut v_inst_55_: *mut crate::leanh::LeanObject,
    mut v_inst_56_: *mut crate::leanh::LeanObject,
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_inst_58_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_59_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_60_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_61_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_62_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_63_: u8 = 0;
    v___x_63_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_54_,
        v_inst_56_,
        v_inst_57_,
        v_m_u2081_59_,
        v_m_u2082_60_,
    );
    return v___x_63_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableEquiv___boxed(
    mut v_00_u03b1_64_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_65_: *mut crate::leanh::LeanObject,
    mut v_inst_66_: *mut crate::leanh::LeanObject,
    mut v_inst_67_: *mut crate::leanh::LeanObject,
    mut v_inst_68_: *mut crate::leanh::LeanObject,
    mut v_inst_69_: *mut crate::leanh::LeanObject,
    mut v_inst_70_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_71_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_72_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_73_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_75_: u8 = 0;
    let mut v_r_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_75_ = l_Std_DHashMap_Raw_instDecidableEquiv(
        v_00_u03b1_64_,
        v_00_u03b2_65_,
        v_inst_66_,
        v_inst_67_,
        v_inst_68_,
        v_inst_69_,
        v_inst_70_,
        v_m_u2081_71_,
        v_m_u2082_72_,
        v_h_u2081_73_,
        v_h_u2082_74_,
    );
    v_r_76_ = crate::leanh::lean_box((v_res_75_) as usize);
    return v_r_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_RawDecidableEquiv(
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
pub unsafe fn initialize_Std_Data_DHashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
}
