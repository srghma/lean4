// Lean compiler output
// Module: Std.Data.DHashMap.RawDecidableEquiv
// Imports: Std.Data.DHashMap.Internal.RawLemmas
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_beq___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::RawLemmas::{
    initialize_Std_Data_DHashMap_Internal_RawLemmas,
    runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_DHashMap_Raw_instDecidableEquiv___redArg(
    mut v_inst_39_: *mut LeanObject,
    mut v_inst_40_: *mut LeanObject,
    mut v_inst_41_: *mut LeanObject,
    mut v_m_u2081_42_: *mut LeanObject,
    mut v_m_u2082_43_: *mut LeanObject,
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
    mut v_inst_45_: *mut LeanObject,
    mut v_inst_46_: *mut LeanObject,
    mut v_inst_47_: *mut LeanObject,
    mut v_m_u2081_48_: *mut LeanObject,
    mut v_m_u2082_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_50_: u8 = 0;
    let mut v_r_51_: *mut LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Std_DHashMap_Raw_instDecidableEquiv___redArg(
        v_inst_45_,
        v_inst_46_,
        v_inst_47_,
        v_m_u2081_48_,
        v_m_u2082_49_,
    );
    v_r_51_ = lean_box((v_res_50_) as usize);
    return v_r_51_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_52_: *mut LeanObject,
    mut v_00_u03b2_53_: *mut LeanObject,
    mut v_inst_54_: *mut LeanObject,
    mut v_inst_55_: *mut LeanObject,
    mut v_inst_56_: *mut LeanObject,
    mut v_inst_57_: *mut LeanObject,
    mut v_inst_58_: *mut LeanObject,
    mut v_m_u2081_59_: *mut LeanObject,
    mut v_m_u2082_60_: *mut LeanObject,
    mut v_h_u2081_61_: *mut LeanObject,
    mut v_h_u2082_62_: *mut LeanObject,
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
    mut v_00_u03b1_64_: *mut LeanObject,
    mut v_00_u03b2_65_: *mut LeanObject,
    mut v_inst_66_: *mut LeanObject,
    mut v_inst_67_: *mut LeanObject,
    mut v_inst_68_: *mut LeanObject,
    mut v_inst_69_: *mut LeanObject,
    mut v_inst_70_: *mut LeanObject,
    mut v_m_u2081_71_: *mut LeanObject,
    mut v_m_u2082_72_: *mut LeanObject,
    mut v_h_u2081_73_: *mut LeanObject,
    mut v_h_u2082_74_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_75_: u8 = 0;
    let mut v_r_76_: *mut LeanObject = core::ptr::null_mut();
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
    v_r_76_ = lean_box((v_res_75_) as usize);
    return v_r_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
}
