// Lean compiler output
// Module: Std.Data.DHashMap.DecidableEquiv
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
pub unsafe fn l_Std_DHashMap_instDecidableEquivOfLawfulBEq___redArg(
    mut v_inst_35_: *mut LeanObject,
    mut v_inst_36_: *mut LeanObject,
    mut v_inst_37_: *mut LeanObject,
    mut v_m_u2081_38_: *mut LeanObject,
    mut v_m_u2082_39_: *mut LeanObject,
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
    mut v_inst_41_: *mut LeanObject,
    mut v_inst_42_: *mut LeanObject,
    mut v_inst_43_: *mut LeanObject,
    mut v_m_u2081_44_: *mut LeanObject,
    mut v_m_u2082_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_DHashMap_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_41_,
        v_inst_42_,
        v_inst_43_,
        v_m_u2081_44_,
        v_m_u2082_45_,
    );
    v_r_47_ = lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Std_DHashMap_instDecidableEquivOfLawfulBEq(
    mut v_00_u03b1_48_: *mut LeanObject,
    mut v_00_u03b2_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
    mut v_inst_52_: *mut LeanObject,
    mut v_inst_53_: *mut LeanObject,
    mut v_inst_54_: *mut LeanObject,
    mut v_m_u2081_55_: *mut LeanObject,
    mut v_m_u2082_56_: *mut LeanObject,
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
    mut v_00_u03b1_58_: *mut LeanObject,
    mut v_00_u03b2_59_: *mut LeanObject,
    mut v_inst_60_: *mut LeanObject,
    mut v_inst_61_: *mut LeanObject,
    mut v_inst_62_: *mut LeanObject,
    mut v_inst_63_: *mut LeanObject,
    mut v_inst_64_: *mut LeanObject,
    mut v_m_u2081_65_: *mut LeanObject,
    mut v_m_u2082_66_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_67_: u8 = 0;
    let mut v_r_68_: *mut LeanObject = core::ptr::null_mut();
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
    v_r_68_ = lean_box((v_res_67_) as usize);
    return v_r_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Std_Data_DHashMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
}
