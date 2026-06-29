// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.DecidableEquiv
// Imports: Std.Data.DTreeMap.Internal.Lemmas Std.Data.DTreeMap.Raw.Basic
use crate::r#gen::Std::Data::DTreeMap::Internal::Lemmas::{
    initialize_Std_Data_DTreeMap_Internal_Lemmas,
    runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_beq___redArg;
use crate::r#gen::Std::Data::DTreeMap::Raw::Basic::{
    initialize_Std_Data_DTreeMap_Raw_Basic, runtime_initialize_Std_Data_DTreeMap_Raw_Basic,
};
pub unsafe fn l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(
    mut v_cmp_37_: *mut crate::leanh::LeanObject,
    mut v_inst_38_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_39_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_40_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_this_41_: u8 = 0;
    v_this_41_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_37_,
        v_inst_38_,
        v_t_u2081_39_,
        v_t_u2082_40_,
    );
    return v_this_41_;
}
pub unsafe fn l_Std_DTreeMap_Raw_instDecidableEquiv___redArg___boxed(
    mut v_cmp_42_: *mut crate::leanh::LeanObject,
    mut v_inst_43_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_44_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(
        v_cmp_42_,
        v_inst_43_,
        v_t_u2081_44_,
        v_t_u2082_45_,
    );
    v_r_47_ = crate::leanh::lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Std_DTreeMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_48_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_49_: *mut crate::leanh::LeanObject,
    mut v_cmp_50_: *mut crate::leanh::LeanObject,
    mut v_inst_51_: *mut crate::leanh::LeanObject,
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_inst_53_: *mut crate::leanh::LeanObject,
    mut v_inst_54_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_55_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_56_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_57_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_58_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_this_59_: u8 = 0;
    v_this_59_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_50_,
        v_inst_53_,
        v_t_u2081_55_,
        v_t_u2082_56_,
    );
    return v_this_59_;
}
pub unsafe fn l_Std_DTreeMap_Raw_instDecidableEquiv___boxed(
    mut v_00_u03b1_60_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_61_: *mut crate::leanh::LeanObject,
    mut v_cmp_62_: *mut crate::leanh::LeanObject,
    mut v_inst_63_: *mut crate::leanh::LeanObject,
    mut v_inst_64_: *mut crate::leanh::LeanObject,
    mut v_inst_65_: *mut crate::leanh::LeanObject,
    mut v_inst_66_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_67_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_68_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_69_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_70_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_71_: u8 = 0;
    let mut v_r_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_71_ = l_Std_DTreeMap_Raw_instDecidableEquiv(
        v_00_u03b1_60_,
        v_00_u03b2_61_,
        v_cmp_62_,
        v_inst_63_,
        v_inst_64_,
        v_inst_65_,
        v_inst_66_,
        v_t_u2081_67_,
        v_t_u2082_68_,
        v_h_u2081_69_,
        v_h_u2082_70_,
    );
    v_r_72_ = crate::leanh::lean_box((v_res_71_) as usize);
    return v_r_72_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
}
