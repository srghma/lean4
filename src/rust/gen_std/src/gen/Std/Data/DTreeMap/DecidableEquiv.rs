// Lean compiler output
// Module: Std.Data.DTreeMap.DecidableEquiv
// Imports: Std.Data.DTreeMap.Raw
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_beq___redArg;
use crate::r#gen::Std::Data::DTreeMap::Raw::{
    initialize_Std_Data_DTreeMap_Raw, runtime_initialize_Std_Data_DTreeMap_Raw,
};
pub unsafe fn l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
    mut v_cmp_33_: *mut leanh::LeanObject,
    mut v_inst_34_: *mut leanh::LeanObject,
    mut v_t_u2081_35_: *mut leanh::LeanObject,
    mut v_t_u2082_36_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_this_37_: u8 = 0;
    v_this_37_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_33_,
        v_inst_34_,
        v_t_u2081_35_,
        v_t_u2082_36_,
    );
    return v_this_37_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(
    mut v_cmp_38_: *mut leanh::LeanObject,
    mut v_inst_39_: *mut leanh::LeanObject,
    mut v_t_u2081_40_: *mut leanh::LeanObject,
    mut v_t_u2082_41_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_42_: u8 = 0;
    let mut v_r_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
        v_cmp_38_,
        v_inst_39_,
        v_t_u2081_40_,
        v_t_u2082_41_,
    );
    v_r_43_ = leanh::lean_box((v_res_42_) as usize);
    return v_r_43_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(
    mut v_00_u03b1_44_: *mut leanh::LeanObject,
    mut v_00_u03b2_45_: *mut leanh::LeanObject,
    mut v_cmp_46_: *mut leanh::LeanObject,
    mut v_inst_47_: *mut leanh::LeanObject,
    mut v_inst_48_: *mut leanh::LeanObject,
    mut v_inst_49_: *mut leanh::LeanObject,
    mut v_inst_50_: *mut leanh::LeanObject,
    mut v_t_u2081_51_: *mut leanh::LeanObject,
    mut v_t_u2082_52_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_this_53_: u8 = 0;
    v_this_53_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_46_,
        v_inst_49_,
        v_t_u2081_51_,
        v_t_u2082_52_,
    );
    return v_this_53_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(
    mut v_00_u03b1_54_: *mut leanh::LeanObject,
    mut v_00_u03b2_55_: *mut leanh::LeanObject,
    mut v_cmp_56_: *mut leanh::LeanObject,
    mut v_inst_57_: *mut leanh::LeanObject,
    mut v_inst_58_: *mut leanh::LeanObject,
    mut v_inst_59_: *mut leanh::LeanObject,
    mut v_inst_60_: *mut leanh::LeanObject,
    mut v_t_u2081_61_: *mut leanh::LeanObject,
    mut v_t_u2082_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_63_: u8 = 0;
    let mut v_r_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_63_ = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(
        v_00_u03b1_54_,
        v_00_u03b2_55_,
        v_cmp_56_,
        v_inst_57_,
        v_inst_58_,
        v_inst_59_,
        v_inst_60_,
        v_t_u2081_61_,
        v_t_u2082_62_,
    );
    v_r_64_ = leanh::lean_box((v_res_63_) as usize);
    return v_r_64_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_DecidableEquiv(
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
pub unsafe fn initialize_Std_Data_DTreeMap_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
}