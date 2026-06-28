// Lean compiler output
// Module: Std.Data.DTreeMap.DecidableEquiv
// Imports: Std.Data.DTreeMap.Raw
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_beq___redArg;
use crate::r#gen::Std::Data::DTreeMap::Raw::{
    initialize_Std_Data_DTreeMap_Raw, runtime_initialize_Std_Data_DTreeMap_Raw,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
    mut v_cmp_33_: *mut LeanObject,
    mut v_inst_34_: *mut LeanObject,
    mut v_t_u2081_35_: *mut LeanObject,
    mut v_t_u2082_36_: *mut LeanObject,
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
    mut v_cmp_38_: *mut LeanObject,
    mut v_inst_39_: *mut LeanObject,
    mut v_t_u2081_40_: *mut LeanObject,
    mut v_t_u2082_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_42_: u8 = 0;
    let mut v_r_43_: *mut LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
        v_cmp_38_,
        v_inst_39_,
        v_t_u2081_40_,
        v_t_u2082_41_,
    );
    v_r_43_ = lean_box((v_res_42_) as usize);
    return v_r_43_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(
    mut v_00_u03b1_44_: *mut LeanObject,
    mut v_00_u03b2_45_: *mut LeanObject,
    mut v_cmp_46_: *mut LeanObject,
    mut v_inst_47_: *mut LeanObject,
    mut v_inst_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_t_u2081_51_: *mut LeanObject,
    mut v_t_u2082_52_: *mut LeanObject,
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
    mut v_00_u03b1_54_: *mut LeanObject,
    mut v_00_u03b2_55_: *mut LeanObject,
    mut v_cmp_56_: *mut LeanObject,
    mut v_inst_57_: *mut LeanObject,
    mut v_inst_58_: *mut LeanObject,
    mut v_inst_59_: *mut LeanObject,
    mut v_inst_60_: *mut LeanObject,
    mut v_t_u2081_61_: *mut LeanObject,
    mut v_t_u2082_62_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_63_: u8 = 0;
    let mut v_r_64_: *mut LeanObject = core::ptr::null_mut();
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
    v_r_64_ = lean_box((v_res_63_) as usize);
    return v_r_64_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
}
