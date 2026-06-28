// Lean compiler output
// Module: Std.Data.TreeMap.Raw.AdditionalOperations
// Imports: Std.Data.TreeMap.Basic Std.Data.TreeMap.Raw.Basic Std.Data.DTreeMap.Raw.AdditionalOperations
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg, l_Std_DTreeMap_Internal_Impl_map___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
};
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
use crate::r#gen::Std::Data::TreeMap::Raw::Basic::{
    initialize_Std_Data_TreeMap_Raw_Basic, runtime_initialize_Std_Data_TreeMap_Raw_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_TreeMap_Raw_filterMap___redArg(
    mut v_f_35_: *mut LeanObject,
    mut v_t_36_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    v___x_37_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_35_, v_t_36_);
    return v___x_37_;
}
pub unsafe fn l_Std_TreeMap_Raw_filterMap(
    mut v_00_u03b1_38_: *mut LeanObject,
    mut v_00_u03b2_39_: *mut LeanObject,
    mut v_00_u03b3_40_: *mut LeanObject,
    mut v_cmp_41_: *mut LeanObject,
    mut v_f_42_: *mut LeanObject,
    mut v_t_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v___x_44_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_42_, v_t_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_TreeMap_Raw_filterMap___boxed(
    mut v_00_u03b1_45_: *mut LeanObject,
    mut v_00_u03b2_46_: *mut LeanObject,
    mut v_00_u03b3_47_: *mut LeanObject,
    mut v_cmp_48_: *mut LeanObject,
    mut v_f_49_: *mut LeanObject,
    mut v_t_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_51_: *mut LeanObject = core::ptr::null_mut();
    v_res_51_ = l_Std_TreeMap_Raw_filterMap(
        v_00_u03b1_45_,
        v_00_u03b2_46_,
        v_00_u03b3_47_,
        v_cmp_48_,
        v_f_49_,
        v_t_50_,
    );
    lean_dec_ref(v_cmp_48_);
    return v_res_51_;
}
pub unsafe fn l_Std_TreeMap_Raw_map___redArg(
    mut v_f_52_: *mut LeanObject,
    mut v_t_53_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    v___x_54_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_52_, v_t_53_);
    return v___x_54_;
}
pub unsafe fn l_Std_TreeMap_Raw_map(
    mut v_00_u03b1_55_: *mut LeanObject,
    mut v_00_u03b2_56_: *mut LeanObject,
    mut v_00_u03b3_57_: *mut LeanObject,
    mut v_cmp_58_: *mut LeanObject,
    mut v_f_59_: *mut LeanObject,
    mut v_t_60_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    v___x_61_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_59_, v_t_60_);
    return v___x_61_;
}
pub unsafe fn l_Std_TreeMap_Raw_map___boxed(
    mut v_00_u03b1_62_: *mut LeanObject,
    mut v_00_u03b2_63_: *mut LeanObject,
    mut v_00_u03b3_64_: *mut LeanObject,
    mut v_cmp_65_: *mut LeanObject,
    mut v_f_66_: *mut LeanObject,
    mut v_t_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_68_: *mut LeanObject = core::ptr::null_mut();
    v_res_68_ = l_Std_TreeMap_Raw_map(
        v_00_u03b1_62_,
        v_00_u03b2_63_,
        v_00_u03b3_64_,
        v_cmp_65_,
        v_f_66_,
        v_t_67_,
    );
    lean_dec_ref(v_cmp_65_);
    return v_res_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin);
}
