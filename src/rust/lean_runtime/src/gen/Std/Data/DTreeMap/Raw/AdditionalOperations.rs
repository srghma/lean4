// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.AdditionalOperations
// Imports: Std.Data.DTreeMap.AdditionalOperations
use crate::r#gen::Std::Data::DTreeMap::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_AdditionalOperations,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg, l_Std_DTreeMap_Internal_Impl_map___redArg,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_DTreeMap_Raw_instCoeTypeForall(
    mut v_00_u03b1_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    v___x_38_ = lean_box(0);
    return v___x_38_;
}
pub unsafe fn l_Std_DTreeMap_Raw_filterMap___redArg(
    mut v_f_39_: *mut LeanObject,
    mut v_t_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    v___x_41_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_39_, v_t_40_);
    return v___x_41_;
}
pub unsafe fn l_Std_DTreeMap_Raw_filterMap(
    mut v_00_u03b1_42_: *mut LeanObject,
    mut v_00_u03b2_43_: *mut LeanObject,
    mut v_00_u03b3_44_: *mut LeanObject,
    mut v_cmp_45_: *mut LeanObject,
    mut v_f_46_: *mut LeanObject,
    mut v_t_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    v___x_48_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_46_, v_t_47_);
    return v___x_48_;
}
pub unsafe fn l_Std_DTreeMap_Raw_filterMap___boxed(
    mut v_00_u03b1_49_: *mut LeanObject,
    mut v_00_u03b2_50_: *mut LeanObject,
    mut v_00_u03b3_51_: *mut LeanObject,
    mut v_cmp_52_: *mut LeanObject,
    mut v_f_53_: *mut LeanObject,
    mut v_t_54_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_55_: *mut LeanObject = core::ptr::null_mut();
    v_res_55_ = l_Std_DTreeMap_Raw_filterMap(
        v_00_u03b1_49_,
        v_00_u03b2_50_,
        v_00_u03b3_51_,
        v_cmp_52_,
        v_f_53_,
        v_t_54_,
    );
    lean_dec_ref(v_cmp_52_);
    return v_res_55_;
}
pub unsafe fn l_Std_DTreeMap_Raw_map___redArg(
    mut v_f_56_: *mut LeanObject,
    mut v_t_57_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
    v___x_58_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_56_, v_t_57_);
    return v___x_58_;
}
pub unsafe fn l_Std_DTreeMap_Raw_map(
    mut v_00_u03b1_59_: *mut LeanObject,
    mut v_00_u03b2_60_: *mut LeanObject,
    mut v_00_u03b3_61_: *mut LeanObject,
    mut v_cmp_62_: *mut LeanObject,
    mut v_f_63_: *mut LeanObject,
    mut v_t_64_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
    v___x_65_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_63_, v_t_64_);
    return v___x_65_;
}
pub unsafe fn l_Std_DTreeMap_Raw_map___boxed(
    mut v_00_u03b1_66_: *mut LeanObject,
    mut v_00_u03b2_67_: *mut LeanObject,
    mut v_00_u03b3_68_: *mut LeanObject,
    mut v_cmp_69_: *mut LeanObject,
    mut v_f_70_: *mut LeanObject,
    mut v_t_71_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_72_: *mut LeanObject = core::ptr::null_mut();
    v_res_72_ = l_Std_DTreeMap_Raw_map(
        v_00_u03b1_66_,
        v_00_u03b2_67_,
        v_00_u03b3_68_,
        v_cmp_69_,
        v_f_70_,
        v_t_71_,
    );
    lean_dec_ref(v_cmp_69_);
    return v_res_72_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
}
