// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.WF.Defs
// Imports: Std.Data.DTreeMap.Internal.Operations
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    initialize_Std_Data_DTreeMap_Internal_Operations,
    runtime_initialize_Std_Data_DTreeMap_Internal_Operations,
};
pub unsafe fn l_Std_DTreeMap_Internal_instCoeTypeForall__std(
    mut v_00_u03b1_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_46_ = leanh::lean_box(0);
    return v___x_46_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Defs_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_47_: *mut leanh::LeanObject,
    mut v_h__1_48_: *mut leanh::LeanObject,
    mut v_h__2_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_47_) == 0 {
        let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_49_);
        v___x_50_ = leanh::lean_box(0);
        v___x_51_ = leanh::lean_apply_1(v_h__1_48_, v___x_50_);
        return v___x_51_;
    } else {
        let mut v_val_52_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_48_);
        v_val_52_ = leanh::lean_ctor_get(v_x_47_, 0);
        leanh::lean_inc(v_val_52_);
        leanh::lean_dec_ref_known(v_x_47_, 1);
        v___x_53_ = leanh::lean_apply_1(v_h__2_49_, v_val_52_);
        return v___x_53_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Defs_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b1_54_: *mut leanh::LeanObject,
    mut v_00_u03b2_55_: *mut leanh::LeanObject,
    mut v_k_56_: *mut leanh::LeanObject,
    mut v_motive_57_: *mut leanh::LeanObject,
    mut v_x_58_: *mut leanh::LeanObject,
    mut v_h__1_59_: *mut leanh::LeanObject,
    mut v_h__2_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_58_) == 0 {
        let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_60_);
        v___x_61_ = leanh::lean_box(0);
        v___x_62_ = leanh::lean_apply_1(v_h__1_59_, v___x_61_);
        return v___x_62_;
    } else {
        let mut v_val_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_59_);
        v_val_63_ = leanh::lean_ctor_get(v_x_58_, 0);
        leanh::lean_inc(v_val_63_);
        leanh::lean_dec_ref_known(v_x_58_, 1);
        v___x_64_ = leanh::lean_apply_1(v_h__2_60_, v_val_63_);
        return v___x_64_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Defs_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_65_: *mut leanh::LeanObject,
    mut v_00_u03b2_66_: *mut leanh::LeanObject,
    mut v_k_67_: *mut leanh::LeanObject,
    mut v_motive_68_: *mut leanh::LeanObject,
    mut v_x_69_: *mut leanh::LeanObject,
    mut v_h__1_70_: *mut leanh::LeanObject,
    mut v_h__2_71_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l___private_Std_Data_DTreeMap_Internal_WF_Defs_0__Std_DTreeMap_Internal_Impl_getThenInsertIfNew_x3f_match__1_splitter(v_00_u03b1_65_, v_00_u03b2_66_, v_k_67_, v_motive_68_, v_x_69_, v_h__1_70_, v_h__2_71_);
    leanh::lean_dec(v_k_67_);
    return v_res_72_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Defs_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter___redArg(
    mut v_x_73_: *mut leanh::LeanObject,
    mut v_h__1_74_: *mut leanh::LeanObject,
    mut v_h__2_75_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_73_) == 0 {
        let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_75_);
        v___x_76_ = leanh::lean_box(0);
        v___x_77_ = leanh::lean_apply_1(v_h__1_74_, v___x_76_);
        return v___x_77_;
    } else {
        let mut v_val_78_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_74_);
        v_val_78_ = leanh::lean_ctor_get(v_x_73_, 0);
        leanh::lean_inc(v_val_78_);
        leanh::lean_dec_ref_known(v_x_73_, 1);
        v___x_79_ = leanh::lean_apply_1(v_h__2_75_, v_val_78_);
        return v___x_79_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_WF_Defs_0__Std_DTreeMap_Internal_Impl_Const_getThenInsertIfNew_x3f_match__1_splitter(
    mut v_00_u03b2_80_: *mut leanh::LeanObject,
    mut v_motive_81_: *mut leanh::LeanObject,
    mut v_x_82_: *mut leanh::LeanObject,
    mut v_h__1_83_: *mut leanh::LeanObject,
    mut v_h__2_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_82_) == 0 {
        let mut v___x_85_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_84_);
        v___x_85_ = leanh::lean_box(0);
        v___x_86_ = leanh::lean_apply_1(v_h__1_83_, v___x_85_);
        return v___x_86_;
    } else {
        let mut v_val_87_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_83_);
        v_val_87_ = leanh::lean_ctor_get(v_x_82_, 0);
        leanh::lean_inc(v_val_87_);
        leanh::lean_dec_ref_known(v_x_82_, 1);
        v___x_88_ = leanh::lean_apply_1(v_h__2_84_, v_val_87_);
        return v___x_88_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_WF_Defs(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_WF_Defs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
}