// Lean compiler output
// Module: Lean.Data.NameMap.AdditionalOperations
// Imports: Lean.Data.NameMap.Basic Std.Data.TreeSet.AdditionalOperations
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic, runtime_initialize_Lean_Data_NameMap_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_link___redArg, l_Std_DTreeMap_Internal_Impl_link2___redArg,
};
use crate::r#gen::Std::Data::TreeSet::AdditionalOperations::{
    initialize_Std_Data_TreeSet_AdditionalOperations,
    runtime_initialize_Std_Data_TreeSet_AdditionalOperations,
};
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(
    mut v_f_30_: *mut leanh::LeanObject,
    mut v_t_31_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_31_) == 0 {
        let mut v_k_32_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_33_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_34_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_35_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_32_ = leanh::lean_ctor_get(v_t_31_, 1);
        leanh::lean_inc_n(v_k_32_, 2);
        v_v_33_ = leanh::lean_ctor_get(v_t_31_, 2);
        leanh::lean_inc(v_v_33_);
        v_l_34_ = leanh::lean_ctor_get(v_t_31_, 3);
        leanh::lean_inc(v_l_34_);
        v_r_35_ = leanh::lean_ctor_get(v_t_31_, 4);
        leanh::lean_inc(v_r_35_);
        leanh::lean_dec_ref_known(v_t_31_, 5);
        leanh::lean_inc_ref(v_f_30_);
        v___x_36_ = leanh::lean_apply_2(v_f_30_, v_k_32_, v_v_33_);
        if leanh::lean_obj_tag(v___x_36_) == 0 {
            let mut v_impl_37_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_38_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_k_32_);
            leanh::lean_inc_ref(v_f_30_);
            v_impl_37_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_30_, v_l_34_);
            v_impl_38_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_30_, v_r_35_);
            v___x_39_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_37_, v_impl_38_);
            return v___x_39_;
        } else {
            let mut v_val_40_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_41_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_42_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_40_ = leanh::lean_ctor_get(v___x_36_, 0);
            leanh::lean_inc(v_val_40_);
            leanh::lean_dec_ref_known(v___x_36_, 1);
            leanh::lean_inc_ref(v_f_30_);
            v_impl_41_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_30_, v_l_34_);
            v_impl_42_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_30_, v_r_35_);
            v___x_43_ = l_Std_DTreeMap_Internal_Impl_link___redArg(
                v_k_32_, v_val_40_, v_impl_41_, v_impl_42_,
            );
            return v___x_43_;
        }
    } else {
        let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_30_);
        v___x_44_ = leanh::lean_box(1);
        return v___x_44_;
    }
}
pub unsafe fn l_Lean_NameMap_filterMap___redArg(
    mut v_f_45_: *mut leanh::LeanObject,
    mut v_m_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_47_ =
        l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(
            v_f_45_, v_m_46_,
        );
    return v___x_47_;
}
pub unsafe fn l_Lean_NameMap_filterMap(
    mut v_00_u03b1_48_: *mut leanh::LeanObject,
    mut v_00_u03b2_49_: *mut leanh::LeanObject,
    mut v_f_50_: *mut leanh::LeanObject,
    mut v_m_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_52_ =
        l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(
            v_f_50_, v_m_51_,
        );
    return v___x_52_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0(
    mut v_00_u03b1_53_: *mut leanh::LeanObject,
    mut v_00_u03b2_54_: *mut leanh::LeanObject,
    mut v_f_55_: *mut leanh::LeanObject,
    mut v_t_56_: *mut leanh::LeanObject,
    mut v_hl_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_58_ =
        l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(
            v_f_55_, v_t_56_,
        );
    return v___x_58_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_NameMap_AdditionalOperations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_NameMap_AdditionalOperations(
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
pub unsafe fn initialize_Lean_Data_NameMap_AdditionalOperations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_NameMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_NameMap_AdditionalOperations(builtin);
}