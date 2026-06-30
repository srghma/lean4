// Lean compiler output
// Module: Std.Data.TreeSet.AdditionalOperations
// Imports: Std.Data.TreeSet.Raw.Basic Std.Data.TreeMap.AdditionalOperations
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg, l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg, l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg,
};
use crate::r#gen::Std::Data::TreeMap::AdditionalOperations::{
    initialize_Std_Data_TreeMap_AdditionalOperations,
    runtime_initialize_Std_Data_TreeMap_AdditionalOperations,
};
use crate::r#gen::Std::Data::TreeSet::Raw::Basic::{
    initialize_Std_Data_TreeSet_Raw_Basic, runtime_initialize_Std_Data_TreeSet_Raw_Basic,
};
pub unsafe fn l_Std_TreeSet_getGE___redArg(
    mut v_cmp_45_: *mut leanh::LeanObject,
    mut v_t_46_: *mut leanh::LeanObject,
    mut v_k_47_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_48_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_45_, v_k_47_, v_t_46_);
    return v___x_48_;
}
pub unsafe fn l_Std_TreeSet_getGE(
    mut v_00_u03b1_49_: *mut leanh::LeanObject,
    mut v_cmp_50_: *mut leanh::LeanObject,
    mut v_inst_51_: *mut leanh::LeanObject,
    mut v_t_52_: *mut leanh::LeanObject,
    mut v_k_53_: *mut leanh::LeanObject,
    mut v_h_54_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_55_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_50_, v_k_53_, v_t_52_);
    return v___x_55_;
}
pub unsafe fn l_Std_TreeSet_getGT___redArg(
    mut v_cmp_56_: *mut leanh::LeanObject,
    mut v_t_57_: *mut leanh::LeanObject,
    mut v_k_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_59_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_56_, v_k_58_, v_t_57_);
    return v___x_59_;
}
pub unsafe fn l_Std_TreeSet_getGT(
    mut v_00_u03b1_60_: *mut leanh::LeanObject,
    mut v_cmp_61_: *mut leanh::LeanObject,
    mut v_inst_62_: *mut leanh::LeanObject,
    mut v_t_63_: *mut leanh::LeanObject,
    mut v_k_64_: *mut leanh::LeanObject,
    mut v_h_65_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_66_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_61_, v_k_64_, v_t_63_);
    return v___x_66_;
}
pub unsafe fn l_Std_TreeSet_getLE___redArg(
    mut v_cmp_67_: *mut leanh::LeanObject,
    mut v_t_68_: *mut leanh::LeanObject,
    mut v_k_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_70_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_67_, v_k_69_, v_t_68_);
    return v___x_70_;
}
pub unsafe fn l_Std_TreeSet_getLE(
    mut v_00_u03b1_71_: *mut leanh::LeanObject,
    mut v_cmp_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
    mut v_t_74_: *mut leanh::LeanObject,
    mut v_k_75_: *mut leanh::LeanObject,
    mut v_h_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_77_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_72_, v_k_75_, v_t_74_);
    return v___x_77_;
}
pub unsafe fn l_Std_TreeSet_getLT___redArg(
    mut v_cmp_78_: *mut leanh::LeanObject,
    mut v_t_79_: *mut leanh::LeanObject,
    mut v_k_80_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_78_, v_k_80_, v_t_79_);
    return v___x_81_;
}
pub unsafe fn l_Std_TreeSet_getLT(
    mut v_00_u03b1_82_: *mut leanh::LeanObject,
    mut v_cmp_83_: *mut leanh::LeanObject,
    mut v_inst_84_: *mut leanh::LeanObject,
    mut v_t_85_: *mut leanh::LeanObject,
    mut v_k_86_: *mut leanh::LeanObject,
    mut v_h_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_88_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_83_, v_k_86_, v_t_85_);
    return v___x_88_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_AdditionalOperations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_AdditionalOperations(
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
pub unsafe fn initialize_Std_Data_TreeSet_AdditionalOperations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
}