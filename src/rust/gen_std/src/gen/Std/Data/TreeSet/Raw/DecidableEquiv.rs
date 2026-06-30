// Lean compiler output
// Module: Std.Data.TreeSet.Raw.DecidableEquiv
// Imports: Std.Data.TreeMap.Raw.DecidableEquiv Std.Data.TreeSet.Raw.Basic
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::TreeMap::Raw::DecidableEquiv::{
    initialize_Std_Data_TreeMap_Raw_DecidableEquiv, l_Std_TreeMap_Raw_instDecidableEquiv___redArg,
    runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv,
};
use crate::r#gen::Std::Data::TreeSet::Raw::Basic::{
    initialize_Std_Data_TreeSet_Raw_Basic, runtime_initialize_Std_Data_TreeSet_Raw_Basic,
};
static mut l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_33_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_32_ = leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_33_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_33_, 0, v___x_32_);
    return v___f_33_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableEquiv___redArg(
    mut v_cmp_34_: *mut leanh::LeanObject,
    mut v_t_u2081_35_: *mut leanh::LeanObject,
    mut v_t_u2082_36_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_38_: u8 = 0;
    v___f_37_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0_once),
        _init_l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0,
    );
    v_this_38_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg(
        v_cmp_34_,
        v___f_37_,
        v_t_u2081_35_,
        v_t_u2082_36_,
    );
    return v_this_38_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableEquiv___redArg___boxed(
    mut v_cmp_39_: *mut leanh::LeanObject,
    mut v_t_u2081_40_: *mut leanh::LeanObject,
    mut v_t_u2082_41_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_42_: u8 = 0;
    let mut v_r_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_42_ =
        l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_39_, v_t_u2081_40_, v_t_u2082_41_);
    v_r_43_ = leanh::lean_box((v_res_42_) as usize);
    return v_r_43_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableEquiv(
    mut v_00_u03b1_44_: *mut leanh::LeanObject,
    mut v_cmp_45_: *mut leanh::LeanObject,
    mut v_inst_46_: *mut leanh::LeanObject,
    mut v_inst_47_: *mut leanh::LeanObject,
    mut v_t_u2081_48_: *mut leanh::LeanObject,
    mut v_t_u2082_49_: *mut leanh::LeanObject,
    mut v_h_u2081_50_: *mut leanh::LeanObject,
    mut v_h_u2082_51_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_52_: u8 = 0;
    v___x_52_ =
        l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_45_, v_t_u2081_48_, v_t_u2082_49_);
    return v___x_52_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableEquiv___boxed(
    mut v_00_u03b1_53_: *mut leanh::LeanObject,
    mut v_cmp_54_: *mut leanh::LeanObject,
    mut v_inst_55_: *mut leanh::LeanObject,
    mut v_inst_56_: *mut leanh::LeanObject,
    mut v_t_u2081_57_: *mut leanh::LeanObject,
    mut v_t_u2082_58_: *mut leanh::LeanObject,
    mut v_h_u2081_59_: *mut leanh::LeanObject,
    mut v_h_u2082_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_61_: u8 = 0;
    let mut v_r_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_61_ = l_Std_TreeSet_Raw_instDecidableEquiv(
        v_00_u03b1_53_,
        v_cmp_54_,
        v_inst_55_,
        v_inst_56_,
        v_t_u2081_57_,
        v_t_u2082_58_,
        v_h_u2081_59_,
        v_h_u2082_60_,
    );
    v_r_62_ = leanh::lean_box((v_res_61_) as usize);
    return v_r_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(
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
pub unsafe fn initialize_Std_Data_TreeSet_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
}