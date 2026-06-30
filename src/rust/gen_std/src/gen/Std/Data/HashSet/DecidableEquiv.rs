// Lean compiler output
// Module: Std.Data.HashSet.DecidableEquiv
// Imports: Std.Data.HashMap.DecidableEquiv Std.Data.HashSet.Basic
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::HashMap::DecidableEquiv::{
    initialize_Std_Data_HashMap_DecidableEquiv,
    l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg,
    runtime_initialize_Std_Data_HashMap_DecidableEquiv,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
static mut l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_31_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_31_, 0, v___x_30_);
    return v___f_31_;
}
pub unsafe fn l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(
    mut v_inst_32_: *mut leanh::LeanObject,
    mut v_inst_33_: *mut leanh::LeanObject,
    mut v_m_u2081_34_: *mut leanh::LeanObject,
    mut v_m_u2082_35_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_37_: u8 = 0;
    v___f_36_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0_once
        ),
        _init_l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0,
    );
    v___x_37_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_32_,
        v_inst_33_,
        v___f_36_,
        v_m_u2081_34_,
        v_m_u2082_35_,
    );
    return v___x_37_;
}
pub unsafe fn l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___boxed(
    mut v_inst_38_: *mut leanh::LeanObject,
    mut v_inst_39_: *mut leanh::LeanObject,
    mut v_m_u2081_40_: *mut leanh::LeanObject,
    mut v_m_u2082_41_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_42_: u8 = 0;
    let mut v_r_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_38_,
        v_inst_39_,
        v_m_u2081_40_,
        v_m_u2082_41_,
    );
    v_r_43_ = leanh::lean_box((v_res_42_) as usize);
    return v_r_43_;
}
pub unsafe fn l_Std_HashSet_instDecidableEquivOfLawfulBEq(
    mut v_00_u03b1_44_: *mut leanh::LeanObject,
    mut v_inst_45_: *mut leanh::LeanObject,
    mut v_inst_46_: *mut leanh::LeanObject,
    mut v_inst_47_: *mut leanh::LeanObject,
    mut v_m_u2081_48_: *mut leanh::LeanObject,
    mut v_m_u2082_49_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_50_: u8 = 0;
    v___x_50_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_45_,
        v_inst_47_,
        v_m_u2081_48_,
        v_m_u2082_49_,
    );
    return v___x_50_;
}
pub unsafe fn l_Std_HashSet_instDecidableEquivOfLawfulBEq___boxed(
    mut v_00_u03b1_51_: *mut leanh::LeanObject,
    mut v_inst_52_: *mut leanh::LeanObject,
    mut v_inst_53_: *mut leanh::LeanObject,
    mut v_inst_54_: *mut leanh::LeanObject,
    mut v_m_u2081_55_: *mut leanh::LeanObject,
    mut v_m_u2082_56_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_57_: u8 = 0;
    let mut v_r_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq(
        v_00_u03b1_51_,
        v_inst_52_,
        v_inst_53_,
        v_inst_54_,
        v_m_u2081_55_,
        v_m_u2082_56_,
    );
    v_r_58_ = leanh::lean_box((v_res_57_) as usize);
    return v_r_58_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_DecidableEquiv(
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
pub unsafe fn initialize_Std_Data_HashSet_DecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_DecidableEquiv(builtin);
}