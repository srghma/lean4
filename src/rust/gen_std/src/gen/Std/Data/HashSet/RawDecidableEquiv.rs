// Lean compiler output
// Module: Std.Data.HashSet.RawDecidableEquiv
// Imports: Std.Data.HashMap.RawDecidableEquiv Std.Data.HashSet.Raw
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::HashMap::RawDecidableEquiv::{
    initialize_Std_Data_HashMap_RawDecidableEquiv, l_Std_HashMap_Raw_instDecidableEquiv___redArg,
    runtime_initialize_Std_Data_HashMap_RawDecidableEquiv,
};
use crate::r#gen::Std::Data::HashSet::Raw::{
    initialize_Std_Data_HashSet_Raw, runtime_initialize_Std_Data_HashSet_Raw,
};
static mut l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_34_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_35_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_34_ = leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_35_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_35_, 0, v___x_34_);
    return v___f_35_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableEquiv___redArg(
    mut v_inst_36_: *mut leanh::LeanObject,
    mut v_inst_37_: *mut leanh::LeanObject,
    mut v_m_u2081_38_: *mut leanh::LeanObject,
    mut v_m_u2082_39_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_41_: u8 = 0;
    v___f_40_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once),
        _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0,
    );
    v_this_41_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(
        v_inst_36_,
        v_inst_37_,
        v___f_40_,
        v_m_u2081_38_,
        v_m_u2082_39_,
    );
    return v_this_41_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableEquiv___redArg___boxed(
    mut v_inst_42_: *mut leanh::LeanObject,
    mut v_inst_43_: *mut leanh::LeanObject,
    mut v_m_u2081_44_: *mut leanh::LeanObject,
    mut v_m_u2082_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(
        v_inst_42_,
        v_inst_43_,
        v_m_u2081_44_,
        v_m_u2082_45_,
    );
    v_r_47_ = leanh::lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableEquiv(
    mut v_00_u03b1_48_: *mut leanh::LeanObject,
    mut v_inst_49_: *mut leanh::LeanObject,
    mut v_inst_50_: *mut leanh::LeanObject,
    mut v_inst_51_: *mut leanh::LeanObject,
    mut v_m_u2081_52_: *mut leanh::LeanObject,
    mut v_m_u2082_53_: *mut leanh::LeanObject,
    mut v_h_u2081_54_: *mut leanh::LeanObject,
    mut v_h_u2082_55_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_56_: u8 = 0;
    v___x_56_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(
        v_inst_49_,
        v_inst_51_,
        v_m_u2081_52_,
        v_m_u2082_53_,
    );
    return v___x_56_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableEquiv___boxed(
    mut v_00_u03b1_57_: *mut leanh::LeanObject,
    mut v_inst_58_: *mut leanh::LeanObject,
    mut v_inst_59_: *mut leanh::LeanObject,
    mut v_inst_60_: *mut leanh::LeanObject,
    mut v_m_u2081_61_: *mut leanh::LeanObject,
    mut v_m_u2082_62_: *mut leanh::LeanObject,
    mut v_h_u2081_63_: *mut leanh::LeanObject,
    mut v_h_u2082_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_65_: u8 = 0;
    let mut v_r_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_65_ = l_Std_HashSet_Raw_instDecidableEquiv(
        v_00_u03b1_57_,
        v_inst_58_,
        v_inst_59_,
        v_inst_60_,
        v_m_u2081_61_,
        v_m_u2082_62_,
        v_h_u2081_63_,
        v_h_u2082_64_,
    );
    v_r_66_ = leanh::lean_box((v_res_65_) as usize);
    return v_r_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_RawDecidableEquiv(
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
pub unsafe fn initialize_Std_Data_HashSet_RawDecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
}