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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_box, lean_closure_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
};
static mut l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_31_: *mut LeanObject = core::ptr::null_mut();
    v___x_30_ = lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_31_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_31_, 0, v___x_30_);
    return v___f_31_;
}
pub unsafe fn l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(
    mut v_inst_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_m_u2081_34_: *mut LeanObject,
    mut v_m_u2082_35_: *mut LeanObject,
) -> u8 {
    let mut v___f_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: u8 = 0;
    v___f_36_ = lean_obj_once(
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
    mut v_inst_38_: *mut LeanObject,
    mut v_inst_39_: *mut LeanObject,
    mut v_m_u2081_40_: *mut LeanObject,
    mut v_m_u2082_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_42_: u8 = 0;
    let mut v_r_43_: *mut LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_38_,
        v_inst_39_,
        v_m_u2081_40_,
        v_m_u2082_41_,
    );
    v_r_43_ = lean_box((v_res_42_) as usize);
    return v_r_43_;
}
pub unsafe fn l_Std_HashSet_instDecidableEquivOfLawfulBEq(
    mut v_00_u03b1_44_: *mut LeanObject,
    mut v_inst_45_: *mut LeanObject,
    mut v_inst_46_: *mut LeanObject,
    mut v_inst_47_: *mut LeanObject,
    mut v_m_u2081_48_: *mut LeanObject,
    mut v_m_u2082_49_: *mut LeanObject,
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
    mut v_00_u03b1_51_: *mut LeanObject,
    mut v_inst_52_: *mut LeanObject,
    mut v_inst_53_: *mut LeanObject,
    mut v_inst_54_: *mut LeanObject,
    mut v_m_u2081_55_: *mut LeanObject,
    mut v_m_u2082_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_57_: u8 = 0;
    let mut v_r_58_: *mut LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq(
        v_00_u03b1_51_,
        v_inst_52_,
        v_inst_53_,
        v_inst_54_,
        v_m_u2081_55_,
        v_m_u2082_56_,
    );
    v_r_58_ = lean_box((v_res_57_) as usize);
    return v_r_58_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashSet_DecidableEquiv(builtin);
}
