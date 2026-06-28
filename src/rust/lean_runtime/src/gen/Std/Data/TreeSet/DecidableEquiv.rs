// Lean compiler output
// Module: Std.Data.TreeSet.DecidableEquiv
// Imports: Std.Data.TreeMap.DecidableEquiv Std.Data.TreeSet.Basic
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::TreeMap::DecidableEquiv::{
    initialize_Std_Data_TreeMap_DecidableEquiv,
    l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg,
    runtime_initialize_Std_Data_TreeMap_DecidableEquiv,
};
use crate::r#gen::Std::Data::TreeSet::Basic::{
    initialize_Std_Data_TreeSet_Basic, runtime_initialize_Std_Data_TreeSet_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_box, lean_closure_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
};
static mut l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_29_: *mut LeanObject = core::ptr::null_mut();
    v___x_28_ = lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_29_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_29_, 0, v___x_28_);
    return v___f_29_;
}
pub unsafe fn l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(
    mut v_cmp_30_: *mut LeanObject,
    mut v_t_u2081_31_: *mut LeanObject,
    mut v_t_u2082_32_: *mut LeanObject,
) -> u8 {
    let mut v___f_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_34_: u8 = 0;
    v___f_33_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0_once
        ),
        _init_l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0,
    );
    v___x_34_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
        v_cmp_30_,
        v___f_33_,
        v_t_u2081_31_,
        v_t_u2082_32_,
    );
    return v___x_34_;
}
pub unsafe fn l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___boxed(
    mut v_cmp_35_: *mut LeanObject,
    mut v_t_u2081_36_: *mut LeanObject,
    mut v_t_u2082_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_38_: u8 = 0;
    let mut v_r_39_: *mut LeanObject = core::ptr::null_mut();
    v_res_38_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(
        v_cmp_35_,
        v_t_u2081_36_,
        v_t_u2082_37_,
    );
    v_r_39_ = lean_box((v_res_38_) as usize);
    return v_r_39_;
}
pub unsafe fn l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(
    mut v_00_u03b1_40_: *mut LeanObject,
    mut v_cmp_41_: *mut LeanObject,
    mut v_inst_42_: *mut LeanObject,
    mut v_inst_43_: *mut LeanObject,
    mut v_t_u2081_44_: *mut LeanObject,
    mut v_t_u2082_45_: *mut LeanObject,
) -> u8 {
    let mut v___x_46_: u8 = 0;
    v___x_46_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(
        v_cmp_41_,
        v_t_u2081_44_,
        v_t_u2082_45_,
    );
    return v___x_46_;
}
pub unsafe fn l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___boxed(
    mut v_00_u03b1_47_: *mut LeanObject,
    mut v_cmp_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_t_u2081_51_: *mut LeanObject,
    mut v_t_u2082_52_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_53_: u8 = 0;
    let mut v_r_54_: *mut LeanObject = core::ptr::null_mut();
    v_res_53_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(
        v_00_u03b1_47_,
        v_cmp_48_,
        v_inst_49_,
        v_inst_50_,
        v_t_u2081_51_,
        v_t_u2082_52_,
    );
    v_r_54_ = lean_box((v_res_53_) as usize);
    return v_r_54_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_DecidableEquiv(builtin);
}
