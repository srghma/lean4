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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_box, lean_closure_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
};
static mut l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_35_: *mut LeanObject = core::ptr::null_mut();
    v___x_34_ = lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_35_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_35_, 0, v___x_34_);
    return v___f_35_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableEquiv___redArg(
    mut v_inst_36_: *mut LeanObject,
    mut v_inst_37_: *mut LeanObject,
    mut v_m_u2081_38_: *mut LeanObject,
    mut v_m_u2082_39_: *mut LeanObject,
) -> u8 {
    let mut v___f_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v_this_41_: u8 = 0;
    v___f_40_ = lean_obj_once(
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
    mut v_inst_42_: *mut LeanObject,
    mut v_inst_43_: *mut LeanObject,
    mut v_m_u2081_44_: *mut LeanObject,
    mut v_m_u2082_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(
        v_inst_42_,
        v_inst_43_,
        v_m_u2081_44_,
        v_m_u2082_45_,
    );
    v_r_47_ = lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableEquiv(
    mut v_00_u03b1_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
    mut v_m_u2081_52_: *mut LeanObject,
    mut v_m_u2082_53_: *mut LeanObject,
    mut v_h_u2081_54_: *mut LeanObject,
    mut v_h_u2082_55_: *mut LeanObject,
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
    mut v_00_u03b1_57_: *mut LeanObject,
    mut v_inst_58_: *mut LeanObject,
    mut v_inst_59_: *mut LeanObject,
    mut v_inst_60_: *mut LeanObject,
    mut v_m_u2081_61_: *mut LeanObject,
    mut v_m_u2082_62_: *mut LeanObject,
    mut v_h_u2081_63_: *mut LeanObject,
    mut v_h_u2082_64_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_65_: u8 = 0;
    let mut v_r_66_: *mut LeanObject = core::ptr::null_mut();
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
    v_r_66_ = lean_box((v_res_65_) as usize);
    return v_r_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_RawDecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
}
