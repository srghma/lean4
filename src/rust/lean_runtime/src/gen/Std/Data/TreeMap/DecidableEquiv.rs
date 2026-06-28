// Lean compiler output
// Module: Std.Data.TreeMap.DecidableEquiv
// Imports: Std.Data.DTreeMap.DecidableEquiv Std.Data.TreeMap.Basic
use crate::r#gen::Std::Data::DTreeMap::DecidableEquiv::{
    initialize_Std_Data_DTreeMap_DecidableEquiv,
    runtime_initialize_Std_Data_DTreeMap_DecidableEquiv,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_beq___redArg;
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_box, lean_closure_set,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(
    mut v_inst_46_: *mut LeanObject,
    mut v_k_47_: *mut LeanObject,
    mut v___y_48_: *mut LeanObject,
    mut v___y_49_: *mut LeanObject,
) -> u8 {
    let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_51_: u8 = 0;
    v___x_50_ = lean_apply_2(v_inst_46_, v___y_48_, v___y_49_);
    v___x_51_ = (lean_unbox(v___x_50_) as u8);
    return v___x_51_;
}
pub unsafe fn l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed(
    mut v_inst_52_: *mut LeanObject,
    mut v_k_53_: *mut LeanObject,
    mut v___y_54_: *mut LeanObject,
    mut v___y_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_56_: u8 = 0;
    let mut v_r_57_: *mut LeanObject = core::ptr::null_mut();
    v_res_56_ =
        l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(
            v_inst_52_, v_k_53_, v___y_54_, v___y_55_,
        );
    lean_dec(v_k_53_);
    v_r_57_ = lean_box((v_res_56_) as usize);
    return v_r_57_;
}
pub unsafe fn l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
    mut v_cmp_58_: *mut LeanObject,
    mut v_inst_59_: *mut LeanObject,
    mut v_t_u2081_60_: *mut LeanObject,
    mut v_t_u2082_61_: *mut LeanObject,
) -> u8 {
    let mut v___f_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v_this_63_: u8 = 0;
    v___f_62_ = lean_alloc_closure(
        l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_62_, 0, v_inst_59_);
    v_this_63_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_58_,
        v___f_62_,
        v_t_u2081_60_,
        v_t_u2082_61_,
    );
    return v_this_63_;
}
pub unsafe fn l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(
    mut v_cmp_64_: *mut LeanObject,
    mut v_inst_65_: *mut LeanObject,
    mut v_t_u2081_66_: *mut LeanObject,
    mut v_t_u2082_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_68_: u8 = 0;
    let mut v_r_69_: *mut LeanObject = core::ptr::null_mut();
    v_res_68_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
        v_cmp_64_,
        v_inst_65_,
        v_t_u2081_66_,
        v_t_u2082_67_,
    );
    v_r_69_ = lean_box((v_res_68_) as usize);
    return v_r_69_;
}
pub unsafe fn l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(
    mut v_00_u03b1_70_: *mut LeanObject,
    mut v_00_u03b2_71_: *mut LeanObject,
    mut v_cmp_72_: *mut LeanObject,
    mut v_inst_73_: *mut LeanObject,
    mut v_inst_74_: *mut LeanObject,
    mut v_inst_75_: *mut LeanObject,
    mut v_inst_76_: *mut LeanObject,
    mut v_t_u2081_77_: *mut LeanObject,
    mut v_t_u2082_78_: *mut LeanObject,
) -> u8 {
    let mut v___x_79_: u8 = 0;
    v___x_79_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
        v_cmp_72_,
        v_inst_75_,
        v_t_u2081_77_,
        v_t_u2082_78_,
    );
    return v___x_79_;
}
pub unsafe fn l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(
    mut v_00_u03b1_80_: *mut LeanObject,
    mut v_00_u03b2_81_: *mut LeanObject,
    mut v_cmp_82_: *mut LeanObject,
    mut v_inst_83_: *mut LeanObject,
    mut v_inst_84_: *mut LeanObject,
    mut v_inst_85_: *mut LeanObject,
    mut v_inst_86_: *mut LeanObject,
    mut v_t_u2081_87_: *mut LeanObject,
    mut v_t_u2082_88_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_89_: u8 = 0;
    let mut v_r_90_: *mut LeanObject = core::ptr::null_mut();
    v_res_89_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(
        v_00_u03b1_80_,
        v_00_u03b2_81_,
        v_cmp_82_,
        v_inst_83_,
        v_inst_84_,
        v_inst_85_,
        v_inst_86_,
        v_t_u2081_87_,
        v_t_u2082_88_,
    );
    v_r_90_ = lean_box((v_res_89_) as usize);
    return v_r_90_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
}
