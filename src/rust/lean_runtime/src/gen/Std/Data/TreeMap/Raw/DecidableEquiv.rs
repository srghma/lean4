// Lean compiler output
// Module: Std.Data.TreeMap.Raw.DecidableEquiv
// Imports: Std.Data.DTreeMap.DecidableEquiv Std.Data.TreeMap.Raw.Basic
use crate::r#gen::Std::Data::DTreeMap::DecidableEquiv::{
    initialize_Std_Data_DTreeMap_DecidableEquiv,
    runtime_initialize_Std_Data_DTreeMap_DecidableEquiv,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_beq___redArg;
use crate::r#gen::Std::Data::TreeMap::Raw::Basic::{
    initialize_Std_Data_TreeMap_Raw_Basic, runtime_initialize_Std_Data_TreeMap_Raw_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_box, lean_closure_set,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0(
    mut v_inst_50_: *mut LeanObject,
    mut v_k_51_: *mut LeanObject,
    mut v___y_52_: *mut LeanObject,
    mut v___y_53_: *mut LeanObject,
) -> u8 {
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_55_: u8 = 0;
    v___x_54_ = lean_apply_2(v_inst_50_, v___y_52_, v___y_53_);
    v___x_55_ = (lean_unbox(v___x_54_) as u8);
    return v___x_55_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0___boxed(
    mut v_inst_56_: *mut LeanObject,
    mut v_k_57_: *mut LeanObject,
    mut v___y_58_: *mut LeanObject,
    mut v___y_59_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_60_: u8 = 0;
    let mut v_r_61_: *mut LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0(
        v_inst_56_, v_k_57_, v___y_58_, v___y_59_,
    );
    lean_dec(v_k_57_);
    v_r_61_ = lean_box((v_res_60_) as usize);
    return v_r_61_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg(
    mut v_cmp_62_: *mut LeanObject,
    mut v_inst_63_: *mut LeanObject,
    mut v_t_u2081_64_: *mut LeanObject,
    mut v_t_u2082_65_: *mut LeanObject,
) -> u8 {
    let mut v___f_66_: *mut LeanObject = core::ptr::null_mut();
    let mut v_this_67_: u8 = 0;
    v___f_66_ = lean_alloc_closure(
        l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_66_, 0, v_inst_63_);
    v_this_67_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_62_,
        v___f_66_,
        v_t_u2081_64_,
        v_t_u2082_65_,
    );
    return v_this_67_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg___boxed(
    mut v_cmp_68_: *mut LeanObject,
    mut v_inst_69_: *mut LeanObject,
    mut v_t_u2081_70_: *mut LeanObject,
    mut v_t_u2082_71_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_72_: u8 = 0;
    let mut v_r_73_: *mut LeanObject = core::ptr::null_mut();
    v_res_72_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg(
        v_cmp_68_,
        v_inst_69_,
        v_t_u2081_70_,
        v_t_u2082_71_,
    );
    v_r_73_ = lean_box((v_res_72_) as usize);
    return v_r_73_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_74_: *mut LeanObject,
    mut v_00_u03b2_75_: *mut LeanObject,
    mut v_cmp_76_: *mut LeanObject,
    mut v_inst_77_: *mut LeanObject,
    mut v_inst_78_: *mut LeanObject,
    mut v_inst_79_: *mut LeanObject,
    mut v_inst_80_: *mut LeanObject,
    mut v_t_u2081_81_: *mut LeanObject,
    mut v_t_u2082_82_: *mut LeanObject,
    mut v_h_u2081_83_: *mut LeanObject,
    mut v_h_u2082_84_: *mut LeanObject,
) -> u8 {
    let mut v___x_85_: u8 = 0;
    v___x_85_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg(
        v_cmp_76_,
        v_inst_79_,
        v_t_u2081_81_,
        v_t_u2082_82_,
    );
    return v___x_85_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___boxed(
    mut v_00_u03b1_86_: *mut LeanObject,
    mut v_00_u03b2_87_: *mut LeanObject,
    mut v_cmp_88_: *mut LeanObject,
    mut v_inst_89_: *mut LeanObject,
    mut v_inst_90_: *mut LeanObject,
    mut v_inst_91_: *mut LeanObject,
    mut v_inst_92_: *mut LeanObject,
    mut v_t_u2081_93_: *mut LeanObject,
    mut v_t_u2082_94_: *mut LeanObject,
    mut v_h_u2081_95_: *mut LeanObject,
    mut v_h_u2082_96_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_97_: u8 = 0;
    let mut v_r_98_: *mut LeanObject = core::ptr::null_mut();
    v_res_97_ = l_Std_TreeMap_Raw_instDecidableEquiv(
        v_00_u03b1_86_,
        v_00_u03b2_87_,
        v_cmp_88_,
        v_inst_89_,
        v_inst_90_,
        v_inst_91_,
        v_inst_92_,
        v_t_u2081_93_,
        v_t_u2082_94_,
        v_h_u2081_95_,
        v_h_u2082_96_,
    );
    v_r_98_ = lean_box((v_res_97_) as usize);
    return v_r_98_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
}
