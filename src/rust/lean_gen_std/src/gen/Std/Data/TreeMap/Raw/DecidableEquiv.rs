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
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0(
    mut v_inst_50_: *mut crate::leanh::LeanObject,
    mut v_k_51_: *mut crate::leanh::LeanObject,
    mut v___y_52_: *mut crate::leanh::LeanObject,
    mut v___y_53_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: u8 = 0;
    v___x_54_ = crate::leanh::lean_apply_2(v_inst_50_, v___y_52_, v___y_53_);
    v___x_55_ = (crate::leanh::lean_unbox(v___x_54_) as u8);
    return v___x_55_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0___boxed(
    mut v_inst_56_: *mut crate::leanh::LeanObject,
    mut v_k_57_: *mut crate::leanh::LeanObject,
    mut v___y_58_: *mut crate::leanh::LeanObject,
    mut v___y_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: u8 = 0;
    let mut v_r_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0(
        v_inst_56_, v_k_57_, v___y_58_, v___y_59_,
    );
    crate::leanh::lean_dec(v_k_57_);
    v_r_61_ = crate::leanh::lean_box((v_res_60_) as usize);
    return v_r_61_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg(
    mut v_cmp_62_: *mut crate::leanh::LeanObject,
    mut v_inst_63_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_64_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_65_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_67_: u8 = 0;
    v___f_66_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instDecidableEquiv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_66_, 0, v_inst_63_);
    v_this_67_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_62_,
        v___f_66_,
        v_t_u2081_64_,
        v_t_u2082_65_,
    );
    return v_this_67_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv___redArg___boxed(
    mut v_cmp_68_: *mut crate::leanh::LeanObject,
    mut v_inst_69_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_70_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_72_: u8 = 0;
    let mut v_r_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg(
        v_cmp_68_,
        v_inst_69_,
        v_t_u2081_70_,
        v_t_u2082_71_,
    );
    v_r_73_ = crate::leanh::lean_box((v_res_72_) as usize);
    return v_r_73_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_74_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_75_: *mut crate::leanh::LeanObject,
    mut v_cmp_76_: *mut crate::leanh::LeanObject,
    mut v_inst_77_: *mut crate::leanh::LeanObject,
    mut v_inst_78_: *mut crate::leanh::LeanObject,
    mut v_inst_79_: *mut crate::leanh::LeanObject,
    mut v_inst_80_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_81_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_82_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_83_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_84_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_86_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_87_: *mut crate::leanh::LeanObject,
    mut v_cmp_88_: *mut crate::leanh::LeanObject,
    mut v_inst_89_: *mut crate::leanh::LeanObject,
    mut v_inst_90_: *mut crate::leanh::LeanObject,
    mut v_inst_91_: *mut crate::leanh::LeanObject,
    mut v_inst_92_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_93_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_94_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_95_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_97_: u8 = 0;
    let mut v_r_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    v_r_98_ = crate::leanh::lean_box((v_res_97_) as usize);
    return v_r_98_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Raw_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
}
