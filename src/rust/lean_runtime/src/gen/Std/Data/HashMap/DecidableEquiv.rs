// Lean compiler output
// Module: Std.Data.HashMap.DecidableEquiv
// Imports: Std.Data.DHashMap.DecidableEquiv Std.Data.HashMap.Basic
use crate::r#gen::Std::Data::DHashMap::DecidableEquiv::{
    initialize_Std_Data_DHashMap_DecidableEquiv,
    runtime_initialize_Std_Data_DHashMap_DecidableEquiv,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_beq___redArg;
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
pub unsafe fn l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0(
    mut v_inst_48_: *mut crate::leanh::LeanObject,
    mut v_k_49_: *mut crate::leanh::LeanObject,
    mut v___y_50_: *mut crate::leanh::LeanObject,
    mut v___y_51_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: u8 = 0;
    v___x_52_ = crate::leanh::lean_apply_2(v_inst_48_, v___y_50_, v___y_51_);
    v___x_53_ = (crate::leanh::lean_unbox(v___x_52_) as u8);
    return v___x_53_;
}
pub unsafe fn l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed(
    mut v_inst_54_: *mut crate::leanh::LeanObject,
    mut v_k_55_: *mut crate::leanh::LeanObject,
    mut v___y_56_: *mut crate::leanh::LeanObject,
    mut v___y_57_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_58_: u8 = 0;
    let mut v_r_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_58_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0(
        v_inst_54_, v_k_55_, v___y_56_, v___y_57_,
    );
    crate::leanh::lean_dec(v_k_55_);
    v_r_59_ = crate::leanh::lean_box((v_res_58_) as usize);
    return v_r_59_;
}
pub unsafe fn l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(
    mut v_inst_60_: *mut crate::leanh::LeanObject,
    mut v_inst_61_: *mut crate::leanh::LeanObject,
    mut v_inst_62_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_63_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_64_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_66_: u8 = 0;
    v___f_65_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_65_, 0, v_inst_62_);
    v_this_66_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_60_,
        v_inst_61_,
        v___f_65_,
        v_m_u2081_63_,
        v_m_u2082_64_,
    );
    return v_this_66_;
}
pub unsafe fn l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___boxed(
    mut v_inst_67_: *mut crate::leanh::LeanObject,
    mut v_inst_68_: *mut crate::leanh::LeanObject,
    mut v_inst_69_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_70_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_72_: u8 = 0;
    let mut v_r_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_67_,
        v_inst_68_,
        v_inst_69_,
        v_m_u2081_70_,
        v_m_u2082_71_,
    );
    v_r_73_ = crate::leanh::lean_box((v_res_72_) as usize);
    return v_r_73_;
}
pub unsafe fn l_Std_HashMap_instDecidableEquivOfLawfulBEq(
    mut v_00_u03b1_74_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_75_: *mut crate::leanh::LeanObject,
    mut v_inst_76_: *mut crate::leanh::LeanObject,
    mut v_inst_77_: *mut crate::leanh::LeanObject,
    mut v_inst_78_: *mut crate::leanh::LeanObject,
    mut v_inst_79_: *mut crate::leanh::LeanObject,
    mut v_inst_80_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_81_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_82_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_83_: u8 = 0;
    v___x_83_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(
        v_inst_76_,
        v_inst_78_,
        v_inst_79_,
        v_m_u2081_81_,
        v_m_u2082_82_,
    );
    return v___x_83_;
}
pub unsafe fn l_Std_HashMap_instDecidableEquivOfLawfulBEq___boxed(
    mut v_00_u03b1_84_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_85_: *mut crate::leanh::LeanObject,
    mut v_inst_86_: *mut crate::leanh::LeanObject,
    mut v_inst_87_: *mut crate::leanh::LeanObject,
    mut v_inst_88_: *mut crate::leanh::LeanObject,
    mut v_inst_89_: *mut crate::leanh::LeanObject,
    mut v_inst_90_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_91_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_92_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_93_: u8 = 0;
    let mut v_r_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_93_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq(
        v_00_u03b1_84_,
        v_00_u03b2_85_,
        v_inst_86_,
        v_inst_87_,
        v_inst_88_,
        v_inst_89_,
        v_inst_90_,
        v_m_u2081_91_,
        v_m_u2082_92_,
    );
    v_r_94_ = crate::leanh::lean_box((v_res_93_) as usize);
    return v_r_94_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_DecidableEquiv(
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
pub unsafe fn initialize_Std_Data_HashMap_DecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_DecidableEquiv(builtin);
}
