// Lean compiler output
// Module: Std.Data.HashMap.RawDecidableEquiv
// Imports: Std.Data.DHashMap.RawDecidableEquiv Std.Data.HashMap.Raw
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_beq___redArg;
use crate::r#gen::Std::Data::DHashMap::RawDecidableEquiv::{
    initialize_Std_Data_DHashMap_RawDecidableEquiv,
    runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv,
};
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0(
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_k_53_: *mut crate::leanh::LeanObject,
    mut v___y_54_: *mut crate::leanh::LeanObject,
    mut v___y_55_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: u8 = 0;
    v___x_56_ = crate::leanh::lean_apply_2(v_inst_52_, v___y_54_, v___y_55_);
    v___x_57_ = (crate::leanh::lean_unbox(v___x_56_) as u8);
    return v___x_57_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed(
    mut v_inst_58_: *mut crate::leanh::LeanObject,
    mut v_k_59_: *mut crate::leanh::LeanObject,
    mut v___y_60_: *mut crate::leanh::LeanObject,
    mut v___y_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_62_: u8 = 0;
    let mut v_r_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0(
        v_inst_58_, v_k_59_, v___y_60_, v___y_61_,
    );
    crate::leanh::lean_dec(v_k_59_);
    v_r_63_ = crate::leanh::lean_box((v_res_62_) as usize);
    return v_r_63_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___redArg(
    mut v_inst_64_: *mut crate::leanh::LeanObject,
    mut v_inst_65_: *mut crate::leanh::LeanObject,
    mut v_inst_66_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_67_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_68_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_70_: u8 = 0;
    v___f_69_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_69_, 0, v_inst_66_);
    v_this_70_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_64_,
        v_inst_65_,
        v___f_69_,
        v_m_u2081_67_,
        v_m_u2082_68_,
    );
    return v_this_70_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___redArg___boxed(
    mut v_inst_71_: *mut crate::leanh::LeanObject,
    mut v_inst_72_: *mut crate::leanh::LeanObject,
    mut v_inst_73_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_74_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_75_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_76_: u8 = 0;
    let mut v_r_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(
        v_inst_71_,
        v_inst_72_,
        v_inst_73_,
        v_m_u2081_74_,
        v_m_u2082_75_,
    );
    v_r_77_ = crate::leanh::lean_box((v_res_76_) as usize);
    return v_r_77_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_78_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_79_: *mut crate::leanh::LeanObject,
    mut v_inst_80_: *mut crate::leanh::LeanObject,
    mut v_inst_81_: *mut crate::leanh::LeanObject,
    mut v_inst_82_: *mut crate::leanh::LeanObject,
    mut v_inst_83_: *mut crate::leanh::LeanObject,
    mut v_inst_84_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_85_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_86_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_87_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_88_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_89_: u8 = 0;
    v___x_89_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(
        v_inst_80_,
        v_inst_82_,
        v_inst_83_,
        v_m_u2081_85_,
        v_m_u2082_86_,
    );
    return v___x_89_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___boxed(
    mut v_00_u03b1_90_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_91_: *mut crate::leanh::LeanObject,
    mut v_inst_92_: *mut crate::leanh::LeanObject,
    mut v_inst_93_: *mut crate::leanh::LeanObject,
    mut v_inst_94_: *mut crate::leanh::LeanObject,
    mut v_inst_95_: *mut crate::leanh::LeanObject,
    mut v_inst_96_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_97_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_98_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_99_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_101_: u8 = 0;
    let mut v_r_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_101_ = l_Std_HashMap_Raw_instDecidableEquiv(
        v_00_u03b1_90_,
        v_00_u03b2_91_,
        v_inst_92_,
        v_inst_93_,
        v_inst_94_,
        v_inst_95_,
        v_inst_96_,
        v_m_u2081_97_,
        v_m_u2082_98_,
        v_h_u2081_99_,
        v_h_u2082_100_,
    );
    v_r_102_ = crate::leanh::lean_box((v_res_101_) as usize);
    return v_r_102_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_RawDecidableEquiv(
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
pub unsafe fn initialize_Std_Data_HashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
}
