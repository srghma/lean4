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
    mut v_inst_52_: *mut leanh::LeanObject,
    mut v_k_53_: *mut leanh::LeanObject,
    mut v___y_54_: *mut leanh::LeanObject,
    mut v___y_55_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: u8 = 0;
    v___x_56_ = leanh::lean_apply_2(v_inst_52_, v___y_54_, v___y_55_);
    v___x_57_ = (leanh::lean_unbox(v___x_56_) as u8);
    return v___x_57_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed(
    mut v_inst_58_: *mut leanh::LeanObject,
    mut v_k_59_: *mut leanh::LeanObject,
    mut v___y_60_: *mut leanh::LeanObject,
    mut v___y_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_62_: u8 = 0;
    let mut v_r_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0(
        v_inst_58_, v_k_59_, v___y_60_, v___y_61_,
    );
    leanh::lean_dec(v_k_59_);
    v_r_63_ = leanh::lean_box((v_res_62_) as usize);
    return v_r_63_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv___redArg(
    mut v_inst_64_: *mut leanh::LeanObject,
    mut v_inst_65_: *mut leanh::LeanObject,
    mut v_inst_66_: *mut leanh::LeanObject,
    mut v_m_u2081_67_: *mut leanh::LeanObject,
    mut v_m_u2082_68_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_70_: u8 = 0;
    v___f_69_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_69_, 0, v_inst_66_);
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
    mut v_inst_71_: *mut leanh::LeanObject,
    mut v_inst_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
    mut v_m_u2081_74_: *mut leanh::LeanObject,
    mut v_m_u2082_75_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_76_: u8 = 0;
    let mut v_r_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(
        v_inst_71_,
        v_inst_72_,
        v_inst_73_,
        v_m_u2081_74_,
        v_m_u2082_75_,
    );
    v_r_77_ = leanh::lean_box((v_res_76_) as usize);
    return v_r_77_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableEquiv(
    mut v_00_u03b1_78_: *mut leanh::LeanObject,
    mut v_00_u03b2_79_: *mut leanh::LeanObject,
    mut v_inst_80_: *mut leanh::LeanObject,
    mut v_inst_81_: *mut leanh::LeanObject,
    mut v_inst_82_: *mut leanh::LeanObject,
    mut v_inst_83_: *mut leanh::LeanObject,
    mut v_inst_84_: *mut leanh::LeanObject,
    mut v_m_u2081_85_: *mut leanh::LeanObject,
    mut v_m_u2082_86_: *mut leanh::LeanObject,
    mut v_h_u2081_87_: *mut leanh::LeanObject,
    mut v_h_u2082_88_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_90_: *mut leanh::LeanObject,
    mut v_00_u03b2_91_: *mut leanh::LeanObject,
    mut v_inst_92_: *mut leanh::LeanObject,
    mut v_inst_93_: *mut leanh::LeanObject,
    mut v_inst_94_: *mut leanh::LeanObject,
    mut v_inst_95_: *mut leanh::LeanObject,
    mut v_inst_96_: *mut leanh::LeanObject,
    mut v_m_u2081_97_: *mut leanh::LeanObject,
    mut v_m_u2082_98_: *mut leanh::LeanObject,
    mut v_h_u2081_99_: *mut leanh::LeanObject,
    mut v_h_u2082_100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_101_: u8 = 0;
    let mut v_r_102_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    v_r_102_ = leanh::lean_box((v_res_101_) as usize);
    return v_r_102_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_RawDecidableEquiv(
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
pub unsafe fn initialize_Std_Data_HashMap_RawDecidableEquiv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
}