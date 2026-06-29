// Lean compiler output
// Module: Init.Data.Int.Cooper
// Imports: Init.Data.Int.Gcd Init.Data.Int.DivMod.Lemmas Init.Omega Init.RCases
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Gcd::{
    initialize_Init_Data_Int_Gcd, l_Int_gcd, l_Int_lcm, runtime_initialize_Init_Data_Int_Gcd,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_mul, lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Prelude::lean_nat_mod;
pub unsafe fn l_Int_add__of__le___redArg(
    mut v_a_80_: *mut crate::leanh::LeanObject,
    mut v_b_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = lean_int_sub(v_b_81_, v_a_80_);
    v___x_83_ = l_Int_toNat(v___x_82_);
    crate::leanh::lean_dec(v___x_82_);
    return v___x_83_;
}
pub unsafe fn l_Int_add__of__le___redArg___boxed(
    mut v_a_84_: *mut crate::leanh::LeanObject,
    mut v_b_85_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_86_ = l_Int_add__of__le___redArg(v_a_84_, v_b_85_);
    crate::leanh::lean_dec(v_b_85_);
    crate::leanh::lean_dec(v_a_84_);
    return v_res_86_;
}
pub unsafe fn l_Int_add__of__le(
    mut v_a_87_: *mut crate::leanh::LeanObject,
    mut v_b_88_: *mut crate::leanh::LeanObject,
    mut v_h_89_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_90_ = l_Int_add__of__le___redArg(v_a_87_, v_b_88_);
    return v___x_90_;
}
pub unsafe fn l_Int_add__of__le___boxed(
    mut v_a_91_: *mut crate::leanh::LeanObject,
    mut v_b_92_: *mut crate::leanh::LeanObject,
    mut v_h_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Int_add__of__le(v_a_91_, v_b_92_, v_h_93_);
    crate::leanh::lean_dec(v_b_92_);
    crate::leanh::lean_dec(v_a_91_);
    return v_res_94_;
}
pub unsafe fn l_Nat_cast___at___00Int_Cooper_resolve__left_spec__0(
    mut v_a_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = lean_nat_to_int(v_a_95_);
    return v___x_96_;
}
pub unsafe fn l_Int_Cooper_resolve__left(
    mut v_a_97_: *mut crate::leanh::LeanObject,
    mut v_c_98_: *mut crate::leanh::LeanObject,
    mut v_d_99_: *mut crate::leanh::LeanObject,
    mut v_p_100_: *mut crate::leanh::LeanObject,
    mut v_x_101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_102_ = lean_int_mul(v_a_97_, v_x_101_);
    v___x_103_ = lean_int_sub(v___x_102_, v_p_100_);
    crate::leanh::lean_dec(v___x_102_);
    v___x_104_ = lean_int_mul(v_a_97_, v_d_99_);
    v___x_105_ = l_Int_gcd(v___x_104_, v_c_98_);
    v___x_106_ = lean_nat_to_int(v___x_105_);
    v___x_107_ = lean_int_ediv(v___x_104_, v___x_106_);
    crate::leanh::lean_dec(v___x_106_);
    crate::leanh::lean_dec(v___x_104_);
    v___x_108_ = l_Int_lcm(v_a_97_, v___x_107_);
    crate::leanh::lean_dec(v___x_107_);
    v___x_109_ = lean_nat_to_int(v___x_108_);
    v___x_110_ = lean_int_emod(v___x_103_, v___x_109_);
    crate::leanh::lean_dec(v___x_109_);
    crate::leanh::lean_dec(v___x_103_);
    return v___x_110_;
}
pub unsafe fn l_Int_Cooper_resolve__left___boxed(
    mut v_a_111_: *mut crate::leanh::LeanObject,
    mut v_c_112_: *mut crate::leanh::LeanObject,
    mut v_d_113_: *mut crate::leanh::LeanObject,
    mut v_p_114_: *mut crate::leanh::LeanObject,
    mut v_x_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ = l_Int_Cooper_resolve__left(v_a_111_, v_c_112_, v_d_113_, v_p_114_, v_x_115_);
    crate::leanh::lean_dec(v_x_115_);
    crate::leanh::lean_dec(v_p_114_);
    crate::leanh::lean_dec(v_d_113_);
    crate::leanh::lean_dec(v_c_112_);
    crate::leanh::lean_dec(v_a_111_);
    return v_res_116_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27___redArg(
    mut v_a_117_: *mut crate::leanh::LeanObject,
    mut v_c_118_: *mut crate::leanh::LeanObject,
    mut v_d_119_: *mut crate::leanh::LeanObject,
    mut v_p_120_: *mut crate::leanh::LeanObject,
    mut v_x_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = lean_int_mul(v_a_117_, v_x_121_);
    v___x_123_ = l_Int_add__of__le___redArg(v_p_120_, v___x_122_);
    crate::leanh::lean_dec(v___x_122_);
    v___x_124_ = lean_int_mul(v_a_117_, v_d_119_);
    v___x_125_ = l_Int_gcd(v___x_124_, v_c_118_);
    v___x_126_ = lean_nat_to_int(v___x_125_);
    v___x_127_ = lean_int_ediv(v___x_124_, v___x_126_);
    crate::leanh::lean_dec(v___x_126_);
    crate::leanh::lean_dec(v___x_124_);
    v___x_128_ = l_Int_lcm(v_a_117_, v___x_127_);
    crate::leanh::lean_dec(v___x_127_);
    v___x_129_ = lean_nat_mod(v___x_123_, v___x_128_);
    crate::leanh::lean_dec(v___x_128_);
    crate::leanh::lean_dec(v___x_123_);
    return v___x_129_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27___redArg___boxed(
    mut v_a_130_: *mut crate::leanh::LeanObject,
    mut v_c_131_: *mut crate::leanh::LeanObject,
    mut v_d_132_: *mut crate::leanh::LeanObject,
    mut v_p_133_: *mut crate::leanh::LeanObject,
    mut v_x_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_135_ =
        l_Int_Cooper_resolve__left_x27___redArg(v_a_130_, v_c_131_, v_d_132_, v_p_133_, v_x_134_);
    crate::leanh::lean_dec(v_x_134_);
    crate::leanh::lean_dec(v_p_133_);
    crate::leanh::lean_dec(v_d_132_);
    crate::leanh::lean_dec(v_c_131_);
    crate::leanh::lean_dec(v_a_130_);
    return v_res_135_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27(
    mut v_a_136_: *mut crate::leanh::LeanObject,
    mut v_c_137_: *mut crate::leanh::LeanObject,
    mut v_d_138_: *mut crate::leanh::LeanObject,
    mut v_p_139_: *mut crate::leanh::LeanObject,
    mut v_x_140_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ =
        l_Int_Cooper_resolve__left_x27___redArg(v_a_136_, v_c_137_, v_d_138_, v_p_139_, v_x_140_);
    return v___x_142_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27___boxed(
    mut v_a_143_: *mut crate::leanh::LeanObject,
    mut v_c_144_: *mut crate::leanh::LeanObject,
    mut v_d_145_: *mut crate::leanh::LeanObject,
    mut v_p_146_: *mut crate::leanh::LeanObject,
    mut v_x_147_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_149_ = l_Int_Cooper_resolve__left_x27(
        v_a_143_,
        v_c_144_,
        v_d_145_,
        v_p_146_,
        v_x_147_,
        v_h_u2081_148_,
    );
    crate::leanh::lean_dec(v_x_147_);
    crate::leanh::lean_dec(v_p_146_);
    crate::leanh::lean_dec(v_d_145_);
    crate::leanh::lean_dec(v_c_144_);
    crate::leanh::lean_dec(v_a_143_);
    return v_res_149_;
}
pub unsafe fn l_Int_Cooper_resolve__left__inv(
    mut v_a_150_: *mut crate::leanh::LeanObject,
    mut v_p_151_: *mut crate::leanh::LeanObject,
    mut v_k_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_153_ = lean_int_add(v_k_152_, v_p_151_);
    v___x_154_ = lean_int_ediv(v___x_153_, v_a_150_);
    crate::leanh::lean_dec(v___x_153_);
    return v___x_154_;
}
pub unsafe fn l_Int_Cooper_resolve__left__inv___boxed(
    mut v_a_155_: *mut crate::leanh::LeanObject,
    mut v_p_156_: *mut crate::leanh::LeanObject,
    mut v_k_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_158_ = l_Int_Cooper_resolve__left__inv(v_a_155_, v_p_156_, v_k_157_);
    crate::leanh::lean_dec(v_k_157_);
    crate::leanh::lean_dec(v_p_156_);
    crate::leanh::lean_dec(v_a_155_);
    return v_res_158_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Cooper(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Cooper(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Cooper(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Cooper(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Cooper(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_Cooper(builtin);
}
