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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Int_add__of__le___redArg(
    mut v_a_80_: *mut LeanObject,
    mut v_b_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
    v___x_82_ = lean_int_sub(v_b_81_, v_a_80_);
    v___x_83_ = l_Int_toNat(v___x_82_);
    lean_dec(v___x_82_);
    return v___x_83_;
}
pub unsafe fn l_Int_add__of__le___redArg___boxed(
    mut v_a_84_: *mut LeanObject,
    mut v_b_85_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_86_: *mut LeanObject = core::ptr::null_mut();
    v_res_86_ = l_Int_add__of__le___redArg(v_a_84_, v_b_85_);
    lean_dec(v_b_85_);
    lean_dec(v_a_84_);
    return v_res_86_;
}
pub unsafe fn l_Int_add__of__le(
    mut v_a_87_: *mut LeanObject,
    mut v_b_88_: *mut LeanObject,
    mut v_h_89_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
    v___x_90_ = l_Int_add__of__le___redArg(v_a_87_, v_b_88_);
    return v___x_90_;
}
pub unsafe fn l_Int_add__of__le___boxed(
    mut v_a_91_: *mut LeanObject,
    mut v_b_92_: *mut LeanObject,
    mut v_h_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Int_add__of__le(v_a_91_, v_b_92_, v_h_93_);
    lean_dec(v_b_92_);
    lean_dec(v_a_91_);
    return v_res_94_;
}
pub unsafe fn l_Nat_cast___at___00Int_Cooper_resolve__left_spec__0(
    mut v_a_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    v___x_96_ = lean_nat_to_int(v_a_95_);
    return v___x_96_;
}
pub unsafe fn l_Int_Cooper_resolve__left(
    mut v_a_97_: *mut LeanObject,
    mut v_c_98_: *mut LeanObject,
    mut v_d_99_: *mut LeanObject,
    mut v_p_100_: *mut LeanObject,
    mut v_x_101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    v___x_102_ = lean_int_mul(v_a_97_, v_x_101_);
    v___x_103_ = lean_int_sub(v___x_102_, v_p_100_);
    lean_dec(v___x_102_);
    v___x_104_ = lean_int_mul(v_a_97_, v_d_99_);
    v___x_105_ = l_Int_gcd(v___x_104_, v_c_98_);
    v___x_106_ = lean_nat_to_int(v___x_105_);
    v___x_107_ = lean_int_ediv(v___x_104_, v___x_106_);
    lean_dec(v___x_106_);
    lean_dec(v___x_104_);
    v___x_108_ = l_Int_lcm(v_a_97_, v___x_107_);
    lean_dec(v___x_107_);
    v___x_109_ = lean_nat_to_int(v___x_108_);
    v___x_110_ = lean_int_emod(v___x_103_, v___x_109_);
    lean_dec(v___x_109_);
    lean_dec(v___x_103_);
    return v___x_110_;
}
pub unsafe fn l_Int_Cooper_resolve__left___boxed(
    mut v_a_111_: *mut LeanObject,
    mut v_c_112_: *mut LeanObject,
    mut v_d_113_: *mut LeanObject,
    mut v_p_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_116_: *mut LeanObject = core::ptr::null_mut();
    v_res_116_ = l_Int_Cooper_resolve__left(v_a_111_, v_c_112_, v_d_113_, v_p_114_, v_x_115_);
    lean_dec(v_x_115_);
    lean_dec(v_p_114_);
    lean_dec(v_d_113_);
    lean_dec(v_c_112_);
    lean_dec(v_a_111_);
    return v_res_116_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27___redArg(
    mut v_a_117_: *mut LeanObject,
    mut v_c_118_: *mut LeanObject,
    mut v_d_119_: *mut LeanObject,
    mut v_p_120_: *mut LeanObject,
    mut v_x_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    v___x_122_ = lean_int_mul(v_a_117_, v_x_121_);
    v___x_123_ = l_Int_add__of__le___redArg(v_p_120_, v___x_122_);
    lean_dec(v___x_122_);
    v___x_124_ = lean_int_mul(v_a_117_, v_d_119_);
    v___x_125_ = l_Int_gcd(v___x_124_, v_c_118_);
    v___x_126_ = lean_nat_to_int(v___x_125_);
    v___x_127_ = lean_int_ediv(v___x_124_, v___x_126_);
    lean_dec(v___x_126_);
    lean_dec(v___x_124_);
    v___x_128_ = l_Int_lcm(v_a_117_, v___x_127_);
    lean_dec(v___x_127_);
    v___x_129_ = lean_nat_mod(v___x_123_, v___x_128_);
    lean_dec(v___x_128_);
    lean_dec(v___x_123_);
    return v___x_129_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27___redArg___boxed(
    mut v_a_130_: *mut LeanObject,
    mut v_c_131_: *mut LeanObject,
    mut v_d_132_: *mut LeanObject,
    mut v_p_133_: *mut LeanObject,
    mut v_x_134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_135_: *mut LeanObject = core::ptr::null_mut();
    v_res_135_ =
        l_Int_Cooper_resolve__left_x27___redArg(v_a_130_, v_c_131_, v_d_132_, v_p_133_, v_x_134_);
    lean_dec(v_x_134_);
    lean_dec(v_p_133_);
    lean_dec(v_d_132_);
    lean_dec(v_c_131_);
    lean_dec(v_a_130_);
    return v_res_135_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27(
    mut v_a_136_: *mut LeanObject,
    mut v_c_137_: *mut LeanObject,
    mut v_d_138_: *mut LeanObject,
    mut v_p_139_: *mut LeanObject,
    mut v_x_140_: *mut LeanObject,
    mut v_h_u2081_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    v___x_142_ =
        l_Int_Cooper_resolve__left_x27___redArg(v_a_136_, v_c_137_, v_d_138_, v_p_139_, v_x_140_);
    return v___x_142_;
}
pub unsafe fn l_Int_Cooper_resolve__left_x27___boxed(
    mut v_a_143_: *mut LeanObject,
    mut v_c_144_: *mut LeanObject,
    mut v_d_145_: *mut LeanObject,
    mut v_p_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_h_u2081_148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_149_: *mut LeanObject = core::ptr::null_mut();
    v_res_149_ = l_Int_Cooper_resolve__left_x27(
        v_a_143_,
        v_c_144_,
        v_d_145_,
        v_p_146_,
        v_x_147_,
        v_h_u2081_148_,
    );
    lean_dec(v_x_147_);
    lean_dec(v_p_146_);
    lean_dec(v_d_145_);
    lean_dec(v_c_144_);
    lean_dec(v_a_143_);
    return v_res_149_;
}
pub unsafe fn l_Int_Cooper_resolve__left__inv(
    mut v_a_150_: *mut LeanObject,
    mut v_p_151_: *mut LeanObject,
    mut v_k_152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    v___x_153_ = lean_int_add(v_k_152_, v_p_151_);
    v___x_154_ = lean_int_ediv(v___x_153_, v_a_150_);
    lean_dec(v___x_153_);
    return v___x_154_;
}
pub unsafe fn l_Int_Cooper_resolve__left__inv___boxed(
    mut v_a_155_: *mut LeanObject,
    mut v_p_156_: *mut LeanObject,
    mut v_k_157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_158_: *mut LeanObject = core::ptr::null_mut();
    v_res_158_ = l_Int_Cooper_resolve__left__inv(v_a_155_, v_p_156_, v_k_157_);
    lean_dec(v_k_157_);
    lean_dec(v_p_156_);
    lean_dec(v_a_155_);
    return v_res_158_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Cooper(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Cooper(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Cooper(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Cooper(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Cooper(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Int_Cooper(builtin);
}
