// Lean compiler output
// Module: Init.Omega.Coeffs
// Imports: Init.Omega.IntList Init.Omega.IntList
use crate::ffi::lean_int_sub;
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_bmod;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_findIdx_x3f_go___redArg, l_List_mapTR_loop___redArg,
};
use crate::r#gen::Init::Omega::IntList::{
    initialize_Init_Omega_IntList, l_Lean_Omega_IntList_dot, l_Lean_Omega_IntList_gcd,
    l_Lean_Omega_IntList_get, l_Lean_Omega_IntList_leading, l_Lean_Omega_IntList_neg,
    l_Lean_Omega_IntList_sdiv, l_Lean_Omega_IntList_set, l_Lean_Omega_IntList_smul,
    l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0,
    l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0,
    l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0,
    runtime_initialize_Init_Omega_IntList,
};
use crate::r#gen::Init::Prelude::l_List_lengthTR___redArg;
pub unsafe fn l_Lean_Omega_Coeffs_toList(
    mut v_xs_98_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_xs_98_);
    return v_xs_98_;
}
pub unsafe fn l_Lean_Omega_Coeffs_toList___boxed(
    mut v_xs_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_100_ = l_Lean_Omega_Coeffs_toList(v_xs_99_);
    leanh::lean_dec(v_xs_99_);
    return v_res_100_;
}
pub unsafe fn l_Lean_Omega_Coeffs_ofList(
    mut v_xs_101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_xs_101_);
    return v_xs_101_;
}
pub unsafe fn l_Lean_Omega_Coeffs_ofList___boxed(
    mut v_xs_102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_103_ = l_Lean_Omega_Coeffs_ofList(v_xs_102_);
    leanh::lean_dec(v_xs_102_);
    return v_res_103_;
}
pub unsafe fn l_Lean_Omega_Coeffs_set(
    mut v_xs_104_: *mut leanh::LeanObject,
    mut v_i_105_: *mut leanh::LeanObject,
    mut v_y_106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_107_ = l_Lean_Omega_IntList_set(v_xs_104_, v_i_105_, v_y_106_);
    return v___x_107_;
}
pub unsafe fn l_Lean_Omega_Coeffs_set___boxed(
    mut v_xs_108_: *mut leanh::LeanObject,
    mut v_i_109_: *mut leanh::LeanObject,
    mut v_y_110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_111_ = l_Lean_Omega_Coeffs_set(v_xs_108_, v_i_109_, v_y_110_);
    leanh::lean_dec(v_i_109_);
    return v_res_111_;
}
pub unsafe fn l_Lean_Omega_Coeffs_get(
    mut v_xs_112_: *mut leanh::LeanObject,
    mut v_i_113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_114_ = l_Lean_Omega_IntList_get(v_xs_112_, v_i_113_);
    return v___x_114_;
}
pub unsafe fn l_Lean_Omega_Coeffs_get___boxed(
    mut v_xs_115_: *mut leanh::LeanObject,
    mut v_i_116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_117_ = l_Lean_Omega_Coeffs_get(v_xs_115_, v_i_116_);
    leanh::lean_dec(v_xs_115_);
    return v_res_117_;
}
pub unsafe fn l_Lean_Omega_Coeffs_gcd(
    mut v_xs_118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_119_ = l_Lean_Omega_IntList_gcd(v_xs_118_);
    return v___x_119_;
}
pub unsafe fn l_Lean_Omega_Coeffs_gcd___boxed(
    mut v_xs_120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_121_ = l_Lean_Omega_Coeffs_gcd(v_xs_120_);
    leanh::lean_dec(v_xs_120_);
    return v_res_121_;
}
pub unsafe fn l_Lean_Omega_Coeffs_smul(
    mut v_xs_122_: *mut leanh::LeanObject,
    mut v_g_123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = l_Lean_Omega_IntList_smul(v_xs_122_, v_g_123_);
    return v___x_124_;
}
pub unsafe fn l_Lean_Omega_Coeffs_smul___boxed(
    mut v_xs_125_: *mut leanh::LeanObject,
    mut v_g_126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_127_ = l_Lean_Omega_Coeffs_smul(v_xs_125_, v_g_126_);
    leanh::lean_dec(v_g_126_);
    return v_res_127_;
}
pub unsafe fn l_Lean_Omega_Coeffs_sdiv(
    mut v_xs_128_: *mut leanh::LeanObject,
    mut v_g_129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Lean_Omega_IntList_sdiv(v_xs_128_, v_g_129_);
    return v___x_130_;
}
pub unsafe fn l_Lean_Omega_Coeffs_sdiv___boxed(
    mut v_xs_131_: *mut leanh::LeanObject,
    mut v_g_132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = l_Lean_Omega_Coeffs_sdiv(v_xs_131_, v_g_132_);
    leanh::lean_dec(v_g_132_);
    return v_res_133_;
}
pub unsafe fn l_Lean_Omega_Coeffs_dot(
    mut v_xs_134_: *mut leanh::LeanObject,
    mut v_ys_135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_136_ = l_Lean_Omega_IntList_dot(v_xs_134_, v_ys_135_);
    return v___x_136_;
}
pub unsafe fn l_Lean_Omega_Coeffs_dot___boxed(
    mut v_xs_137_: *mut leanh::LeanObject,
    mut v_ys_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_139_ = l_Lean_Omega_Coeffs_dot(v_xs_137_, v_ys_138_);
    leanh::lean_dec(v_xs_137_);
    return v_res_139_;
}
pub unsafe fn l_Lean_Omega_Coeffs_add(
    mut v_xs_140_: *mut leanh::LeanObject,
    mut v_ys_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_140_, v_ys_141_);
    return v___x_142_;
}
pub unsafe fn l_Lean_Omega_Coeffs_sub(
    mut v_xs_143_: *mut leanh::LeanObject,
    mut v_ys_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_143_, v_ys_144_);
    return v___x_145_;
}
pub unsafe fn l_Lean_Omega_Coeffs_neg(
    mut v_xs_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_147_ = l_Lean_Omega_IntList_neg(v_xs_146_);
    return v___x_147_;
}
pub unsafe fn l_Lean_Omega_Coeffs_combo(
    mut v_a_148_: *mut leanh::LeanObject,
    mut v_xs_149_: *mut leanh::LeanObject,
    mut v_b_150_: *mut leanh::LeanObject,
    mut v_ys_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(
        v_a_148_, v_b_150_, v_xs_149_, v_ys_151_,
    );
    return v___x_152_;
}
pub unsafe fn l_Lean_Omega_Coeffs_combo___boxed(
    mut v_a_153_: *mut leanh::LeanObject,
    mut v_xs_154_: *mut leanh::LeanObject,
    mut v_b_155_: *mut leanh::LeanObject,
    mut v_ys_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_157_ = l_Lean_Omega_Coeffs_combo(v_a_153_, v_xs_154_, v_b_155_, v_ys_156_);
    leanh::lean_dec(v_b_155_);
    leanh::lean_dec(v_a_153_);
    return v_res_157_;
}
pub unsafe fn l_Lean_Omega_Coeffs_length(
    mut v_xs_158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_159_ = l_List_lengthTR___redArg(v_xs_158_);
    return v___x_159_;
}
pub unsafe fn l_Lean_Omega_Coeffs_length___boxed(
    mut v_xs_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_161_ = l_Lean_Omega_Coeffs_length(v_xs_160_);
    leanh::lean_dec(v_xs_160_);
    return v_res_161_;
}
pub unsafe fn l_Lean_Omega_Coeffs_leading(
    mut v_xs_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_163_ = l_Lean_Omega_IntList_leading(v_xs_162_);
    return v___x_163_;
}
pub unsafe fn l_Lean_Omega_Coeffs_leading___boxed(
    mut v_xs_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_165_ = l_Lean_Omega_Coeffs_leading(v_xs_164_);
    leanh::lean_dec(v_xs_164_);
    return v_res_165_;
}
pub unsafe fn l_Lean_Omega_Coeffs_map(
    mut v_f_166_: *mut leanh::LeanObject,
    mut v_xs_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = leanh::lean_box(0);
    v___x_169_ = l_List_mapTR_loop___redArg(v_f_166_, v_xs_167_, v___x_168_);
    return v___x_169_;
}
pub unsafe fn l_Lean_Omega_Coeffs_findIdx_x3f(
    mut v_f_170_: *mut leanh::LeanObject,
    mut v_xs_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_172_ = leanh::lean_unsigned_to_nat(0);
    v___x_173_ = l_List_findIdx_x3f_go___redArg(v_f_170_, v_xs_171_, v___x_172_);
    return v___x_173_;
}
pub unsafe fn l_Lean_Omega_Coeffs_bmod___lam__0(
    mut v_m_174_: *mut leanh::LeanObject,
    mut v_x_175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_176_ = l_Int_bmod(v_x_175_, v_m_174_);
    return v___x_176_;
}
pub unsafe fn l_Lean_Omega_Coeffs_bmod___lam__0___boxed(
    mut v_m_177_: *mut leanh::LeanObject,
    mut v_x_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_179_ = l_Lean_Omega_Coeffs_bmod___lam__0(v_m_177_, v_x_178_);
    leanh::lean_dec(v_x_178_);
    return v_res_179_;
}
pub unsafe fn l_Lean_Omega_Coeffs_bmod(
    mut v_x_180_: *mut leanh::LeanObject,
    mut v_m_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_182_ = leanh::lean_alloc_closure(
        l_Lean_Omega_Coeffs_bmod___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_182_, 0, v_m_181_);
    v___x_183_ = leanh::lean_box(0);
    v___x_184_ = l_List_mapTR_loop___redArg(v___f_182_, v_x_180_, v___x_183_);
    return v___x_184_;
}
pub unsafe fn l_Lean_Omega_Coeffs_bmod__dot__sub__dot__bmod(
    mut v_m_185_: *mut leanh::LeanObject,
    mut v_a_186_: *mut leanh::LeanObject,
    mut v_b_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_m_185_);
    v___f_188_ = leanh::lean_alloc_closure(
        l_Lean_Omega_Coeffs_bmod___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_188_, 0, v_m_185_);
    leanh::lean_inc(v_b_187_);
    v___x_189_ = l_Lean_Omega_IntList_dot(v_a_186_, v_b_187_);
    v___x_190_ = l_Int_bmod(v___x_189_, v_m_185_);
    leanh::lean_dec(v___x_189_);
    v___x_191_ = leanh::lean_box(0);
    v___x_192_ = l_List_mapTR_loop___redArg(v___f_188_, v_a_186_, v___x_191_);
    v___x_193_ = l_Lean_Omega_IntList_dot(v___x_192_, v_b_187_);
    leanh::lean_dec(v___x_192_);
    v___x_194_ = lean_int_sub(v___x_190_, v___x_193_);
    leanh::lean_dec(v___x_193_);
    leanh::lean_dec(v___x_190_);
    return v___x_194_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Omega_Coeffs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Omega_IntList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega_IntList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Omega_Coeffs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Omega_Coeffs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Omega_IntList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega_IntList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega_Coeffs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Omega_Coeffs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Omega_Coeffs(builtin);
}