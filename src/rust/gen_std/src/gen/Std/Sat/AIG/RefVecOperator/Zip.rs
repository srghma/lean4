// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Zip
// Imports: Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_mul, lean_nat_shiftr,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___redArg(
    mut v_len_117_: *mut leanh::LeanObject,
    mut v_aig_118_: *mut leanh::LeanObject,
    mut v_idx_119_: *mut leanh::LeanObject,
    mut v_s_120_: *mut leanh::LeanObject,
    mut v_lhs_121_: *mut leanh::LeanObject,
    mut v_rhs_122_: *mut leanh::LeanObject,
    mut v_f_123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_132_: u8 = 0;
    let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u8 = 0;
    let mut v___y_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: u8 = 0;
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: u8 = 0;
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: u8 = 0;
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: u8 = 0;
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_141_ = lean_nat_dec_lt(v_idx_119_, v_len_117_);
                if v___x_141_ == 0 {
                    leanh::lean_dec_ref(v_f_123_);
                    leanh::lean_dec(v_idx_119_);
                    v___x_153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_153_, 0, v_aig_118_);
                    leanh::lean_ctor_set(v___x_153_, 1, v_s_120_);
                    return v___x_153_;
                } else {
                    v_ref_154_ = lean_array_fget_borrowed(v_lhs_121_, v_idx_119_);
                    v___x_155_ = leanh::lean_unsigned_to_nat(1);
                    v___x_156_ = lean_nat_shiftr(v_ref_154_, v___x_155_);
                    v___x_157_ = lean_nat_land(v___x_155_, v_ref_154_);
                    v___x_158_ = leanh::lean_unsigned_to_nat(0);
                    v___x_159_ = lean_nat_dec_eq(v___x_157_, v___x_158_);
                    leanh::lean_dec(v___x_157_);
                    if v___x_159_ == 0 {
                        v___x_160_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_160_, 0, v___x_156_);
                        leanh::lean_ctor_set_uint8(
                            v___x_160_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_141_,
                        );
                        v___y_143_ = v___x_160_;
                        state = 2;
                        continue;
                    } else {
                        v___x_161_ = 0;
                        v___x_162_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_162_, 0, v___x_156_);
                        leanh::lean_ctor_set_uint8(
                            v___x_162_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_161_,
                        );
                        v___y_143_ = v___x_162_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_127_, 0, v___y_125_);
                leanh::lean_ctor_set(v___x_127_, 1, v___y_126_);
                leanh::lean_inc_ref(v_f_123_);
                v_res_128_ = leanh::lean_apply_2(v_f_123_, v_aig_118_, v___x_127_);
                v_ref_129_ = leanh::lean_ctor_get(v_res_128_, 1);
                leanh::lean_inc_ref(v_ref_129_);
                v_aig_130_ = leanh::lean_ctor_get(v_res_128_, 0);
                leanh::lean_inc_ref(v_aig_130_);
                leanh::lean_dec_ref(v_res_128_);
                v_gate_131_ = leanh::lean_ctor_get(v_ref_129_, 0);
                leanh::lean_inc(v_gate_131_);
                v_invert_132_ = leanh::lean_ctor_get_uint8(
                    v_ref_129_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_ref_129_);
                v___x_133_ = leanh::lean_unsigned_to_nat(1);
                v___x_134_ = lean_nat_add(v_idx_119_, v___x_133_);
                leanh::lean_dec(v_idx_119_);
                v___x_135_ = leanh::lean_unsigned_to_nat(2);
                v___x_136_ = lean_nat_mul(v_gate_131_, v___x_135_);
                leanh::lean_dec(v_gate_131_);
                v___x_137_ = l_Bool_toNat(v_invert_132_);
                v___x_138_ = lean_nat_lor(v___x_136_, v___x_137_);
                leanh::lean_dec(v___x_137_);
                leanh::lean_dec(v___x_136_);
                v_s_139_ = lean_array_push(v_s_120_, v___x_138_);
                v_aig_118_ = v_aig_130_;
                v_idx_119_ = v___x_134_;
                v_s_120_ = v_s_139_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_144_ = lean_array_fget_borrowed(v_rhs_122_, v_idx_119_);
                v___x_145_ = leanh::lean_unsigned_to_nat(1);
                v___x_146_ = lean_nat_shiftr(v_ref_144_, v___x_145_);
                v___x_147_ = lean_nat_land(v___x_145_, v_ref_144_);
                v___x_148_ = leanh::lean_unsigned_to_nat(0);
                v___x_149_ = lean_nat_dec_eq(v___x_147_, v___x_148_);
                leanh::lean_dec(v___x_147_);
                if v___x_149_ == 0 {
                    v___x_150_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_150_, 0, v___x_146_);
                    leanh::lean_ctor_set_uint8(
                        v___x_150_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_141_,
                    );
                    v___y_125_ = v___y_143_;
                    v___y_126_ = v___x_150_;
                    state = 1;
                    continue;
                } else {
                    v___x_151_ = 0;
                    v___x_152_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_152_, 0, v___x_146_);
                    leanh::lean_ctor_set_uint8(
                        v___x_152_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_151_,
                    );
                    v___y_125_ = v___y_143_;
                    v___y_126_ = v___x_152_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___redArg___boxed(
    mut v_len_163_: *mut leanh::LeanObject,
    mut v_aig_164_: *mut leanh::LeanObject,
    mut v_idx_165_: *mut leanh::LeanObject,
    mut v_s_166_: *mut leanh::LeanObject,
    mut v_lhs_167_: *mut leanh::LeanObject,
    mut v_rhs_168_: *mut leanh::LeanObject,
    mut v_f_169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(
        v_len_163_, v_aig_164_, v_idx_165_, v_s_166_, v_lhs_167_, v_rhs_168_, v_f_169_,
    );
    leanh::lean_dec_ref(v_rhs_168_);
    leanh::lean_dec_ref(v_lhs_167_);
    leanh::lean_dec(v_len_163_);
    return v_res_170_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go(
    mut v_00_u03b1_171_: *mut leanh::LeanObject,
    mut v_inst_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_len_174_: *mut leanh::LeanObject,
    mut v_aig_175_: *mut leanh::LeanObject,
    mut v_idx_176_: *mut leanh::LeanObject,
    mut v_s_177_: *mut leanh::LeanObject,
    mut v_hidx_178_: *mut leanh::LeanObject,
    mut v_lhs_179_: *mut leanh::LeanObject,
    mut v_rhs_180_: *mut leanh::LeanObject,
    mut v_f_181_: *mut leanh::LeanObject,
    mut v_inst_182_: *mut leanh::LeanObject,
    mut v_inst_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(
        v_len_174_, v_aig_175_, v_idx_176_, v_s_177_, v_lhs_179_, v_rhs_180_, v_f_181_,
    );
    return v___x_184_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip_go___boxed(
    mut v_00_u03b1_185_: *mut leanh::LeanObject,
    mut v_inst_186_: *mut leanh::LeanObject,
    mut v_inst_187_: *mut leanh::LeanObject,
    mut v_len_188_: *mut leanh::LeanObject,
    mut v_aig_189_: *mut leanh::LeanObject,
    mut v_idx_190_: *mut leanh::LeanObject,
    mut v_s_191_: *mut leanh::LeanObject,
    mut v_hidx_192_: *mut leanh::LeanObject,
    mut v_lhs_193_: *mut leanh::LeanObject,
    mut v_rhs_194_: *mut leanh::LeanObject,
    mut v_f_195_: *mut leanh::LeanObject,
    mut v_inst_196_: *mut leanh::LeanObject,
    mut v_inst_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_198_ = l_Std_Sat_AIG_RefVec_zip_go(
        v_00_u03b1_185_,
        v_inst_186_,
        v_inst_187_,
        v_len_188_,
        v_aig_189_,
        v_idx_190_,
        v_s_191_,
        v_hidx_192_,
        v_lhs_193_,
        v_rhs_194_,
        v_f_195_,
        v_inst_196_,
        v_inst_197_,
    );
    leanh::lean_dec_ref(v_rhs_194_);
    leanh::lean_dec_ref(v_lhs_193_);
    leanh::lean_dec(v_len_188_);
    leanh::lean_dec_ref(v_inst_187_);
    leanh::lean_dec_ref(v_inst_186_);
    return v_res_198_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___redArg(
    mut v_len_199_: *mut leanh::LeanObject,
    mut v_aig_200_: *mut leanh::LeanObject,
    mut v_input_201_: *mut leanh::LeanObject,
    mut v_func_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_203_ = leanh::lean_ctor_get(v_input_201_, 0);
    v_rhs_204_ = leanh::lean_ctor_get(v_input_201_, 1);
    v___x_205_ = leanh::lean_unsigned_to_nat(0);
    v___x_206_ = lean_mk_empty_array_with_capacity(v_len_199_);
    v___x_207_ = l_Std_Sat_AIG_RefVec_zip_go___redArg(
        v_len_199_,
        v_aig_200_,
        v___x_205_,
        v___x_206_,
        v_lhs_203_,
        v_rhs_204_,
        v_func_202_,
    );
    return v___x_207_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___redArg___boxed(
    mut v_len_208_: *mut leanh::LeanObject,
    mut v_aig_209_: *mut leanh::LeanObject,
    mut v_input_210_: *mut leanh::LeanObject,
    mut v_func_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_212_ =
        l_Std_Sat_AIG_RefVec_zip___redArg(v_len_208_, v_aig_209_, v_input_210_, v_func_211_);
    leanh::lean_dec_ref(v_input_210_);
    leanh::lean_dec(v_len_208_);
    return v_res_212_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip(
    mut v_00_u03b1_213_: *mut leanh::LeanObject,
    mut v_inst_214_: *mut leanh::LeanObject,
    mut v_inst_215_: *mut leanh::LeanObject,
    mut v_len_216_: *mut leanh::LeanObject,
    mut v_aig_217_: *mut leanh::LeanObject,
    mut v_input_218_: *mut leanh::LeanObject,
    mut v_func_219_: *mut leanh::LeanObject,
    mut v_inst_220_: *mut leanh::LeanObject,
    mut v_inst_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ =
        l_Std_Sat_AIG_RefVec_zip___redArg(v_len_216_, v_aig_217_, v_input_218_, v_func_219_);
    return v___x_222_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_zip___boxed(
    mut v_00_u03b1_223_: *mut leanh::LeanObject,
    mut v_inst_224_: *mut leanh::LeanObject,
    mut v_inst_225_: *mut leanh::LeanObject,
    mut v_len_226_: *mut leanh::LeanObject,
    mut v_aig_227_: *mut leanh::LeanObject,
    mut v_input_228_: *mut leanh::LeanObject,
    mut v_func_229_: *mut leanh::LeanObject,
    mut v_inst_230_: *mut leanh::LeanObject,
    mut v_inst_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_232_ = l_Std_Sat_AIG_RefVec_zip(
        v_00_u03b1_223_,
        v_inst_224_,
        v_inst_225_,
        v_len_226_,
        v_aig_227_,
        v_input_228_,
        v_func_229_,
        v_inst_230_,
        v_inst_231_,
    );
    leanh::lean_dec_ref(v_input_228_);
    leanh::lean_dec(v_len_226_);
    leanh::lean_dec_ref(v_inst_225_);
    leanh::lean_dec_ref(v_inst_224_);
    return v_res_232_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_RefVecOperator_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_RefVecOperator_Zip(
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
pub unsafe fn initialize_Std_Sat_AIG_RefVecOperator_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RefVecOperator_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_RefVecOperator_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_RefVecOperator_Zip(builtin);
}