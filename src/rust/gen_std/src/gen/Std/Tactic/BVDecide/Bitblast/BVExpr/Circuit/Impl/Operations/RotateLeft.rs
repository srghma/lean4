// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_mod, lean_nat_mul,
    lean_nat_shiftr, lean_nat_sub,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(
    mut v_w_108_: *mut leanh::LeanObject,
    mut v_input_109_: *mut leanh::LeanObject,
    mut v_distance_110_: *mut leanh::LeanObject,
    mut v_curr_111_: *mut leanh::LeanObject,
    mut v_s_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_115_: u8 = 0;
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_126_: u8 = 0;
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: u8 = 0;
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: u8 = 0;
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: u8 = 0;
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: u8 = 0;
    let mut v___x_153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_135_ = lean_nat_dec_lt(v_curr_111_, v_w_108_);
                if v___x_135_ == 0 {
                    leanh::lean_dec(v_curr_111_);
                    return v_s_112_;
                } else {
                    v___x_136_ = lean_nat_mod(v_distance_110_, v_w_108_);
                    v___x_137_ = lean_nat_dec_lt(v_curr_111_, v___x_136_);
                    if v___x_137_ == 0 {
                        v___x_138_ = lean_nat_sub(v_curr_111_, v___x_136_);
                        leanh::lean_dec(v___x_136_);
                        v_ref_139_ = lean_array_fget_borrowed(v_input_109_, v___x_138_);
                        leanh::lean_dec(v___x_138_);
                        v___x_140_ = leanh::lean_unsigned_to_nat(1);
                        v___x_141_ = lean_nat_shiftr(v_ref_139_, v___x_140_);
                        v___x_142_ = lean_nat_land(v___x_140_, v_ref_139_);
                        v___x_143_ = leanh::lean_unsigned_to_nat(0);
                        v___x_144_ = lean_nat_dec_eq(v___x_142_, v___x_143_);
                        leanh::lean_dec(v___x_142_);
                        if v___x_144_ == 0 {
                            v_gate_114_ = v___x_141_;
                            v_invert_115_ = v___x_135_;
                            state = 1;
                            continue;
                        } else {
                            v_gate_114_ = v___x_141_;
                            v_invert_115_ = v___x_137_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_145_ = lean_nat_sub(v_w_108_, v___x_136_);
                        leanh::lean_dec(v___x_136_);
                        v___x_146_ = lean_nat_add(v___x_145_, v_curr_111_);
                        leanh::lean_dec(v___x_145_);
                        v_ref_147_ = lean_array_fget_borrowed(v_input_109_, v___x_146_);
                        leanh::lean_dec(v___x_146_);
                        v___x_148_ = leanh::lean_unsigned_to_nat(1);
                        v___x_149_ = lean_nat_shiftr(v_ref_147_, v___x_148_);
                        v___x_150_ = lean_nat_land(v___x_148_, v_ref_147_);
                        v___x_151_ = leanh::lean_unsigned_to_nat(0);
                        v___x_152_ = lean_nat_dec_eq(v___x_150_, v___x_151_);
                        leanh::lean_dec(v___x_150_);
                        if v___x_152_ == 0 {
                            v_gate_125_ = v___x_149_;
                            v_invert_126_ = v___x_137_;
                            state = 2;
                            continue;
                        } else {
                            v___x_153_ = 0;
                            v_gate_125_ = v___x_149_;
                            v_invert_126_ = v___x_153_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_116_ = leanh::lean_unsigned_to_nat(1);
                v___x_117_ = lean_nat_add(v_curr_111_, v___x_116_);
                leanh::lean_dec(v_curr_111_);
                v___x_118_ = leanh::lean_unsigned_to_nat(2);
                v___x_119_ = lean_nat_mul(v_gate_114_, v___x_118_);
                leanh::lean_dec(v_gate_114_);
                v___x_120_ = l_Bool_toNat(v_invert_115_);
                v___x_121_ = lean_nat_lor(v___x_119_, v___x_120_);
                leanh::lean_dec(v___x_120_);
                leanh::lean_dec(v___x_119_);
                v_s_122_ = lean_array_push(v_s_112_, v___x_121_);
                v_curr_111_ = v___x_117_;
                v_s_112_ = v_s_122_;
                state = 0;
                continue;
            }
            2 => {
                v___x_127_ = leanh::lean_unsigned_to_nat(1);
                v___x_128_ = lean_nat_add(v_curr_111_, v___x_127_);
                leanh::lean_dec(v_curr_111_);
                v___x_129_ = leanh::lean_unsigned_to_nat(2);
                v___x_130_ = lean_nat_mul(v_gate_125_, v___x_129_);
                leanh::lean_dec(v_gate_125_);
                v___x_131_ = l_Bool_toNat(v_invert_126_);
                v___x_132_ = lean_nat_lor(v___x_130_, v___x_131_);
                leanh::lean_dec(v___x_131_);
                leanh::lean_dec(v___x_130_);
                v_s_133_ = lean_array_push(v_s_112_, v___x_132_);
                v_curr_111_ = v___x_128_;
                v_s_112_ = v_s_133_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg___boxed(
    mut v_w_154_: *mut leanh::LeanObject,
    mut v_input_155_: *mut leanh::LeanObject,
    mut v_distance_156_: *mut leanh::LeanObject,
    mut v_curr_157_: *mut leanh::LeanObject,
    mut v_s_158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_159_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(
        v_w_154_,
        v_input_155_,
        v_distance_156_,
        v_curr_157_,
        v_s_158_,
    );
    leanh::lean_dec(v_distance_156_);
    leanh::lean_dec_ref(v_input_155_);
    leanh::lean_dec(v_w_154_);
    return v_res_159_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(
    mut v_00_u03b1_160_: *mut leanh::LeanObject,
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_inst_162_: *mut leanh::LeanObject,
    mut v_w_163_: *mut leanh::LeanObject,
    mut v_aig_164_: *mut leanh::LeanObject,
    mut v_input_165_: *mut leanh::LeanObject,
    mut v_distance_166_: *mut leanh::LeanObject,
    mut v_curr_167_: *mut leanh::LeanObject,
    mut v_hcurr_168_: *mut leanh::LeanObject,
    mut v_s_169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_170_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(
        v_w_163_,
        v_input_165_,
        v_distance_166_,
        v_curr_167_,
        v_s_169_,
    );
    return v___x_170_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___boxed(
    mut v_00_u03b1_171_: *mut leanh::LeanObject,
    mut v_inst_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_w_174_: *mut leanh::LeanObject,
    mut v_aig_175_: *mut leanh::LeanObject,
    mut v_input_176_: *mut leanh::LeanObject,
    mut v_distance_177_: *mut leanh::LeanObject,
    mut v_curr_178_: *mut leanh::LeanObject,
    mut v_hcurr_179_: *mut leanh::LeanObject,
    mut v_s_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go(
        v_00_u03b1_171_,
        v_inst_172_,
        v_inst_173_,
        v_w_174_,
        v_aig_175_,
        v_input_176_,
        v_distance_177_,
        v_curr_178_,
        v_hcurr_179_,
        v_s_180_,
    );
    leanh::lean_dec(v_distance_177_);
    leanh::lean_dec_ref(v_input_176_);
    leanh::lean_dec_ref(v_aig_175_);
    leanh::lean_dec(v_w_174_);
    leanh::lean_dec_ref(v_inst_173_);
    leanh::lean_dec_ref(v_inst_172_);
    return v_res_181_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(
    mut v_w_182_: *mut leanh::LeanObject,
    mut v_aig_183_: *mut leanh::LeanObject,
    mut v_target_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vec_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_189_: u8 = 0;
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vec_185_ = leanh::lean_ctor_get(v_target_184_, 0);
                v_distance_186_ = leanh::lean_ctor_get(v_target_184_, 1);
                v_isSharedCheck_196_ = (!leanh::lean_is_exclusive(v_target_184_)) as u8;
                if v_isSharedCheck_196_ == 0 {
                    v___x_188_ = v_target_184_;
                    v_isShared_189_ = v_isSharedCheck_196_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_distance_186_);
                    leanh::lean_inc(v_vec_185_);
                    leanh::lean_dec(v_target_184_);
                    v___x_188_ = leanh::lean_box(0);
                    v_isShared_189_ = v_isSharedCheck_196_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_190_ = leanh::lean_unsigned_to_nat(0);
                v___x_191_ = lean_mk_empty_array_with_capacity(v_w_182_);
                v___x_192_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft_go___redArg(
                    v_w_182_,
                    v_vec_185_,
                    v_distance_186_,
                    v___x_190_,
                    v___x_191_,
                );
                leanh::lean_dec(v_distance_186_);
                leanh::lean_dec_ref(v_vec_185_);
                if v_isShared_189_ == 0 {
                    leanh::lean_ctor_set(v___x_188_, 1, v___x_192_);
                    leanh::lean_ctor_set(v___x_188_, 0, v_aig_183_);
                    v___x_194_ = v___x_188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_195_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_195_, 0, v_aig_183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_192_);
                    v___x_194_ = v_reuseFailAlloc_195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg___boxed(
    mut v_w_197_: *mut leanh::LeanObject,
    mut v_aig_198_: *mut leanh::LeanObject,
    mut v_target_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(
        v_w_197_,
        v_aig_198_,
        v_target_199_,
    );
    leanh::lean_dec(v_w_197_);
    return v_res_200_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(
    mut v_00_u03b1_201_: *mut leanh::LeanObject,
    mut v_inst_202_: *mut leanh::LeanObject,
    mut v_inst_203_: *mut leanh::LeanObject,
    mut v_w_204_: *mut leanh::LeanObject,
    mut v_aig_205_: *mut leanh::LeanObject,
    mut v_target_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_207_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___redArg(
        v_w_204_,
        v_aig_205_,
        v_target_206_,
    );
    return v___x_207_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft___boxed(
    mut v_00_u03b1_208_: *mut leanh::LeanObject,
    mut v_inst_209_: *mut leanh::LeanObject,
    mut v_inst_210_: *mut leanh::LeanObject,
    mut v_w_211_: *mut leanh::LeanObject,
    mut v_aig_212_: *mut leanh::LeanObject,
    mut v_target_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastRotateLeft(
        v_00_u03b1_208_,
        v_inst_209_,
        v_inst_210_,
        v_w_211_,
        v_aig_212_,
        v_target_213_,
    );
    leanh::lean_dec(v_w_211_);
    leanh::lean_dec_ref(v_inst_210_);
    leanh::lean_dec_ref(v_inst_209_);
    return v_res_214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(
        builtin,
    );
}