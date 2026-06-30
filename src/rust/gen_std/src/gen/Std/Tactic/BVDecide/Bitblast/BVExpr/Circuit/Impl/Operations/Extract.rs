// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_mul, lean_nat_shiftr,
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
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(
    mut v_newWidth_88_: *mut leanh::LeanObject,
    mut v_w_89_: *mut leanh::LeanObject,
    mut v_input_90_: *mut leanh::LeanObject,
    mut v_start_91_: *mut leanh::LeanObject,
    mut v_curr_92_: *mut leanh::LeanObject,
    mut v_s_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_96_: u8 = 0;
    let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: u8 = 0;
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: u8 = 0;
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: u8 = 0;
    let mut v___x_115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_105_ = lean_nat_dec_lt(v_curr_92_, v_newWidth_88_);
                if v___x_105_ == 0 {
                    leanh::lean_dec(v_curr_92_);
                    return v_s_93_;
                } else {
                    v___x_106_ = lean_nat_add(v_start_91_, v_curr_92_);
                    v___x_107_ = lean_nat_dec_lt(v___x_106_, v_w_89_);
                    if v___x_107_ == 0 {
                        leanh::lean_dec(v___x_106_);
                        v___x_108_ = leanh::lean_unsigned_to_nat(0);
                        v_gate_95_ = v___x_108_;
                        v_invert_96_ = v___x_107_;
                        state = 1;
                        continue;
                    } else {
                        v_ref_109_ = lean_array_fget_borrowed(v_input_90_, v___x_106_);
                        leanh::lean_dec(v___x_106_);
                        v___x_110_ = leanh::lean_unsigned_to_nat(1);
                        v___x_111_ = lean_nat_shiftr(v_ref_109_, v___x_110_);
                        v___x_112_ = lean_nat_land(v___x_110_, v_ref_109_);
                        v___x_113_ = leanh::lean_unsigned_to_nat(0);
                        v___x_114_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
                        leanh::lean_dec(v___x_112_);
                        if v___x_114_ == 0 {
                            v_gate_95_ = v___x_111_;
                            v_invert_96_ = v___x_107_;
                            state = 1;
                            continue;
                        } else {
                            v___x_115_ = 0;
                            v_gate_95_ = v___x_111_;
                            v_invert_96_ = v___x_115_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_97_ = leanh::lean_unsigned_to_nat(1);
                v___x_98_ = lean_nat_add(v_curr_92_, v___x_97_);
                leanh::lean_dec(v_curr_92_);
                v___x_99_ = leanh::lean_unsigned_to_nat(2);
                v___x_100_ = lean_nat_mul(v_gate_95_, v___x_99_);
                leanh::lean_dec(v_gate_95_);
                v___x_101_ = l_Bool_toNat(v_invert_96_);
                v___x_102_ = lean_nat_lor(v___x_100_, v___x_101_);
                leanh::lean_dec(v___x_101_);
                leanh::lean_dec(v___x_100_);
                v_s_103_ = lean_array_push(v_s_93_, v___x_102_);
                v_curr_92_ = v___x_98_;
                v_s_93_ = v_s_103_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg___boxed(
    mut v_newWidth_116_: *mut leanh::LeanObject,
    mut v_w_117_: *mut leanh::LeanObject,
    mut v_input_118_: *mut leanh::LeanObject,
    mut v_start_119_: *mut leanh::LeanObject,
    mut v_curr_120_: *mut leanh::LeanObject,
    mut v_s_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(
        v_newWidth_116_,
        v_w_117_,
        v_input_118_,
        v_start_119_,
        v_curr_120_,
        v_s_121_,
    );
    leanh::lean_dec(v_start_119_);
    leanh::lean_dec_ref(v_input_118_);
    leanh::lean_dec(v_w_117_);
    leanh::lean_dec(v_newWidth_116_);
    return v_res_122_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(
    mut v_00_u03b1_123_: *mut leanh::LeanObject,
    mut v_inst_124_: *mut leanh::LeanObject,
    mut v_inst_125_: *mut leanh::LeanObject,
    mut v_newWidth_126_: *mut leanh::LeanObject,
    mut v_aig_127_: *mut leanh::LeanObject,
    mut v_w_128_: *mut leanh::LeanObject,
    mut v_input_129_: *mut leanh::LeanObject,
    mut v_start_130_: *mut leanh::LeanObject,
    mut v_curr_131_: *mut leanh::LeanObject,
    mut v_hcurr_132_: *mut leanh::LeanObject,
    mut v_s_133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(
        v_newWidth_126_,
        v_w_128_,
        v_input_129_,
        v_start_130_,
        v_curr_131_,
        v_s_133_,
    );
    return v___x_134_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___boxed(
    mut v_00_u03b1_135_: *mut leanh::LeanObject,
    mut v_inst_136_: *mut leanh::LeanObject,
    mut v_inst_137_: *mut leanh::LeanObject,
    mut v_newWidth_138_: *mut leanh::LeanObject,
    mut v_aig_139_: *mut leanh::LeanObject,
    mut v_w_140_: *mut leanh::LeanObject,
    mut v_input_141_: *mut leanh::LeanObject,
    mut v_start_142_: *mut leanh::LeanObject,
    mut v_curr_143_: *mut leanh::LeanObject,
    mut v_hcurr_144_: *mut leanh::LeanObject,
    mut v_s_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_146_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(
        v_00_u03b1_135_,
        v_inst_136_,
        v_inst_137_,
        v_newWidth_138_,
        v_aig_139_,
        v_w_140_,
        v_input_141_,
        v_start_142_,
        v_curr_143_,
        v_hcurr_144_,
        v_s_145_,
    );
    leanh::lean_dec(v_start_142_);
    leanh::lean_dec_ref(v_input_141_);
    leanh::lean_dec(v_w_140_);
    leanh::lean_dec_ref(v_aig_139_);
    leanh::lean_dec(v_newWidth_138_);
    leanh::lean_dec_ref(v_inst_137_);
    leanh::lean_dec_ref(v_inst_136_);
    return v_res_146_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
    mut v_newWidth_147_: *mut leanh::LeanObject,
    mut v_aig_148_: *mut leanh::LeanObject,
    mut v_target_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_w_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_w_150_ = leanh::lean_ctor_get(v_target_149_, 0);
    v_vec_151_ = leanh::lean_ctor_get(v_target_149_, 1);
    v_start_152_ = leanh::lean_ctor_get(v_target_149_, 2);
    v___x_153_ = leanh::lean_unsigned_to_nat(0);
    v___x_154_ = lean_mk_empty_array_with_capacity(v_newWidth_147_);
    v___x_155_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___redArg(
        v_newWidth_147_,
        v_w_150_,
        v_vec_151_,
        v_start_152_,
        v___x_153_,
        v___x_154_,
    );
    v___x_156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_156_, 0, v_aig_148_);
    leanh::lean_ctor_set(v___x_156_, 1, v___x_155_);
    return v___x_156_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg___boxed(
    mut v_newWidth_157_: *mut leanh::LeanObject,
    mut v_aig_158_: *mut leanh::LeanObject,
    mut v_target_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_160_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
        v_newWidth_157_,
        v_aig_158_,
        v_target_159_,
    );
    leanh::lean_dec_ref(v_target_159_);
    leanh::lean_dec(v_newWidth_157_);
    return v_res_160_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(
    mut v_00_u03b1_161_: *mut leanh::LeanObject,
    mut v_inst_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_newWidth_164_: *mut leanh::LeanObject,
    mut v_aig_165_: *mut leanh::LeanObject,
    mut v_target_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_167_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
        v_newWidth_164_,
        v_aig_165_,
        v_target_166_,
    );
    return v___x_167_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___boxed(
    mut v_00_u03b1_168_: *mut leanh::LeanObject,
    mut v_inst_169_: *mut leanh::LeanObject,
    mut v_inst_170_: *mut leanh::LeanObject,
    mut v_newWidth_171_: *mut leanh::LeanObject,
    mut v_aig_172_: *mut leanh::LeanObject,
    mut v_target_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_174_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(
        v_00_u03b1_168_,
        v_inst_169_,
        v_inst_170_,
        v_newWidth_171_,
        v_aig_172_,
        v_target_173_,
    );
    leanh::lean_dec_ref(v_target_173_);
    leanh::lean_dec(v_newWidth_171_);
    leanh::lean_dec_ref(v_inst_170_);
    leanh::lean_dec_ref(v_inst_169_);
    return v_res_174_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
}