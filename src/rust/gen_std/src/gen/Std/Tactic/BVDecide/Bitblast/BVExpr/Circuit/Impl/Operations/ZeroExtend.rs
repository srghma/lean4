// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
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
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(
    mut v_aig_90_: *mut leanh::LeanObject,
    mut v_w_91_: *mut leanh::LeanObject,
    mut v_input_92_: *mut leanh::LeanObject,
    mut v_newWidth_93_: *mut leanh::LeanObject,
    mut v_curr_94_: *mut leanh::LeanObject,
    mut v_s_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_98_: u8 = 0;
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: u8 = 0;
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: u8 = 0;
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_107_ = lean_nat_dec_lt(v_curr_94_, v_newWidth_93_);
                if v___x_107_ == 0 {
                    leanh::lean_dec(v_curr_94_);
                    v___x_108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_108_, 0, v_aig_90_);
                    leanh::lean_ctor_set(v___x_108_, 1, v_s_95_);
                    return v___x_108_;
                } else {
                    v___x_109_ = lean_nat_dec_lt(v_curr_94_, v_w_91_);
                    if v___x_109_ == 0 {
                        v___x_110_ = leanh::lean_unsigned_to_nat(1);
                        v___x_111_ = lean_nat_add(v_curr_94_, v___x_110_);
                        leanh::lean_dec(v_curr_94_);
                        v___x_112_ = leanh::lean_unsigned_to_nat(0);
                        v___x_113_ = l_Bool_toNat(v___x_109_);
                        v___x_114_ = lean_nat_lor(v___x_112_, v___x_113_);
                        leanh::lean_dec(v___x_113_);
                        v_s_115_ = lean_array_push(v_s_95_, v___x_114_);
                        v_curr_94_ = v___x_111_;
                        v_s_95_ = v_s_115_;
                        state = 0;
                        continue;
                    } else {
                        v_ref_117_ = lean_array_fget_borrowed(v_input_92_, v_curr_94_);
                        v___x_118_ = leanh::lean_unsigned_to_nat(1);
                        v___x_119_ = lean_nat_shiftr(v_ref_117_, v___x_118_);
                        v___x_120_ = lean_nat_land(v___x_118_, v_ref_117_);
                        v___x_121_ = leanh::lean_unsigned_to_nat(0);
                        v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
                        leanh::lean_dec(v___x_120_);
                        if v___x_122_ == 0 {
                            v_gate_97_ = v___x_119_;
                            v_invert_98_ = v___x_109_;
                            state = 1;
                            continue;
                        } else {
                            v___x_123_ = 0;
                            v_gate_97_ = v___x_119_;
                            v_invert_98_ = v___x_123_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_99_ = leanh::lean_unsigned_to_nat(1);
                v___x_100_ = lean_nat_add(v_curr_94_, v___x_99_);
                leanh::lean_dec(v_curr_94_);
                v___x_101_ = leanh::lean_unsigned_to_nat(2);
                v___x_102_ = lean_nat_mul(v_gate_97_, v___x_101_);
                leanh::lean_dec(v_gate_97_);
                v___x_103_ = l_Bool_toNat(v_invert_98_);
                v___x_104_ = lean_nat_lor(v___x_102_, v___x_103_);
                leanh::lean_dec(v___x_103_);
                leanh::lean_dec(v___x_102_);
                v_s_105_ = lean_array_push(v_s_95_, v___x_104_);
                v_curr_94_ = v___x_100_;
                v_s_95_ = v_s_105_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg___boxed(
    mut v_aig_124_: *mut leanh::LeanObject,
    mut v_w_125_: *mut leanh::LeanObject,
    mut v_input_126_: *mut leanh::LeanObject,
    mut v_newWidth_127_: *mut leanh::LeanObject,
    mut v_curr_128_: *mut leanh::LeanObject,
    mut v_s_129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_130_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(
        v_aig_124_,
        v_w_125_,
        v_input_126_,
        v_newWidth_127_,
        v_curr_128_,
        v_s_129_,
    );
    leanh::lean_dec(v_newWidth_127_);
    leanh::lean_dec_ref(v_input_126_);
    leanh::lean_dec(v_w_125_);
    return v_res_130_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(
    mut v_00_u03b1_131_: *mut leanh::LeanObject,
    mut v_inst_132_: *mut leanh::LeanObject,
    mut v_inst_133_: *mut leanh::LeanObject,
    mut v_aig_134_: *mut leanh::LeanObject,
    mut v_w_135_: *mut leanh::LeanObject,
    mut v_input_136_: *mut leanh::LeanObject,
    mut v_newWidth_137_: *mut leanh::LeanObject,
    mut v_curr_138_: *mut leanh::LeanObject,
    mut v_hcurr_139_: *mut leanh::LeanObject,
    mut v_s_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(
        v_aig_134_,
        v_w_135_,
        v_input_136_,
        v_newWidth_137_,
        v_curr_138_,
        v_s_140_,
    );
    return v___x_141_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___boxed(
    mut v_00_u03b1_142_: *mut leanh::LeanObject,
    mut v_inst_143_: *mut leanh::LeanObject,
    mut v_inst_144_: *mut leanh::LeanObject,
    mut v_aig_145_: *mut leanh::LeanObject,
    mut v_w_146_: *mut leanh::LeanObject,
    mut v_input_147_: *mut leanh::LeanObject,
    mut v_newWidth_148_: *mut leanh::LeanObject,
    mut v_curr_149_: *mut leanh::LeanObject,
    mut v_hcurr_150_: *mut leanh::LeanObject,
    mut v_s_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(
        v_00_u03b1_142_,
        v_inst_143_,
        v_inst_144_,
        v_aig_145_,
        v_w_146_,
        v_input_147_,
        v_newWidth_148_,
        v_curr_149_,
        v_hcurr_150_,
        v_s_151_,
    );
    leanh::lean_dec(v_newWidth_148_);
    leanh::lean_dec_ref(v_input_147_);
    leanh::lean_dec(v_w_146_);
    leanh::lean_dec_ref(v_inst_144_);
    leanh::lean_dec_ref(v_inst_143_);
    return v_res_152_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
    mut v_newWidth_153_: *mut leanh::LeanObject,
    mut v_aig_154_: *mut leanh::LeanObject,
    mut v_target_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_w_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_w_156_ = leanh::lean_ctor_get(v_target_155_, 0);
    v_vec_157_ = leanh::lean_ctor_get(v_target_155_, 1);
    v___x_158_ = leanh::lean_unsigned_to_nat(0);
    v___x_159_ = lean_mk_empty_array_with_capacity(v_newWidth_153_);
    v___x_160_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(
        v_aig_154_,
        v_w_156_,
        v_vec_157_,
        v_newWidth_153_,
        v___x_158_,
        v___x_159_,
    );
    return v___x_160_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg___boxed(
    mut v_newWidth_161_: *mut leanh::LeanObject,
    mut v_aig_162_: *mut leanh::LeanObject,
    mut v_target_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_164_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
        v_newWidth_161_,
        v_aig_162_,
        v_target_163_,
    );
    leanh::lean_dec_ref(v_target_163_);
    leanh::lean_dec(v_newWidth_161_);
    return v_res_164_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(
    mut v_00_u03b1_165_: *mut leanh::LeanObject,
    mut v_inst_166_: *mut leanh::LeanObject,
    mut v_inst_167_: *mut leanh::LeanObject,
    mut v_newWidth_168_: *mut leanh::LeanObject,
    mut v_aig_169_: *mut leanh::LeanObject,
    mut v_target_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_171_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
        v_newWidth_168_,
        v_aig_169_,
        v_target_170_,
    );
    return v___x_171_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___boxed(
    mut v_00_u03b1_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_inst_174_: *mut leanh::LeanObject,
    mut v_newWidth_175_: *mut leanh::LeanObject,
    mut v_aig_176_: *mut leanh::LeanObject,
    mut v_target_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_178_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(
        v_00_u03b1_172_,
        v_inst_173_,
        v_inst_174_,
        v_newWidth_175_,
        v_aig_176_,
        v_target_177_,
    );
    leanh::lean_dec_ref(v_target_177_);
    leanh::lean_dec(v_newWidth_175_);
    leanh::lean_dec_ref(v_inst_174_);
    leanh::lean_dec_ref(v_inst_173_);
    return v_res_178_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
}