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
    mut v_aig_90_: *mut crate::leanh::LeanObject,
    mut v_w_91_: *mut crate::leanh::LeanObject,
    mut v_input_92_: *mut crate::leanh::LeanObject,
    mut v_newWidth_93_: *mut crate::leanh::LeanObject,
    mut v_curr_94_: *mut crate::leanh::LeanObject,
    mut v_s_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_98_: u8 = 0;
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: u8 = 0;
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: u8 = 0;
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_107_ = lean_nat_dec_lt(v_curr_94_, v_newWidth_93_);
                if v___x_107_ == 0 {
                    crate::leanh::lean_dec(v_curr_94_);
                    v___x_108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_108_, 0, v_aig_90_);
                    crate::leanh::lean_ctor_set(v___x_108_, 1, v_s_95_);
                    return v___x_108_;
                } else {
                    v___x_109_ = lean_nat_dec_lt(v_curr_94_, v_w_91_);
                    if v___x_109_ == 0 {
                        v___x_110_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_111_ = lean_nat_add(v_curr_94_, v___x_110_);
                        crate::leanh::lean_dec(v_curr_94_);
                        v___x_112_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_113_ = l_Bool_toNat(v___x_109_);
                        v___x_114_ = lean_nat_lor(v___x_112_, v___x_113_);
                        crate::leanh::lean_dec(v___x_113_);
                        v_s_115_ = lean_array_push(v_s_95_, v___x_114_);
                        v_curr_94_ = v___x_111_;
                        v_s_95_ = v_s_115_;
                        state = 0;
                        continue;
                    } else {
                        v_ref_117_ = lean_array_fget_borrowed(v_input_92_, v_curr_94_);
                        v___x_118_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_119_ = lean_nat_shiftr(v_ref_117_, v___x_118_);
                        v___x_120_ = lean_nat_land(v___x_118_, v_ref_117_);
                        v___x_121_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
                        crate::leanh::lean_dec(v___x_120_);
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
                v___x_99_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_100_ = lean_nat_add(v_curr_94_, v___x_99_);
                crate::leanh::lean_dec(v_curr_94_);
                v___x_101_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_102_ = lean_nat_mul(v_gate_97_, v___x_101_);
                crate::leanh::lean_dec(v_gate_97_);
                v___x_103_ = l_Bool_toNat(v_invert_98_);
                v___x_104_ = lean_nat_lor(v___x_102_, v___x_103_);
                crate::leanh::lean_dec(v___x_103_);
                crate::leanh::lean_dec(v___x_102_);
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
    mut v_aig_124_: *mut crate::leanh::LeanObject,
    mut v_w_125_: *mut crate::leanh::LeanObject,
    mut v_input_126_: *mut crate::leanh::LeanObject,
    mut v_newWidth_127_: *mut crate::leanh::LeanObject,
    mut v_curr_128_: *mut crate::leanh::LeanObject,
    mut v_s_129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_130_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go___redArg(
        v_aig_124_,
        v_w_125_,
        v_input_126_,
        v_newWidth_127_,
        v_curr_128_,
        v_s_129_,
    );
    crate::leanh::lean_dec(v_newWidth_127_);
    crate::leanh::lean_dec_ref(v_input_126_);
    crate::leanh::lean_dec(v_w_125_);
    return v_res_130_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend_go(
    mut v_00_u03b1_131_: *mut crate::leanh::LeanObject,
    mut v_inst_132_: *mut crate::leanh::LeanObject,
    mut v_inst_133_: *mut crate::leanh::LeanObject,
    mut v_aig_134_: *mut crate::leanh::LeanObject,
    mut v_w_135_: *mut crate::leanh::LeanObject,
    mut v_input_136_: *mut crate::leanh::LeanObject,
    mut v_newWidth_137_: *mut crate::leanh::LeanObject,
    mut v_curr_138_: *mut crate::leanh::LeanObject,
    mut v_hcurr_139_: *mut crate::leanh::LeanObject,
    mut v_s_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_142_: *mut crate::leanh::LeanObject,
    mut v_inst_143_: *mut crate::leanh::LeanObject,
    mut v_inst_144_: *mut crate::leanh::LeanObject,
    mut v_aig_145_: *mut crate::leanh::LeanObject,
    mut v_w_146_: *mut crate::leanh::LeanObject,
    mut v_input_147_: *mut crate::leanh::LeanObject,
    mut v_newWidth_148_: *mut crate::leanh::LeanObject,
    mut v_curr_149_: *mut crate::leanh::LeanObject,
    mut v_hcurr_150_: *mut crate::leanh::LeanObject,
    mut v_s_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_newWidth_148_);
    crate::leanh::lean_dec_ref(v_input_147_);
    crate::leanh::lean_dec(v_w_146_);
    crate::leanh::lean_dec_ref(v_inst_144_);
    crate::leanh::lean_dec_ref(v_inst_143_);
    return v_res_152_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
    mut v_newWidth_153_: *mut crate::leanh::LeanObject,
    mut v_aig_154_: *mut crate::leanh::LeanObject,
    mut v_target_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_156_ = crate::leanh::lean_ctor_get(v_target_155_, 0);
    v_vec_157_ = crate::leanh::lean_ctor_get(v_target_155_, 1);
    v___x_158_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_newWidth_161_: *mut crate::leanh::LeanObject,
    mut v_aig_162_: *mut crate::leanh::LeanObject,
    mut v_target_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_164_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
        v_newWidth_161_,
        v_aig_162_,
        v_target_163_,
    );
    crate::leanh::lean_dec_ref(v_target_163_);
    crate::leanh::lean_dec(v_newWidth_161_);
    return v_res_164_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(
    mut v_00_u03b1_165_: *mut crate::leanh::LeanObject,
    mut v_inst_166_: *mut crate::leanh::LeanObject,
    mut v_inst_167_: *mut crate::leanh::LeanObject,
    mut v_newWidth_168_: *mut crate::leanh::LeanObject,
    mut v_aig_169_: *mut crate::leanh::LeanObject,
    mut v_target_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_171_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
        v_newWidth_168_,
        v_aig_169_,
        v_target_170_,
    );
    return v___x_171_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___boxed(
    mut v_00_u03b1_172_: *mut crate::leanh::LeanObject,
    mut v_inst_173_: *mut crate::leanh::LeanObject,
    mut v_inst_174_: *mut crate::leanh::LeanObject,
    mut v_newWidth_175_: *mut crate::leanh::LeanObject,
    mut v_aig_176_: *mut crate::leanh::LeanObject,
    mut v_target_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_178_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend(
        v_00_u03b1_172_,
        v_inst_173_,
        v_inst_174_,
        v_newWidth_175_,
        v_aig_176_,
        v_target_177_,
    );
    crate::leanh::lean_dec_ref(v_target_177_);
    crate::leanh::lean_dec(v_newWidth_175_);
    crate::leanh::lean_dec_ref(v_inst_174_);
    crate::leanh::lean_dec_ref(v_inst_173_);
    return v_res_178_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
}
