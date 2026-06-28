// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
    mut v_n_91_: *mut crate::leanh::LeanObject,
    mut v_input_92_: *mut crate::leanh::LeanObject,
    mut v_curr_93_: *mut crate::leanh::LeanObject,
    mut v_s_94_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_95_: u8 = 0;
    let mut v_s_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_95_ = lean_nat_dec_lt(v_curr_93_, v_n_91_);
                if v___x_95_ == 0 {
                    crate::leanh::lean_dec(v_curr_93_);
                    return v_s_94_;
                } else {
                    v_s_96_ = l_Array_append___redArg(v_s_94_, v_input_92_);
                    v___x_97_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_98_ = lean_nat_add(v_curr_93_, v___x_97_);
                    crate::leanh::lean_dec(v_curr_93_);
                    v_curr_93_ = v___x_98_;
                    v_s_94_ = v_s_96_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg___boxed(
    mut v_n_100_: *mut crate::leanh::LeanObject,
    mut v_input_101_: *mut crate::leanh::LeanObject,
    mut v_curr_102_: *mut crate::leanh::LeanObject,
    mut v_s_103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_104_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
        v_n_100_,
        v_input_101_,
        v_curr_102_,
        v_s_103_,
    );
    crate::leanh::lean_dec_ref(v_input_101_);
    crate::leanh::lean_dec(v_n_100_);
    return v_res_104_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go(
    mut v_00_u03b1_105_: *mut crate::leanh::LeanObject,
    mut v_inst_106_: *mut crate::leanh::LeanObject,
    mut v_inst_107_: *mut crate::leanh::LeanObject,
    mut v_aig_108_: *mut crate::leanh::LeanObject,
    mut v_w_109_: *mut crate::leanh::LeanObject,
    mut v_n_110_: *mut crate::leanh::LeanObject,
    mut v_input_111_: *mut crate::leanh::LeanObject,
    mut v_curr_112_: *mut crate::leanh::LeanObject,
    mut v_hcurr_113_: *mut crate::leanh::LeanObject,
    mut v_s_114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_115_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
        v_n_110_,
        v_input_111_,
        v_curr_112_,
        v_s_114_,
    );
    return v___x_115_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___boxed(
    mut v_00_u03b1_116_: *mut crate::leanh::LeanObject,
    mut v_inst_117_: *mut crate::leanh::LeanObject,
    mut v_inst_118_: *mut crate::leanh::LeanObject,
    mut v_aig_119_: *mut crate::leanh::LeanObject,
    mut v_w_120_: *mut crate::leanh::LeanObject,
    mut v_n_121_: *mut crate::leanh::LeanObject,
    mut v_input_122_: *mut crate::leanh::LeanObject,
    mut v_curr_123_: *mut crate::leanh::LeanObject,
    mut v_hcurr_124_: *mut crate::leanh::LeanObject,
    mut v_s_125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_126_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go(
        v_00_u03b1_116_,
        v_inst_117_,
        v_inst_118_,
        v_aig_119_,
        v_w_120_,
        v_n_121_,
        v_input_122_,
        v_curr_123_,
        v_hcurr_124_,
        v_s_125_,
    );
    crate::leanh::lean_dec_ref(v_input_122_);
    crate::leanh::lean_dec(v_n_121_);
    crate::leanh::lean_dec(v_w_120_);
    crate::leanh::lean_dec_ref(v_aig_119_);
    crate::leanh::lean_dec_ref(v_inst_118_);
    crate::leanh::lean_dec_ref(v_inst_117_);
    return v_res_126_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(
    mut v_newWidth_127_: *mut crate::leanh::LeanObject,
    mut v_aig_128_: *mut crate::leanh::LeanObject,
    mut v_target_129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_130_ = crate::leanh::lean_ctor_get(v_target_129_, 1);
    v_inner_131_ = crate::leanh::lean_ctor_get(v_target_129_, 2);
    v___x_132_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_133_ = lean_mk_empty_array_with_capacity(v_newWidth_127_);
    v_ref_134_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
        v_n_130_,
        v_inner_131_,
        v___x_132_,
        v___x_133_,
    );
    v___x_135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_135_, 0, v_aig_128_);
    crate::leanh::lean_ctor_set(v___x_135_, 1, v_ref_134_);
    return v___x_135_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg___boxed(
    mut v_newWidth_136_: *mut crate::leanh::LeanObject,
    mut v_aig_137_: *mut crate::leanh::LeanObject,
    mut v_target_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_139_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(
        v_newWidth_136_,
        v_aig_137_,
        v_target_138_,
    );
    crate::leanh::lean_dec_ref(v_target_138_);
    crate::leanh::lean_dec(v_newWidth_136_);
    return v_res_139_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(
    mut v_00_u03b1_140_: *mut crate::leanh::LeanObject,
    mut v_inst_141_: *mut crate::leanh::LeanObject,
    mut v_inst_142_: *mut crate::leanh::LeanObject,
    mut v_newWidth_143_: *mut crate::leanh::LeanObject,
    mut v_aig_144_: *mut crate::leanh::LeanObject,
    mut v_target_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(
        v_newWidth_143_,
        v_aig_144_,
        v_target_145_,
    );
    return v___x_146_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___boxed(
    mut v_00_u03b1_147_: *mut crate::leanh::LeanObject,
    mut v_inst_148_: *mut crate::leanh::LeanObject,
    mut v_inst_149_: *mut crate::leanh::LeanObject,
    mut v_newWidth_150_: *mut crate::leanh::LeanObject,
    mut v_aig_151_: *mut crate::leanh::LeanObject,
    mut v_target_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_153_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(
        v_00_u03b1_147_,
        v_inst_148_,
        v_inst_149_,
        v_newWidth_150_,
        v_aig_151_,
        v_target_152_,
    );
    crate::leanh::lean_dec_ref(v_target_152_);
    crate::leanh::lean_dec(v_newWidth_150_);
    crate::leanh::lean_dec_ref(v_inst_149_);
    crate::leanh::lean_dec_ref(v_inst_148_);
    return v_res_153_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___redArg(
    mut v_target_154_: *mut crate::leanh::LeanObject,
    mut v_h__1_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_156_ = crate::leanh::lean_ctor_get(v_target_154_, 0);
    crate::leanh::lean_inc(v_w_156_);
    v_n_157_ = crate::leanh::lean_ctor_get(v_target_154_, 1);
    crate::leanh::lean_inc(v_n_157_);
    v_inner_158_ = crate::leanh::lean_ctor_get(v_target_154_, 2);
    crate::leanh::lean_inc_ref(v_inner_158_);
    crate::leanh::lean_dec_ref(v_target_154_);
    v___x_159_ = crate::leanh::lean_apply_4(
        v_h__1_155_,
        v_w_156_,
        v_n_157_,
        v_inner_158_,
        crate::leanh::lean_box(0),
    );
    return v___x_159_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_inst_161_: *mut crate::leanh::LeanObject,
    mut v_inst_162_: *mut crate::leanh::LeanObject,
    mut v_newWidth_163_: *mut crate::leanh::LeanObject,
    mut v_aig_164_: *mut crate::leanh::LeanObject,
    mut v_motive_165_: *mut crate::leanh::LeanObject,
    mut v_target_166_: *mut crate::leanh::LeanObject,
    mut v_h__1_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_168_ = crate::leanh::lean_ctor_get(v_target_166_, 0);
    crate::leanh::lean_inc(v_w_168_);
    v_n_169_ = crate::leanh::lean_ctor_get(v_target_166_, 1);
    crate::leanh::lean_inc(v_n_169_);
    v_inner_170_ = crate::leanh::lean_ctor_get(v_target_166_, 2);
    crate::leanh::lean_inc_ref(v_inner_170_);
    crate::leanh::lean_dec_ref(v_target_166_);
    v___x_171_ = crate::leanh::lean_apply_4(
        v_h__1_167_,
        v_w_168_,
        v_n_169_,
        v_inner_170_,
        crate::leanh::lean_box(0),
    );
    return v___x_171_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___boxed(
    mut v_00_u03b1_172_: *mut crate::leanh::LeanObject,
    mut v_inst_173_: *mut crate::leanh::LeanObject,
    mut v_inst_174_: *mut crate::leanh::LeanObject,
    mut v_newWidth_175_: *mut crate::leanh::LeanObject,
    mut v_aig_176_: *mut crate::leanh::LeanObject,
    mut v_motive_177_: *mut crate::leanh::LeanObject,
    mut v_target_178_: *mut crate::leanh::LeanObject,
    mut v_h__1_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(v_00_u03b1_172_, v_inst_173_, v_inst_174_, v_newWidth_175_, v_aig_176_, v_motive_177_, v_target_178_, v_h__1_179_);
    crate::leanh::lean_dec_ref(v_aig_176_);
    crate::leanh::lean_dec(v_newWidth_175_);
    crate::leanh::lean_dec_ref(v_inst_174_);
    crate::leanh::lean_dec_ref(v_inst_173_);
    return v_res_180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
}
