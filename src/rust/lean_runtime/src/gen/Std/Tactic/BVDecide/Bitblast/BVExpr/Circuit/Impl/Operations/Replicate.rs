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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_4, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
    mut v_n_91_: *mut LeanObject,
    mut v_input_92_: *mut LeanObject,
    mut v_curr_93_: *mut LeanObject,
    mut v_s_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_95_: u8 = 0;
    let mut v_s_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_95_ = lean_nat_dec_lt(v_curr_93_, v_n_91_);
                if v___x_95_ == 0 {
                    lean_dec(v_curr_93_);
                    return v_s_94_;
                } else {
                    v_s_96_ = l_Array_append___redArg(v_s_94_, v_input_92_);
                    v___x_97_ = lean_unsigned_to_nat(1);
                    v___x_98_ = lean_nat_add(v_curr_93_, v___x_97_);
                    lean_dec(v_curr_93_);
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
    mut v_n_100_: *mut LeanObject,
    mut v_input_101_: *mut LeanObject,
    mut v_curr_102_: *mut LeanObject,
    mut v_s_103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_104_: *mut LeanObject = core::ptr::null_mut();
    v_res_104_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
        v_n_100_,
        v_input_101_,
        v_curr_102_,
        v_s_103_,
    );
    lean_dec_ref(v_input_101_);
    lean_dec(v_n_100_);
    return v_res_104_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go(
    mut v_00_u03b1_105_: *mut LeanObject,
    mut v_inst_106_: *mut LeanObject,
    mut v_inst_107_: *mut LeanObject,
    mut v_aig_108_: *mut LeanObject,
    mut v_w_109_: *mut LeanObject,
    mut v_n_110_: *mut LeanObject,
    mut v_input_111_: *mut LeanObject,
    mut v_curr_112_: *mut LeanObject,
    mut v_hcurr_113_: *mut LeanObject,
    mut v_s_114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    v___x_115_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
        v_n_110_,
        v_input_111_,
        v_curr_112_,
        v_s_114_,
    );
    return v___x_115_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___boxed(
    mut v_00_u03b1_116_: *mut LeanObject,
    mut v_inst_117_: *mut LeanObject,
    mut v_inst_118_: *mut LeanObject,
    mut v_aig_119_: *mut LeanObject,
    mut v_w_120_: *mut LeanObject,
    mut v_n_121_: *mut LeanObject,
    mut v_input_122_: *mut LeanObject,
    mut v_curr_123_: *mut LeanObject,
    mut v_hcurr_124_: *mut LeanObject,
    mut v_s_125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_126_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_input_122_);
    lean_dec(v_n_121_);
    lean_dec(v_w_120_);
    lean_dec_ref(v_aig_119_);
    lean_dec_ref(v_inst_118_);
    lean_dec_ref(v_inst_117_);
    return v_res_126_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(
    mut v_newWidth_127_: *mut LeanObject,
    mut v_aig_128_: *mut LeanObject,
    mut v_target_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    v_n_130_ = lean_ctor_get(v_target_129_, 1);
    v_inner_131_ = lean_ctor_get(v_target_129_, 2);
    v___x_132_ = lean_unsigned_to_nat(0);
    v___x_133_ = lean_mk_empty_array_with_capacity(v_newWidth_127_);
    v_ref_134_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_go___redArg(
        v_n_130_,
        v_inner_131_,
        v___x_132_,
        v___x_133_,
    );
    v___x_135_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_135_, 0, v_aig_128_);
    lean_ctor_set(v___x_135_, 1, v_ref_134_);
    return v___x_135_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg___boxed(
    mut v_newWidth_136_: *mut LeanObject,
    mut v_aig_137_: *mut LeanObject,
    mut v_target_138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_139_: *mut LeanObject = core::ptr::null_mut();
    v_res_139_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(
        v_newWidth_136_,
        v_aig_137_,
        v_target_138_,
    );
    lean_dec_ref(v_target_138_);
    lean_dec(v_newWidth_136_);
    return v_res_139_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(
    mut v_00_u03b1_140_: *mut LeanObject,
    mut v_inst_141_: *mut LeanObject,
    mut v_inst_142_: *mut LeanObject,
    mut v_newWidth_143_: *mut LeanObject,
    mut v_aig_144_: *mut LeanObject,
    mut v_target_145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    v___x_146_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___redArg(
        v_newWidth_143_,
        v_aig_144_,
        v_target_145_,
    );
    return v___x_146_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate___boxed(
    mut v_00_u03b1_147_: *mut LeanObject,
    mut v_inst_148_: *mut LeanObject,
    mut v_inst_149_: *mut LeanObject,
    mut v_newWidth_150_: *mut LeanObject,
    mut v_aig_151_: *mut LeanObject,
    mut v_target_152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_153_: *mut LeanObject = core::ptr::null_mut();
    v_res_153_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate(
        v_00_u03b1_147_,
        v_inst_148_,
        v_inst_149_,
        v_newWidth_150_,
        v_aig_151_,
        v_target_152_,
    );
    lean_dec_ref(v_target_152_);
    lean_dec(v_newWidth_150_);
    lean_dec_ref(v_inst_149_);
    lean_dec_ref(v_inst_148_);
    return v_res_153_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___redArg(
    mut v_target_154_: *mut LeanObject,
    mut v_h__1_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_w_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    v_w_156_ = lean_ctor_get(v_target_154_, 0);
    lean_inc(v_w_156_);
    v_n_157_ = lean_ctor_get(v_target_154_, 1);
    lean_inc(v_n_157_);
    v_inner_158_ = lean_ctor_get(v_target_154_, 2);
    lean_inc_ref(v_inner_158_);
    lean_dec_ref(v_target_154_);
    v___x_159_ = lean_apply_4(v_h__1_155_, v_w_156_, v_n_157_, v_inner_158_, lean_box(0));
    return v___x_159_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(
    mut v_00_u03b1_160_: *mut LeanObject,
    mut v_inst_161_: *mut LeanObject,
    mut v_inst_162_: *mut LeanObject,
    mut v_newWidth_163_: *mut LeanObject,
    mut v_aig_164_: *mut LeanObject,
    mut v_motive_165_: *mut LeanObject,
    mut v_target_166_: *mut LeanObject,
    mut v_h__1_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_w_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    v_w_168_ = lean_ctor_get(v_target_166_, 0);
    lean_inc(v_w_168_);
    v_n_169_ = lean_ctor_get(v_target_166_, 1);
    lean_inc(v_n_169_);
    v_inner_170_ = lean_ctor_get(v_target_166_, 2);
    lean_inc_ref(v_inner_170_);
    lean_dec_ref(v_target_166_);
    v___x_171_ = lean_apply_4(v_h__1_167_, v_w_168_, v_n_169_, v_inner_170_, lean_box(0));
    return v___x_171_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter___boxed(
    mut v_00_u03b1_172_: *mut LeanObject,
    mut v_inst_173_: *mut LeanObject,
    mut v_inst_174_: *mut LeanObject,
    mut v_newWidth_175_: *mut LeanObject,
    mut v_aig_176_: *mut LeanObject,
    mut v_motive_177_: *mut LeanObject,
    mut v_target_178_: *mut LeanObject,
    mut v_h__1_179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_180_: *mut LeanObject = core::ptr::null_mut();
    v_res_180_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReplicate_match__1_splitter(v_00_u03b1_172_, v_inst_173_, v_inst_174_, v_newWidth_175_, v_aig_176_, v_motive_177_, v_target_178_, v_h__1_179_);
    lean_dec_ref(v_aig_176_);
    lean_dec(v_newWidth_175_);
    lean_dec_ref(v_inst_174_);
    lean_dec_ref(v_inst_173_);
    return v_res_180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(
        builtin,
    );
}
