// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
// Imports: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker Std.Tactic.BVDecide.LRAT.Internal.CNF Std.Tactic.BVDecide.LRAT.Internal.Actions
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CNF::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATChecker::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_apply_5, lean_apply_6, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter___redArg(
    mut v_prf_95_: *mut LeanObject,
    mut v_h__1_96_: *mut LeanObject,
    mut v_h__2_97_: *mut LeanObject,
    mut v_h__3_98_: *mut LeanObject,
    mut v_h__4_99_: *mut LeanObject,
    mut v_h__5_100_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_prf_95_) == 0 {
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__5_100_);
        lean_dec(v_h__4_99_);
        lean_dec(v_h__3_98_);
        lean_dec(v_h__2_97_);
        v___x_101_ = lean_box(0);
        v___x_102_ = lean_apply_1(v_h__1_96_, v___x_101_);
        return v___x_102_;
    } else {
        let mut v_head_103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_96_);
        v_head_103_ = lean_ctor_get(v_prf_95_, 0);
        lean_inc(v_head_103_);
        match lean_obj_tag(v_head_103_) {
            0 => {
                let mut v_tail_104_: *mut LeanObject = core::ptr::null_mut();
                let mut v_id_105_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_106_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_100_);
                lean_dec(v_h__4_99_);
                lean_dec(v_h__3_98_);
                v_tail_104_ = lean_ctor_get(v_prf_95_, 1);
                lean_inc(v_tail_104_);
                lean_dec_ref_known(v_prf_95_, 2);
                v_id_105_ = lean_ctor_get(v_head_103_, 0);
                lean_inc(v_id_105_);
                v_rupHints_106_ = lean_ctor_get(v_head_103_, 1);
                lean_inc_ref(v_rupHints_106_);
                lean_dec_ref_known(v_head_103_, 2);
                v___x_107_ = lean_apply_3(v_h__2_97_, v_id_105_, v_rupHints_106_, v_tail_104_);
                return v___x_107_;
            }
            1 => {
                let mut v_tail_108_: *mut LeanObject = core::ptr::null_mut();
                let mut v_id_109_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_110_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_111_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_100_);
                lean_dec(v_h__4_99_);
                lean_dec(v_h__2_97_);
                v_tail_108_ = lean_ctor_get(v_prf_95_, 1);
                lean_inc(v_tail_108_);
                lean_dec_ref_known(v_prf_95_, 2);
                v_id_109_ = lean_ctor_get(v_head_103_, 0);
                lean_inc(v_id_109_);
                v_c_110_ = lean_ctor_get(v_head_103_, 1);
                lean_inc(v_c_110_);
                v_rupHints_111_ = lean_ctor_get(v_head_103_, 2);
                lean_inc_ref(v_rupHints_111_);
                lean_dec_ref_known(v_head_103_, 3);
                v___x_112_ = lean_apply_4(
                    v_h__3_98_,
                    v_id_109_,
                    v_c_110_,
                    v_rupHints_111_,
                    v_tail_108_,
                );
                return v___x_112_;
            }
            2 => {
                let mut v_tail_113_: *mut LeanObject = core::ptr::null_mut();
                let mut v_id_114_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_115_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pivot_116_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_117_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ratHints_118_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_100_);
                lean_dec(v_h__3_98_);
                lean_dec(v_h__2_97_);
                v_tail_113_ = lean_ctor_get(v_prf_95_, 1);
                lean_inc(v_tail_113_);
                lean_dec_ref_known(v_prf_95_, 2);
                v_id_114_ = lean_ctor_get(v_head_103_, 0);
                lean_inc(v_id_114_);
                v_c_115_ = lean_ctor_get(v_head_103_, 1);
                lean_inc(v_c_115_);
                v_pivot_116_ = lean_ctor_get(v_head_103_, 2);
                lean_inc_ref(v_pivot_116_);
                v_rupHints_117_ = lean_ctor_get(v_head_103_, 3);
                lean_inc_ref(v_rupHints_117_);
                v_ratHints_118_ = lean_ctor_get(v_head_103_, 4);
                lean_inc_ref(v_ratHints_118_);
                lean_dec_ref_known(v_head_103_, 5);
                v___x_119_ = lean_apply_6(
                    v_h__4_99_,
                    v_id_114_,
                    v_c_115_,
                    v_pivot_116_,
                    v_rupHints_117_,
                    v_ratHints_118_,
                    v_tail_113_,
                );
                return v___x_119_;
            }
            _ => {
                let mut v_tail_120_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ids_121_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_99_);
                lean_dec(v_h__3_98_);
                lean_dec(v_h__2_97_);
                v_tail_120_ = lean_ctor_get(v_prf_95_, 1);
                lean_inc(v_tail_120_);
                lean_dec_ref_known(v_prf_95_, 2);
                v_ids_121_ = lean_ctor_get(v_head_103_, 0);
                lean_inc_ref(v_ids_121_);
                lean_dec_ref_known(v_head_103_, 1);
                v___x_122_ = lean_apply_2(v_h__5_100_, v_ids_121_, v_tail_120_);
                return v___x_122_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter(
    mut v_00_u03b1_123_: *mut LeanObject,
    mut v_00_u03b2_124_: *mut LeanObject,
    mut v_motive_125_: *mut LeanObject,
    mut v_prf_126_: *mut LeanObject,
    mut v_h__1_127_: *mut LeanObject,
    mut v_h__2_128_: *mut LeanObject,
    mut v_h__3_129_: *mut LeanObject,
    mut v_h__4_130_: *mut LeanObject,
    mut v_h__5_131_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_prf_126_) == 0 {
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__5_131_);
        lean_dec(v_h__4_130_);
        lean_dec(v_h__3_129_);
        lean_dec(v_h__2_128_);
        v___x_132_ = lean_box(0);
        v___x_133_ = lean_apply_1(v_h__1_127_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_head_134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_127_);
        v_head_134_ = lean_ctor_get(v_prf_126_, 0);
        lean_inc(v_head_134_);
        match lean_obj_tag(v_head_134_) {
            0 => {
                let mut v_tail_135_: *mut LeanObject = core::ptr::null_mut();
                let mut v_id_136_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_137_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_131_);
                lean_dec(v_h__4_130_);
                lean_dec(v_h__3_129_);
                v_tail_135_ = lean_ctor_get(v_prf_126_, 1);
                lean_inc(v_tail_135_);
                lean_dec_ref_known(v_prf_126_, 2);
                v_id_136_ = lean_ctor_get(v_head_134_, 0);
                lean_inc(v_id_136_);
                v_rupHints_137_ = lean_ctor_get(v_head_134_, 1);
                lean_inc_ref(v_rupHints_137_);
                lean_dec_ref_known(v_head_134_, 2);
                v___x_138_ = lean_apply_3(v_h__2_128_, v_id_136_, v_rupHints_137_, v_tail_135_);
                return v___x_138_;
            }
            1 => {
                let mut v_tail_139_: *mut LeanObject = core::ptr::null_mut();
                let mut v_id_140_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_141_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_142_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_131_);
                lean_dec(v_h__4_130_);
                lean_dec(v_h__2_128_);
                v_tail_139_ = lean_ctor_get(v_prf_126_, 1);
                lean_inc(v_tail_139_);
                lean_dec_ref_known(v_prf_126_, 2);
                v_id_140_ = lean_ctor_get(v_head_134_, 0);
                lean_inc(v_id_140_);
                v_c_141_ = lean_ctor_get(v_head_134_, 1);
                lean_inc(v_c_141_);
                v_rupHints_142_ = lean_ctor_get(v_head_134_, 2);
                lean_inc_ref(v_rupHints_142_);
                lean_dec_ref_known(v_head_134_, 3);
                v___x_143_ = lean_apply_4(
                    v_h__3_129_,
                    v_id_140_,
                    v_c_141_,
                    v_rupHints_142_,
                    v_tail_139_,
                );
                return v___x_143_;
            }
            2 => {
                let mut v_tail_144_: *mut LeanObject = core::ptr::null_mut();
                let mut v_id_145_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_146_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pivot_147_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_148_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ratHints_149_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_131_);
                lean_dec(v_h__3_129_);
                lean_dec(v_h__2_128_);
                v_tail_144_ = lean_ctor_get(v_prf_126_, 1);
                lean_inc(v_tail_144_);
                lean_dec_ref_known(v_prf_126_, 2);
                v_id_145_ = lean_ctor_get(v_head_134_, 0);
                lean_inc(v_id_145_);
                v_c_146_ = lean_ctor_get(v_head_134_, 1);
                lean_inc(v_c_146_);
                v_pivot_147_ = lean_ctor_get(v_head_134_, 2);
                lean_inc_ref(v_pivot_147_);
                v_rupHints_148_ = lean_ctor_get(v_head_134_, 3);
                lean_inc_ref(v_rupHints_148_);
                v_ratHints_149_ = lean_ctor_get(v_head_134_, 4);
                lean_inc_ref(v_ratHints_149_);
                lean_dec_ref_known(v_head_134_, 5);
                v___x_150_ = lean_apply_6(
                    v_h__4_130_,
                    v_id_145_,
                    v_c_146_,
                    v_pivot_147_,
                    v_rupHints_148_,
                    v_ratHints_149_,
                    v_tail_144_,
                );
                return v___x_150_;
            }
            _ => {
                let mut v_tail_151_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ids_152_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_130_);
                lean_dec(v_h__3_129_);
                lean_dec(v_h__2_128_);
                v_tail_151_ = lean_ctor_get(v_prf_126_, 1);
                lean_inc(v_tail_151_);
                lean_dec_ref_known(v_prf_126_, 2);
                v_ids_152_ = lean_ctor_get(v_head_134_, 0);
                lean_inc_ref(v_ids_152_);
                lean_dec_ref_known(v_head_134_, 1);
                v___x_153_ = lean_apply_2(v_h__5_131_, v_ids_152_, v_tail_151_);
                return v___x_153_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(
    mut v_x_154_: *mut LeanObject,
    mut v_h__1_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    v_fst_156_ = lean_ctor_get(v_x_154_, 0);
    lean_inc(v_fst_156_);
    v_snd_157_ = lean_ctor_get(v_x_154_, 1);
    lean_inc(v_snd_157_);
    lean_dec_ref(v_x_154_);
    v___x_158_ = lean_apply_2(v_h__1_155_, v_fst_156_, v_snd_157_);
    return v___x_158_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter(
    mut v_00_u03c3_159_: *mut LeanObject,
    mut v_motive_160_: *mut LeanObject,
    mut v_x_161_: *mut LeanObject,
    mut v_h__1_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    v_fst_163_ = lean_ctor_get(v_x_161_, 0);
    lean_inc(v_fst_163_);
    v_snd_164_ = lean_ctor_get(v_x_161_, 1);
    lean_inc(v_snd_164_);
    lean_dec_ref(v_x_161_);
    v___x_165_ = lean_apply_2(v_h__1_162_, v_fst_163_, v_snd_164_);
    return v___x_165_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter___redArg(
    mut v_x_166_: *mut LeanObject,
    mut v_h__1_167_: *mut LeanObject,
    mut v_h__2_168_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_166_) == 2 {
        let mut v_id_169_: *mut LeanObject = core::ptr::null_mut();
        let mut v_c_170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pivot_171_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rupHints_172_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ratHints_173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_168_);
        v_id_169_ = lean_ctor_get(v_x_166_, 0);
        lean_inc(v_id_169_);
        v_c_170_ = lean_ctor_get(v_x_166_, 1);
        lean_inc(v_c_170_);
        v_pivot_171_ = lean_ctor_get(v_x_166_, 2);
        lean_inc_ref(v_pivot_171_);
        v_rupHints_172_ = lean_ctor_get(v_x_166_, 3);
        lean_inc_ref(v_rupHints_172_);
        v_ratHints_173_ = lean_ctor_get(v_x_166_, 4);
        lean_inc_ref(v_ratHints_173_);
        lean_dec_ref_known(v_x_166_, 5);
        v___x_174_ = lean_apply_5(
            v_h__1_167_,
            v_id_169_,
            v_c_170_,
            v_pivot_171_,
            v_rupHints_172_,
            v_ratHints_173_,
        );
        return v___x_174_;
    } else {
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_167_);
        v___x_175_ = lean_apply_2(v_h__2_168_, v_x_166_, lean_box(0));
        return v___x_175_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_00_u03b2_177_: *mut LeanObject,
    mut v_motive_178_: *mut LeanObject,
    mut v_x_179_: *mut LeanObject,
    mut v_h__1_180_: *mut LeanObject,
    mut v_h__2_181_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_179_) == 2 {
        let mut v_id_182_: *mut LeanObject = core::ptr::null_mut();
        let mut v_c_183_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pivot_184_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rupHints_185_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ratHints_186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_181_);
        v_id_182_ = lean_ctor_get(v_x_179_, 0);
        lean_inc(v_id_182_);
        v_c_183_ = lean_ctor_get(v_x_179_, 1);
        lean_inc(v_c_183_);
        v_pivot_184_ = lean_ctor_get(v_x_179_, 2);
        lean_inc_ref(v_pivot_184_);
        v_rupHints_185_ = lean_ctor_get(v_x_179_, 3);
        lean_inc_ref(v_rupHints_185_);
        v_ratHints_186_ = lean_ctor_get(v_x_179_, 4);
        lean_inc_ref(v_ratHints_186_);
        lean_dec_ref_known(v_x_179_, 5);
        v___x_187_ = lean_apply_5(
            v_h__1_180_,
            v_id_182_,
            v_c_183_,
            v_pivot_184_,
            v_rupHints_185_,
            v_ratHints_186_,
        );
        return v___x_187_;
    } else {
        let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_180_);
        v___x_188_ = lean_apply_2(v_h__2_181_, v_x_179_, lean_box(0));
        return v___x_188_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
}
