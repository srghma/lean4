// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATCheckerSound
// Imports: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CompactLRATChecker::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATCheckerSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_5,
    lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(
    mut v_step_77_: *mut LeanObject,
    mut v_h__1_78_: *mut LeanObject,
    mut v_h__2_79_: *mut LeanObject,
    mut v_h__3_80_: *mut LeanObject,
    mut v_h__4_81_: *mut LeanObject,
    mut v_h__5_82_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_77_) == 0 {
        let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__5_82_);
        lean_dec(v_h__4_81_);
        lean_dec(v_h__3_80_);
        lean_dec(v_h__2_79_);
        v___x_83_ = lean_box(0);
        v___x_84_ = lean_apply_1(v_h__1_78_, v___x_83_);
        return v___x_84_;
    } else {
        let mut v_val_85_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_78_);
        v_val_85_ = lean_ctor_get(v_step_77_, 0);
        lean_inc(v_val_85_);
        lean_dec_ref_known(v_step_77_, 1);
        match lean_obj_tag(v_val_85_) {
            0 => {
                let mut v_id_86_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_87_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_82_);
                lean_dec(v_h__4_81_);
                lean_dec(v_h__3_80_);
                v_id_86_ = lean_ctor_get(v_val_85_, 0);
                lean_inc(v_id_86_);
                v_rupHints_87_ = lean_ctor_get(v_val_85_, 1);
                lean_inc_ref(v_rupHints_87_);
                lean_dec_ref_known(v_val_85_, 2);
                v___x_88_ = lean_apply_2(v_h__2_79_, v_id_86_, v_rupHints_87_);
                return v___x_88_;
            }
            1 => {
                let mut v_id_89_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_90_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_91_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_82_);
                lean_dec(v_h__4_81_);
                lean_dec(v_h__2_79_);
                v_id_89_ = lean_ctor_get(v_val_85_, 0);
                lean_inc(v_id_89_);
                v_c_90_ = lean_ctor_get(v_val_85_, 1);
                lean_inc(v_c_90_);
                v_rupHints_91_ = lean_ctor_get(v_val_85_, 2);
                lean_inc_ref(v_rupHints_91_);
                lean_dec_ref_known(v_val_85_, 3);
                v___x_92_ = lean_apply_3(v_h__3_80_, v_id_89_, v_c_90_, v_rupHints_91_);
                return v___x_92_;
            }
            2 => {
                let mut v_id_93_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_94_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pivot_95_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_96_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ratHints_97_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_82_);
                lean_dec(v_h__3_80_);
                lean_dec(v_h__2_79_);
                v_id_93_ = lean_ctor_get(v_val_85_, 0);
                lean_inc(v_id_93_);
                v_c_94_ = lean_ctor_get(v_val_85_, 1);
                lean_inc(v_c_94_);
                v_pivot_95_ = lean_ctor_get(v_val_85_, 2);
                lean_inc_ref(v_pivot_95_);
                v_rupHints_96_ = lean_ctor_get(v_val_85_, 3);
                lean_inc_ref(v_rupHints_96_);
                v_ratHints_97_ = lean_ctor_get(v_val_85_, 4);
                lean_inc_ref(v_ratHints_97_);
                lean_dec_ref_known(v_val_85_, 5);
                v___x_98_ = lean_apply_5(
                    v_h__4_81_,
                    v_id_93_,
                    v_c_94_,
                    v_pivot_95_,
                    v_rupHints_96_,
                    v_ratHints_97_,
                );
                return v___x_98_;
            }
            _ => {
                let mut v_ids_99_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_81_);
                lean_dec(v_h__3_80_);
                lean_dec(v_h__2_79_);
                v_ids_99_ = lean_ctor_get(v_val_85_, 0);
                lean_inc_ref(v_ids_99_);
                lean_dec_ref_known(v_val_85_, 1);
                v___x_100_ = lean_apply_1(v_h__5_82_, v_ids_99_);
                return v___x_100_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(
    mut v_n_101_: *mut LeanObject,
    mut v_motive_102_: *mut LeanObject,
    mut v_step_103_: *mut LeanObject,
    mut v_h__1_104_: *mut LeanObject,
    mut v_h__2_105_: *mut LeanObject,
    mut v_h__3_106_: *mut LeanObject,
    mut v_h__4_107_: *mut LeanObject,
    mut v_h__5_108_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_103_) == 0 {
        let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__5_108_);
        lean_dec(v_h__4_107_);
        lean_dec(v_h__3_106_);
        lean_dec(v_h__2_105_);
        v___x_109_ = lean_box(0);
        v___x_110_ = lean_apply_1(v_h__1_104_, v___x_109_);
        return v___x_110_;
    } else {
        let mut v_val_111_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_104_);
        v_val_111_ = lean_ctor_get(v_step_103_, 0);
        lean_inc(v_val_111_);
        lean_dec_ref_known(v_step_103_, 1);
        match lean_obj_tag(v_val_111_) {
            0 => {
                let mut v_id_112_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_113_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_108_);
                lean_dec(v_h__4_107_);
                lean_dec(v_h__3_106_);
                v_id_112_ = lean_ctor_get(v_val_111_, 0);
                lean_inc(v_id_112_);
                v_rupHints_113_ = lean_ctor_get(v_val_111_, 1);
                lean_inc_ref(v_rupHints_113_);
                lean_dec_ref_known(v_val_111_, 2);
                v___x_114_ = lean_apply_2(v_h__2_105_, v_id_112_, v_rupHints_113_);
                return v___x_114_;
            }
            1 => {
                let mut v_id_115_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_116_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_117_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_108_);
                lean_dec(v_h__4_107_);
                lean_dec(v_h__2_105_);
                v_id_115_ = lean_ctor_get(v_val_111_, 0);
                lean_inc(v_id_115_);
                v_c_116_ = lean_ctor_get(v_val_111_, 1);
                lean_inc(v_c_116_);
                v_rupHints_117_ = lean_ctor_get(v_val_111_, 2);
                lean_inc_ref(v_rupHints_117_);
                lean_dec_ref_known(v_val_111_, 3);
                v___x_118_ = lean_apply_3(v_h__3_106_, v_id_115_, v_c_116_, v_rupHints_117_);
                return v___x_118_;
            }
            2 => {
                let mut v_id_119_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_120_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pivot_121_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_122_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ratHints_123_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_108_);
                lean_dec(v_h__3_106_);
                lean_dec(v_h__2_105_);
                v_id_119_ = lean_ctor_get(v_val_111_, 0);
                lean_inc(v_id_119_);
                v_c_120_ = lean_ctor_get(v_val_111_, 1);
                lean_inc(v_c_120_);
                v_pivot_121_ = lean_ctor_get(v_val_111_, 2);
                lean_inc_ref(v_pivot_121_);
                v_rupHints_122_ = lean_ctor_get(v_val_111_, 3);
                lean_inc_ref(v_rupHints_122_);
                v_ratHints_123_ = lean_ctor_get(v_val_111_, 4);
                lean_inc_ref(v_ratHints_123_);
                lean_dec_ref_known(v_val_111_, 5);
                v___x_124_ = lean_apply_5(
                    v_h__4_107_,
                    v_id_119_,
                    v_c_120_,
                    v_pivot_121_,
                    v_rupHints_122_,
                    v_ratHints_123_,
                );
                return v___x_124_;
            }
            _ => {
                let mut v_ids_125_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_107_);
                lean_dec(v_h__3_106_);
                lean_dec(v_h__2_105_);
                v_ids_125_ = lean_ctor_get(v_val_111_, 0);
                lean_inc_ref(v_ids_125_);
                lean_dec_ref_known(v_val_111_, 1);
                v___x_126_ = lean_apply_1(v_h__5_108_, v_ids_125_);
                return v___x_126_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(
    mut v_n_127_: *mut LeanObject,
    mut v_motive_128_: *mut LeanObject,
    mut v_step_129_: *mut LeanObject,
    mut v_h__1_130_: *mut LeanObject,
    mut v_h__2_131_: *mut LeanObject,
    mut v_h__3_132_: *mut LeanObject,
    mut v_h__4_133_: *mut LeanObject,
    mut v_h__5_134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_135_: *mut LeanObject = core::ptr::null_mut();
    v_res_135_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_127_, v_motive_128_, v_step_129_, v_h__1_130_, v_h__2_131_, v_h__3_132_, v_h__4_133_, v_h__5_134_);
    lean_dec(v_n_127_);
    return v_res_135_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(
    mut v_x_136_: *mut LeanObject,
    mut v_h__1_137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    v_fst_138_ = lean_ctor_get(v_x_136_, 0);
    lean_inc(v_fst_138_);
    v_snd_139_ = lean_ctor_get(v_x_136_, 1);
    lean_inc(v_snd_139_);
    lean_dec_ref(v_x_136_);
    v___x_140_ = lean_apply_2(v_h__1_137_, v_fst_138_, v_snd_139_);
    return v___x_140_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(
    mut v_n_141_: *mut LeanObject,
    mut v_motive_142_: *mut LeanObject,
    mut v_x_143_: *mut LeanObject,
    mut v_h__1_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    v_fst_145_ = lean_ctor_get(v_x_143_, 0);
    lean_inc(v_fst_145_);
    v_snd_146_ = lean_ctor_get(v_x_143_, 1);
    lean_inc(v_snd_146_);
    lean_dec_ref(v_x_143_);
    v___x_147_ = lean_apply_2(v_h__1_144_, v_fst_145_, v_snd_146_);
    return v___x_147_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(
    mut v_n_148_: *mut LeanObject,
    mut v_motive_149_: *mut LeanObject,
    mut v_x_150_: *mut LeanObject,
    mut v_h__1_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_152_: *mut LeanObject = core::ptr::null_mut();
    v_res_152_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_148_, v_motive_149_, v_x_150_, v_h__1_151_);
    lean_dec(v_n_148_);
    return v_res_152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
}
