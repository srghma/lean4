// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound Init.ByCases Init.Data.Int.OfNat Init.Data.Nat.Linear
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RupAddSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(
    mut v_f_72_: *mut crate::leanh::LeanObject,
    mut v_h__1_73_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clauses_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clauses_74_ = crate::leanh::lean_ctor_get(v_f_72_, 0);
    crate::leanh::lean_inc_ref(v_clauses_74_);
    v_rupUnits_75_ = crate::leanh::lean_ctor_get(v_f_72_, 1);
    crate::leanh::lean_inc_ref(v_rupUnits_75_);
    v_ratUnits_76_ = crate::leanh::lean_ctor_get(v_f_72_, 2);
    crate::leanh::lean_inc_ref(v_ratUnits_76_);
    v_assignments_77_ = crate::leanh::lean_ctor_get(v_f_72_, 3);
    crate::leanh::lean_inc_ref(v_assignments_77_);
    crate::leanh::lean_dec_ref(v_f_72_);
    v___x_78_ = crate::leanh::lean_apply_4(
        v_h__1_73_,
        v_clauses_74_,
        v_rupUnits_75_,
        v_ratUnits_76_,
        v_assignments_77_,
    );
    return v___x_78_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(
    mut v_n_79_: *mut crate::leanh::LeanObject,
    mut v_motive_80_: *mut crate::leanh::LeanObject,
    mut v_f_81_: *mut crate::leanh::LeanObject,
    mut v_h__1_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clauses_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clauses_83_ = crate::leanh::lean_ctor_get(v_f_81_, 0);
    crate::leanh::lean_inc_ref(v_clauses_83_);
    v_rupUnits_84_ = crate::leanh::lean_ctor_get(v_f_81_, 1);
    crate::leanh::lean_inc_ref(v_rupUnits_84_);
    v_ratUnits_85_ = crate::leanh::lean_ctor_get(v_f_81_, 2);
    crate::leanh::lean_inc_ref(v_ratUnits_85_);
    v_assignments_86_ = crate::leanh::lean_ctor_get(v_f_81_, 3);
    crate::leanh::lean_inc_ref(v_assignments_86_);
    crate::leanh::lean_dec_ref(v_f_81_);
    v___x_87_ = crate::leanh::lean_apply_4(
        v_h__1_82_,
        v_clauses_83_,
        v_rupUnits_84_,
        v_ratUnits_85_,
        v_assignments_86_,
    );
    return v___x_87_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(
    mut v_n_88_: *mut crate::leanh::LeanObject,
    mut v_motive_89_: *mut crate::leanh::LeanObject,
    mut v_f_90_: *mut crate::leanh::LeanObject,
    mut v_h__1_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_88_, v_motive_89_, v_f_90_, v_h__1_91_);
    crate::leanh::lean_dec(v_n_88_);
    return v_res_92_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___redArg(
    mut v_f_93_: *mut crate::leanh::LeanObject,
    mut v_ratHint_94_: *mut crate::leanh::LeanObject,
    mut v_h__1_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clauses_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clauses_96_ = crate::leanh::lean_ctor_get(v_f_93_, 0);
    crate::leanh::lean_inc_ref(v_clauses_96_);
    v_rupUnits_97_ = crate::leanh::lean_ctor_get(v_f_93_, 1);
    crate::leanh::lean_inc_ref(v_rupUnits_97_);
    v_ratUnits_98_ = crate::leanh::lean_ctor_get(v_f_93_, 2);
    crate::leanh::lean_inc_ref(v_ratUnits_98_);
    v_assignments_99_ = crate::leanh::lean_ctor_get(v_f_93_, 3);
    crate::leanh::lean_inc_ref(v_assignments_99_);
    crate::leanh::lean_dec_ref(v_f_93_);
    v_fst_100_ = crate::leanh::lean_ctor_get(v_ratHint_94_, 0);
    crate::leanh::lean_inc(v_fst_100_);
    v_snd_101_ = crate::leanh::lean_ctor_get(v_ratHint_94_, 1);
    crate::leanh::lean_inc(v_snd_101_);
    crate::leanh::lean_dec_ref(v_ratHint_94_);
    v___x_102_ = crate::leanh::lean_apply_6(
        v_h__1_95_,
        v_clauses_96_,
        v_rupUnits_97_,
        v_ratUnits_98_,
        v_assignments_99_,
        v_fst_100_,
        v_snd_101_,
    );
    return v___x_102_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(
    mut v_n_103_: *mut crate::leanh::LeanObject,
    mut v_motive_104_: *mut crate::leanh::LeanObject,
    mut v_f_105_: *mut crate::leanh::LeanObject,
    mut v_ratHint_106_: *mut crate::leanh::LeanObject,
    mut v_h__1_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clauses_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clauses_108_ = crate::leanh::lean_ctor_get(v_f_105_, 0);
    crate::leanh::lean_inc_ref(v_clauses_108_);
    v_rupUnits_109_ = crate::leanh::lean_ctor_get(v_f_105_, 1);
    crate::leanh::lean_inc_ref(v_rupUnits_109_);
    v_ratUnits_110_ = crate::leanh::lean_ctor_get(v_f_105_, 2);
    crate::leanh::lean_inc_ref(v_ratUnits_110_);
    v_assignments_111_ = crate::leanh::lean_ctor_get(v_f_105_, 3);
    crate::leanh::lean_inc_ref(v_assignments_111_);
    crate::leanh::lean_dec_ref(v_f_105_);
    v_fst_112_ = crate::leanh::lean_ctor_get(v_ratHint_106_, 0);
    crate::leanh::lean_inc(v_fst_112_);
    v_snd_113_ = crate::leanh::lean_ctor_get(v_ratHint_106_, 1);
    crate::leanh::lean_inc(v_snd_113_);
    crate::leanh::lean_dec_ref(v_ratHint_106_);
    v___x_114_ = crate::leanh::lean_apply_6(
        v_h__1_107_,
        v_clauses_108_,
        v_rupUnits_109_,
        v_ratUnits_110_,
        v_assignments_111_,
        v_fst_112_,
        v_snd_113_,
    );
    return v___x_114_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___boxed(
    mut v_n_115_: *mut crate::leanh::LeanObject,
    mut v_motive_116_: *mut crate::leanh::LeanObject,
    mut v_f_117_: *mut crate::leanh::LeanObject,
    mut v_ratHint_118_: *mut crate::leanh::LeanObject,
    mut v_h__1_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(v_n_115_, v_motive_116_, v_f_117_, v_ratHint_118_, v_h__1_119_);
    crate::leanh::lean_dec(v_n_115_);
    return v_res_120_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___redArg(
    mut v_x_121_: *mut crate::leanh::LeanObject,
    mut v_h__1_122_: *mut crate::leanh::LeanObject,
    mut v_h__2_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_121_) == 0 {
        let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_122_);
        v___x_124_ = crate::leanh::lean_box(0);
        v___x_125_ = crate::leanh::lean_apply_1(v_h__2_123_, v___x_124_);
        return v___x_125_;
    } else {
        let mut v_val_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_123_);
        v_val_126_ = crate::leanh::lean_ctor_get(v_x_121_, 0);
        crate::leanh::lean_inc(v_val_126_);
        crate::leanh::lean_dec_ref_known(v_x_121_, 1);
        v___x_127_ = crate::leanh::lean_apply_1(v_h__1_122_, v_val_126_);
        return v___x_127_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(
    mut v_n_128_: *mut crate::leanh::LeanObject,
    mut v_motive_129_: *mut crate::leanh::LeanObject,
    mut v_x_130_: *mut crate::leanh::LeanObject,
    mut v_h__1_131_: *mut crate::leanh::LeanObject,
    mut v_h__2_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_130_) == 0 {
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_131_);
        v___x_133_ = crate::leanh::lean_box(0);
        v___x_134_ = crate::leanh::lean_apply_1(v_h__2_132_, v___x_133_);
        return v___x_134_;
    } else {
        let mut v_val_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_132_);
        v_val_135_ = crate::leanh::lean_ctor_get(v_x_130_, 0);
        crate::leanh::lean_inc(v_val_135_);
        crate::leanh::lean_dec_ref_known(v_x_130_, 1);
        v___x_136_ = crate::leanh::lean_apply_1(v_h__1_131_, v_val_135_);
        return v___x_136_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___boxed(
    mut v_n_137_: *mut crate::leanh::LeanObject,
    mut v_motive_138_: *mut crate::leanh::LeanObject,
    mut v_x_139_: *mut crate::leanh::LeanObject,
    mut v_h__1_140_: *mut crate::leanh::LeanObject,
    mut v_h__2_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(v_n_137_, v_motive_138_, v_x_139_, v_h__1_140_, v_h__2_141_);
    crate::leanh::lean_dec(v_n_137_);
    return v_res_142_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
}
