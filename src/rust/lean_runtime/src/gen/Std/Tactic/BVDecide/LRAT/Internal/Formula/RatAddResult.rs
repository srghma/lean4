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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_4, lean_apply_6, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(
    mut v_f_72_: *mut LeanObject,
    mut v_h__1_73_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_75_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_74_ = lean_ctor_get(v_f_72_, 0);
    lean_inc_ref(v_clauses_74_);
    v_rupUnits_75_ = lean_ctor_get(v_f_72_, 1);
    lean_inc_ref(v_rupUnits_75_);
    v_ratUnits_76_ = lean_ctor_get(v_f_72_, 2);
    lean_inc_ref(v_ratUnits_76_);
    v_assignments_77_ = lean_ctor_get(v_f_72_, 3);
    lean_inc_ref(v_assignments_77_);
    lean_dec_ref(v_f_72_);
    v___x_78_ = lean_apply_4(
        v_h__1_73_,
        v_clauses_74_,
        v_rupUnits_75_,
        v_ratUnits_76_,
        v_assignments_77_,
    );
    return v___x_78_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(
    mut v_n_79_: *mut LeanObject,
    mut v_motive_80_: *mut LeanObject,
    mut v_f_81_: *mut LeanObject,
    mut v_h__1_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_85_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_83_ = lean_ctor_get(v_f_81_, 0);
    lean_inc_ref(v_clauses_83_);
    v_rupUnits_84_ = lean_ctor_get(v_f_81_, 1);
    lean_inc_ref(v_rupUnits_84_);
    v_ratUnits_85_ = lean_ctor_get(v_f_81_, 2);
    lean_inc_ref(v_ratUnits_85_);
    v_assignments_86_ = lean_ctor_get(v_f_81_, 3);
    lean_inc_ref(v_assignments_86_);
    lean_dec_ref(v_f_81_);
    v___x_87_ = lean_apply_4(
        v_h__1_82_,
        v_clauses_83_,
        v_rupUnits_84_,
        v_ratUnits_85_,
        v_assignments_86_,
    );
    return v___x_87_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(
    mut v_n_88_: *mut LeanObject,
    mut v_motive_89_: *mut LeanObject,
    mut v_f_90_: *mut LeanObject,
    mut v_h__1_91_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_92_: *mut LeanObject = core::ptr::null_mut();
    v_res_92_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_88_, v_motive_89_, v_f_90_, v_h__1_91_);
    lean_dec(v_n_88_);
    return v_res_92_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter___redArg(
    mut v_f_93_: *mut LeanObject,
    mut v_ratHint_94_: *mut LeanObject,
    mut v_h__1_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_96_ = lean_ctor_get(v_f_93_, 0);
    lean_inc_ref(v_clauses_96_);
    v_rupUnits_97_ = lean_ctor_get(v_f_93_, 1);
    lean_inc_ref(v_rupUnits_97_);
    v_ratUnits_98_ = lean_ctor_get(v_f_93_, 2);
    lean_inc_ref(v_ratUnits_98_);
    v_assignments_99_ = lean_ctor_get(v_f_93_, 3);
    lean_inc_ref(v_assignments_99_);
    lean_dec_ref(v_f_93_);
    v_fst_100_ = lean_ctor_get(v_ratHint_94_, 0);
    lean_inc(v_fst_100_);
    v_snd_101_ = lean_ctor_get(v_ratHint_94_, 1);
    lean_inc(v_snd_101_);
    lean_dec_ref(v_ratHint_94_);
    v___x_102_ = lean_apply_6(
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
    mut v_n_103_: *mut LeanObject,
    mut v_motive_104_: *mut LeanObject,
    mut v_f_105_: *mut LeanObject,
    mut v_ratHint_106_: *mut LeanObject,
    mut v_h__1_107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_108_ = lean_ctor_get(v_f_105_, 0);
    lean_inc_ref(v_clauses_108_);
    v_rupUnits_109_ = lean_ctor_get(v_f_105_, 1);
    lean_inc_ref(v_rupUnits_109_);
    v_ratUnits_110_ = lean_ctor_get(v_f_105_, 2);
    lean_inc_ref(v_ratUnits_110_);
    v_assignments_111_ = lean_ctor_get(v_f_105_, 3);
    lean_inc_ref(v_assignments_111_);
    lean_dec_ref(v_f_105_);
    v_fst_112_ = lean_ctor_get(v_ratHint_106_, 0);
    lean_inc(v_fst_112_);
    v_snd_113_ = lean_ctor_get(v_ratHint_106_, 1);
    lean_inc(v_snd_113_);
    lean_dec_ref(v_ratHint_106_);
    v___x_114_ = lean_apply_6(
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
    mut v_n_115_: *mut LeanObject,
    mut v_motive_116_: *mut LeanObject,
    mut v_f_117_: *mut LeanObject,
    mut v_ratHint_118_: *mut LeanObject,
    mut v_h__1_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__3_splitter(v_n_115_, v_motive_116_, v_f_117_, v_ratHint_118_, v_h__1_119_);
    lean_dec(v_n_115_);
    return v_res_120_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___redArg(
    mut v_x_121_: *mut LeanObject,
    mut v_h__1_122_: *mut LeanObject,
    mut v_h__2_123_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_121_) == 0 {
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_122_);
        v___x_124_ = lean_box(0);
        v___x_125_ = lean_apply_1(v_h__2_123_, v___x_124_);
        return v___x_125_;
    } else {
        let mut v_val_126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_123_);
        v_val_126_ = lean_ctor_get(v_x_121_, 0);
        lean_inc(v_val_126_);
        lean_dec_ref_known(v_x_121_, 1);
        v___x_127_ = lean_apply_1(v_h__1_122_, v_val_126_);
        return v___x_127_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(
    mut v_n_128_: *mut LeanObject,
    mut v_motive_129_: *mut LeanObject,
    mut v_x_130_: *mut LeanObject,
    mut v_h__1_131_: *mut LeanObject,
    mut v_h__2_132_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_130_) == 0 {
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_131_);
        v___x_133_ = lean_box(0);
        v___x_134_ = lean_apply_1(v_h__2_132_, v___x_133_);
        return v___x_134_;
    } else {
        let mut v_val_135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_132_);
        v_val_135_ = lean_ctor_get(v_x_130_, 0);
        lean_inc(v_val_135_);
        lean_dec_ref_known(v_x_130_, 1);
        v___x_136_ = lean_apply_1(v_h__1_131_, v_val_135_);
        return v___x_136_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter___boxed(
    mut v_n_137_: *mut LeanObject,
    mut v_motive_138_: *mut LeanObject,
    mut v_x_139_: *mut LeanObject,
    mut v_h__1_140_: *mut LeanObject,
    mut v_h__2_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_142_: *mut LeanObject = core::ptr::null_mut();
    v_res_142_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_match__1_splitter(v_n_137_, v_motive_138_, v_x_139_, v_h__1_140_, v_h__2_141_);
    lean_dec(v_n_137_);
    return v_res_142_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
}
