// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult Init.ByCases Init.Data.Array.Range Init.Data.Int.OfNat Init.Data.Nat.Linear
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Range::{
    initialize_Init_Data_Array_Range, runtime_initialize_Init_Data_Array_Range,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RatAddResult::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
    lean_unbox,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(
    mut v_a_65_: u8,
    mut v_h__1_66_: *mut LeanObject,
    mut v_h__2_67_: *mut LeanObject,
    mut v_h__3_68_: *mut LeanObject,
    mut v_h__4_69_: *mut LeanObject,
) -> *mut LeanObject {
    match v_a_65_ {
        0 => {
            let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_69_);
            lean_dec(v_h__3_68_);
            lean_dec(v_h__2_67_);
            v___x_70_ = lean_box(0);
            v___x_71_ = lean_apply_1(v_h__1_66_, v___x_70_);
            return v___x_71_;
        }
        1 => {
            let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_69_);
            lean_dec(v_h__3_68_);
            lean_dec(v_h__1_66_);
            v___x_72_ = lean_box(0);
            v___x_73_ = lean_apply_1(v_h__2_67_, v___x_72_);
            return v___x_73_;
        }
        2 => {
            let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_69_);
            lean_dec(v_h__2_67_);
            lean_dec(v_h__1_66_);
            v___x_74_ = lean_box(0);
            v___x_75_ = lean_apply_1(v_h__3_68_, v___x_74_);
            return v___x_75_;
        }
        _ => {
            let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_68_);
            lean_dec(v_h__2_67_);
            lean_dec(v_h__1_66_);
            v___x_76_ = lean_box(0);
            v___x_77_ = lean_apply_1(v_h__4_69_, v___x_76_);
            return v___x_77_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(
    mut v_a_78_: *mut LeanObject,
    mut v_h__1_79_: *mut LeanObject,
    mut v_h__2_80_: *mut LeanObject,
    mut v_h__3_81_: *mut LeanObject,
    mut v_h__4_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_46__boxed_83_: u8 = 0;
    let mut v_res_84_: *mut LeanObject = core::ptr::null_mut();
    v_a_46__boxed_83_ = (lean_unbox(v_a_78_) as u8);
    v_res_84_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_83_, v_h__1_79_, v_h__2_80_, v_h__3_81_, v_h__4_82_);
    return v_res_84_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(
    mut v_motive_85_: *mut LeanObject,
    mut v_a_86_: u8,
    mut v_h__1_87_: *mut LeanObject,
    mut v_h__2_88_: *mut LeanObject,
    mut v_h__3_89_: *mut LeanObject,
    mut v_h__4_90_: *mut LeanObject,
) -> *mut LeanObject {
    match v_a_86_ {
        0 => {
            let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_90_);
            lean_dec(v_h__3_89_);
            lean_dec(v_h__2_88_);
            v___x_91_ = lean_box(0);
            v___x_92_ = lean_apply_1(v_h__1_87_, v___x_91_);
            return v___x_92_;
        }
        1 => {
            let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_90_);
            lean_dec(v_h__3_89_);
            lean_dec(v_h__1_87_);
            v___x_93_ = lean_box(0);
            v___x_94_ = lean_apply_1(v_h__2_88_, v___x_93_);
            return v___x_94_;
        }
        2 => {
            let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_90_);
            lean_dec(v_h__2_88_);
            lean_dec(v_h__1_87_);
            v___x_95_ = lean_box(0);
            v___x_96_ = lean_apply_1(v_h__3_89_, v___x_95_);
            return v___x_96_;
        }
        _ => {
            let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_89_);
            lean_dec(v_h__2_88_);
            lean_dec(v_h__1_87_);
            v___x_97_ = lean_box(0);
            v___x_98_ = lean_apply_1(v_h__4_90_, v___x_97_);
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(
    mut v_motive_99_: *mut LeanObject,
    mut v_a_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
    mut v_h__3_103_: *mut LeanObject,
    mut v_h__4_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_65__boxed_105_: u8 = 0;
    let mut v_res_106_: *mut LeanObject = core::ptr::null_mut();
    v_a_65__boxed_105_ = (lean_unbox(v_a_100_) as u8);
    v_res_106_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_99_, v_a_65__boxed_105_, v_h__1_101_, v_h__2_102_, v_h__3_103_, v_h__4_104_);
    return v_res_106_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(
    mut v_cOpt_107_: *mut LeanObject,
    mut v_h__1_108_: *mut LeanObject,
    mut v_h__2_109_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_cOpt_107_) == 0 {
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_109_);
        v___x_110_ = lean_box(0);
        v___x_111_ = lean_apply_1(v_h__1_108_, v___x_110_);
        return v___x_111_;
    } else {
        let mut v_val_112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_108_);
        v_val_112_ = lean_ctor_get(v_cOpt_107_, 0);
        lean_inc(v_val_112_);
        lean_dec_ref_known(v_cOpt_107_, 1);
        v___x_113_ = lean_apply_1(v_h__2_109_, v_val_112_);
        return v___x_113_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(
    mut v_n_114_: *mut LeanObject,
    mut v_motive_115_: *mut LeanObject,
    mut v_cOpt_116_: *mut LeanObject,
    mut v_h__1_117_: *mut LeanObject,
    mut v_h__2_118_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_cOpt_116_) == 0 {
        let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_118_);
        v___x_119_ = lean_box(0);
        v___x_120_ = lean_apply_1(v_h__1_117_, v___x_119_);
        return v___x_120_;
    } else {
        let mut v_val_121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_117_);
        v_val_121_ = lean_ctor_get(v_cOpt_116_, 0);
        lean_inc(v_val_121_);
        lean_dec_ref_known(v_cOpt_116_, 1);
        v___x_122_ = lean_apply_1(v_h__2_118_, v_val_121_);
        return v___x_122_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(
    mut v_n_123_: *mut LeanObject,
    mut v_motive_124_: *mut LeanObject,
    mut v_cOpt_125_: *mut LeanObject,
    mut v_h__1_126_: *mut LeanObject,
    mut v_h__2_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_128_: *mut LeanObject = core::ptr::null_mut();
    v_res_128_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_123_, v_motive_124_, v_cOpt_125_, v_h__1_126_, v_h__2_127_);
    lean_dec(v_n_123_);
    return v_res_128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Range(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Range(builtin);
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
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
}
