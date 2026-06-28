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
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(
    mut v_a_65_: u8,
    mut v_h__1_66_: *mut crate::leanh::LeanObject,
    mut v_h__2_67_: *mut crate::leanh::LeanObject,
    mut v_h__3_68_: *mut crate::leanh::LeanObject,
    mut v_h__4_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_a_65_ {
        0 => {
            let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_69_);
            crate::leanh::lean_dec(v_h__3_68_);
            crate::leanh::lean_dec(v_h__2_67_);
            v___x_70_ = crate::leanh::lean_box(0);
            v___x_71_ = crate::leanh::lean_apply_1(v_h__1_66_, v___x_70_);
            return v___x_71_;
        }
        1 => {
            let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_69_);
            crate::leanh::lean_dec(v_h__3_68_);
            crate::leanh::lean_dec(v_h__1_66_);
            v___x_72_ = crate::leanh::lean_box(0);
            v___x_73_ = crate::leanh::lean_apply_1(v_h__2_67_, v___x_72_);
            return v___x_73_;
        }
        2 => {
            let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_69_);
            crate::leanh::lean_dec(v_h__2_67_);
            crate::leanh::lean_dec(v_h__1_66_);
            v___x_74_ = crate::leanh::lean_box(0);
            v___x_75_ = crate::leanh::lean_apply_1(v_h__3_68_, v___x_74_);
            return v___x_75_;
        }
        _ => {
            let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_68_);
            crate::leanh::lean_dec(v_h__2_67_);
            crate::leanh::lean_dec(v_h__1_66_);
            v___x_76_ = crate::leanh::lean_box(0);
            v___x_77_ = crate::leanh::lean_apply_1(v_h__4_69_, v___x_76_);
            return v___x_77_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(
    mut v_a_78_: *mut crate::leanh::LeanObject,
    mut v_h__1_79_: *mut crate::leanh::LeanObject,
    mut v_h__2_80_: *mut crate::leanh::LeanObject,
    mut v_h__3_81_: *mut crate::leanh::LeanObject,
    mut v_h__4_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_46__boxed_83_: u8 = 0;
    let mut v_res_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_46__boxed_83_ = (crate::leanh::lean_unbox(v_a_78_) as u8);
    v_res_84_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_83_, v_h__1_79_, v_h__2_80_, v_h__3_81_, v_h__4_82_);
    return v_res_84_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(
    mut v_motive_85_: *mut crate::leanh::LeanObject,
    mut v_a_86_: u8,
    mut v_h__1_87_: *mut crate::leanh::LeanObject,
    mut v_h__2_88_: *mut crate::leanh::LeanObject,
    mut v_h__3_89_: *mut crate::leanh::LeanObject,
    mut v_h__4_90_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_a_86_ {
        0 => {
            let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_90_);
            crate::leanh::lean_dec(v_h__3_89_);
            crate::leanh::lean_dec(v_h__2_88_);
            v___x_91_ = crate::leanh::lean_box(0);
            v___x_92_ = crate::leanh::lean_apply_1(v_h__1_87_, v___x_91_);
            return v___x_92_;
        }
        1 => {
            let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_90_);
            crate::leanh::lean_dec(v_h__3_89_);
            crate::leanh::lean_dec(v_h__1_87_);
            v___x_93_ = crate::leanh::lean_box(0);
            v___x_94_ = crate::leanh::lean_apply_1(v_h__2_88_, v___x_93_);
            return v___x_94_;
        }
        2 => {
            let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_90_);
            crate::leanh::lean_dec(v_h__2_88_);
            crate::leanh::lean_dec(v_h__1_87_);
            v___x_95_ = crate::leanh::lean_box(0);
            v___x_96_ = crate::leanh::lean_apply_1(v_h__3_89_, v___x_95_);
            return v___x_96_;
        }
        _ => {
            let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_89_);
            crate::leanh::lean_dec(v_h__2_88_);
            crate::leanh::lean_dec(v_h__1_87_);
            v___x_97_ = crate::leanh::lean_box(0);
            v___x_98_ = crate::leanh::lean_apply_1(v_h__4_90_, v___x_97_);
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(
    mut v_motive_99_: *mut crate::leanh::LeanObject,
    mut v_a_100_: *mut crate::leanh::LeanObject,
    mut v_h__1_101_: *mut crate::leanh::LeanObject,
    mut v_h__2_102_: *mut crate::leanh::LeanObject,
    mut v_h__3_103_: *mut crate::leanh::LeanObject,
    mut v_h__4_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_65__boxed_105_: u8 = 0;
    let mut v_res_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_65__boxed_105_ = (crate::leanh::lean_unbox(v_a_100_) as u8);
    v_res_106_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_99_, v_a_65__boxed_105_, v_h__1_101_, v_h__2_102_, v_h__3_103_, v_h__4_104_);
    return v_res_106_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(
    mut v_cOpt_107_: *mut crate::leanh::LeanObject,
    mut v_h__1_108_: *mut crate::leanh::LeanObject,
    mut v_h__2_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_cOpt_107_) == 0 {
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_109_);
        v___x_110_ = crate::leanh::lean_box(0);
        v___x_111_ = crate::leanh::lean_apply_1(v_h__1_108_, v___x_110_);
        return v___x_111_;
    } else {
        let mut v_val_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_108_);
        v_val_112_ = crate::leanh::lean_ctor_get(v_cOpt_107_, 0);
        crate::leanh::lean_inc(v_val_112_);
        crate::leanh::lean_dec_ref_known(v_cOpt_107_, 1);
        v___x_113_ = crate::leanh::lean_apply_1(v_h__2_109_, v_val_112_);
        return v___x_113_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(
    mut v_n_114_: *mut crate::leanh::LeanObject,
    mut v_motive_115_: *mut crate::leanh::LeanObject,
    mut v_cOpt_116_: *mut crate::leanh::LeanObject,
    mut v_h__1_117_: *mut crate::leanh::LeanObject,
    mut v_h__2_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_cOpt_116_) == 0 {
        let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_118_);
        v___x_119_ = crate::leanh::lean_box(0);
        v___x_120_ = crate::leanh::lean_apply_1(v_h__1_117_, v___x_119_);
        return v___x_120_;
    } else {
        let mut v_val_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_117_);
        v_val_121_ = crate::leanh::lean_ctor_get(v_cOpt_116_, 0);
        crate::leanh::lean_inc(v_val_121_);
        crate::leanh::lean_dec_ref_known(v_cOpt_116_, 1);
        v___x_122_ = crate::leanh::lean_apply_1(v_h__2_118_, v_val_121_);
        return v___x_122_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(
    mut v_n_123_: *mut crate::leanh::LeanObject,
    mut v_motive_124_: *mut crate::leanh::LeanObject,
    mut v_cOpt_125_: *mut crate::leanh::LeanObject,
    mut v_h__1_126_: *mut crate::leanh::LeanObject,
    mut v_h__2_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_123_, v_motive_124_, v_cOpt_125_, v_h__1_126_, v_h__2_127_);
    crate::leanh::lean_dec(v_n_123_);
    return v_res_128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Range(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Range(builtin);
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
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
}
