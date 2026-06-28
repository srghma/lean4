// Lean compiler output
// Module: Init.Data.Rat.Lemmas
// Imports: Init.Data.Rat.Basic Init.Data.Int.Gcd Init.ByCases Init.Data.Bool Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.Data.Nat.Dvd Init.Omega Init.TacticsExtra
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Gcd::{
    initialize_Init_Data_Int_Gcd, runtime_initialize_Init_Data_Int_Gcd,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    initialize_Init_Data_Rat_Basic, runtime_initialize_Init_Data_Rat_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_sub;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_77_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_76_ = lean_unsigned_to_nat(0);
    v_intZero_77_ = lean_nat_to_int(v_natZero_76_);
    return v_intZero_77_;
}
pub unsafe fn l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(
    mut v_x_78_: *mut LeanObject,
    mut v_x_79_: *mut LeanObject,
    mut v_h__1_80_: *mut LeanObject,
    mut v_h__2_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_83_: u8 = 0;
    v_intZero_82_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0);
    v_isNeg_83_ = lean_int_dec_lt(v_x_79_, v_intZero_82_);
    if v_isNeg_83_ == 0 {
        let mut v_a_84_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_81_);
        v_a_84_ = lean_nat_abs(v_x_79_);
        v___x_85_ = lean_apply_2(v_h__1_80_, v_x_78_, v_a_84_);
        return v___x_85_;
    } else {
        let mut v_abs_86_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_80_);
        v_abs_86_ = lean_nat_abs(v_x_79_);
        v_one_87_ = lean_unsigned_to_nat(1);
        v_a_88_ = lean_nat_sub(v_abs_86_, v_one_87_);
        lean_dec(v_abs_86_);
        v___x_89_ = lean_apply_2(v_h__2_81_, v_x_78_, v_a_88_);
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___boxed(
    mut v_x_90_: *mut LeanObject,
    mut v_x_91_: *mut LeanObject,
    mut v_h__1_92_: *mut LeanObject,
    mut v_h__2_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(
        v_x_90_, v_x_91_, v_h__1_92_, v_h__2_93_,
    );
    lean_dec(v_x_91_);
    return v_res_94_;
}
pub unsafe fn l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(
    mut v_motive_95_: *mut LeanObject,
    mut v_x_96_: *mut LeanObject,
    mut v_x_97_: *mut LeanObject,
    mut v_h__1_98_: *mut LeanObject,
    mut v_h__2_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_101_: u8 = 0;
    v_intZero_100_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0);
    v_isNeg_101_ = lean_int_dec_lt(v_x_97_, v_intZero_100_);
    if v_isNeg_101_ == 0 {
        let mut v_a_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_99_);
        v_a_102_ = lean_nat_abs(v_x_97_);
        v___x_103_ = lean_apply_2(v_h__1_98_, v_x_96_, v_a_102_);
        return v___x_103_;
    } else {
        let mut v_abs_104_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_105_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_98_);
        v_abs_104_ = lean_nat_abs(v_x_97_);
        v_one_105_ = lean_unsigned_to_nat(1);
        v_a_106_ = lean_nat_sub(v_abs_104_, v_one_105_);
        lean_dec(v_abs_104_);
        v___x_107_ = lean_apply_2(v_h__2_99_, v_x_96_, v_a_106_);
        return v___x_107_;
    }
}
pub unsafe fn l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___boxed(
    mut v_motive_108_: *mut LeanObject,
    mut v_x_109_: *mut LeanObject,
    mut v_x_110_: *mut LeanObject,
    mut v_h__1_111_: *mut LeanObject,
    mut v_h__2_112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_113_: *mut LeanObject = core::ptr::null_mut();
    v_res_113_ = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(
        v_motive_108_,
        v_x_109_,
        v_x_110_,
        v_h__1_111_,
        v_h__2_112_,
    );
    lean_dec(v_x_110_);
    return v_res_113_;
}
pub unsafe fn l_Rat_numDenCasesOn___redArg(
    mut v_x_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_num_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
    v_num_116_ = lean_ctor_get(v_x_114_, 0);
    lean_inc(v_num_116_);
    v_den_117_ = lean_ctor_get(v_x_114_, 1);
    lean_inc(v_den_117_);
    lean_dec_ref(v_x_114_);
    v___x_118_ = lean_apply_4(v_x_115_, v_num_116_, v_den_117_, lean_box(0), lean_box(0));
    return v___x_118_;
}
pub unsafe fn l_Rat_numDenCasesOn(
    mut v_C_119_: *mut LeanObject,
    mut v_x_120_: *mut LeanObject,
    mut v_x_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    v___x_122_ = l_Rat_numDenCasesOn___redArg(v_x_120_, v_x_121_);
    return v___x_122_;
}
pub unsafe fn l_Rat_numDenCasesOn_x27___redArg___lam__0(
    mut v_H_123_: *mut LeanObject,
    mut v_n_124_: *mut LeanObject,
    mut v_d_125_: *mut LeanObject,
    mut v_h_126_: *mut LeanObject,
    mut v_x_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    v___x_128_ = lean_apply_3(v_H_123_, v_n_124_, v_d_125_, lean_box(0));
    return v___x_128_;
}
pub unsafe fn l_Rat_numDenCasesOn_x27___redArg(
    mut v_a_129_: *mut LeanObject,
    mut v_H_130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    v___f_131_ = lean_alloc_closure(
        l_Rat_numDenCasesOn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_131_, 0, v_H_130_);
    v___x_132_ = l_Rat_numDenCasesOn___redArg(v_a_129_, v___f_131_);
    return v___x_132_;
}
pub unsafe fn l_Rat_numDenCasesOn_x27(
    mut v_C_133_: *mut LeanObject,
    mut v_a_134_: *mut LeanObject,
    mut v_H_135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    v___x_136_ = l_Rat_numDenCasesOn_x27___redArg(v_a_134_, v_H_135_);
    return v___x_136_;
}
pub unsafe fn l_Rat_numDenCasesOn_x27_x27___redArg___lam__0(
    mut v_H_137_: *mut LeanObject,
    mut v_n_138_: *mut LeanObject,
    mut v_d_139_: *mut LeanObject,
    mut v_h_140_: *mut LeanObject,
    mut v_h_x27_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    v___x_142_ = lean_apply_4(v_H_137_, v_n_138_, v_d_139_, lean_box(0), lean_box(0));
    return v___x_142_;
}
pub unsafe fn l_Rat_numDenCasesOn_x27_x27___redArg(
    mut v_a_143_: *mut LeanObject,
    mut v_H_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    v___f_145_ = lean_alloc_closure(
        l_Rat_numDenCasesOn_x27_x27___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_145_, 0, v_H_144_);
    v___x_146_ = l_Rat_numDenCasesOn___redArg(v_a_143_, v___f_145_);
    return v___x_146_;
}
pub unsafe fn l_Rat_numDenCasesOn_x27_x27(
    mut v_C_147_: *mut LeanObject,
    mut v_a_148_: *mut LeanObject,
    mut v_H_149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    v___x_150_ = l_Rat_numDenCasesOn_x27_x27___redArg(v_a_148_, v_H_149_);
    return v___x_150_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Rat_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Rat_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Rat_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Rat_Lemmas(builtin);
}
