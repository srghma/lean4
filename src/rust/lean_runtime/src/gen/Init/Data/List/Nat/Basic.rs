// Lean compiler output
// Module: Init.Data.List.Nat.Basic
// Imports: Init.Data.List.MinMax Init.Data.Bool Init.Data.List.Count Init.Data.Nat.Lemmas Init.Data.Nat.Linear Init.Data.Nat.MinMax Init.Data.Option.Lemmas Init.Omega
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Count::{
    initialize_Init_Data_List_Count, runtime_initialize_Init_Data_List_Count,
};
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_71_: *mut LeanObject,
    mut v_h__1_72_: *mut LeanObject,
    mut v_h__2_73_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_71_) == 0 {
        let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_73_);
        v___x_74_ = lean_box(0);
        v___x_75_ = lean_apply_1(v_h__1_72_, v___x_74_);
        return v___x_75_;
    } else {
        let mut v_val_76_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_72_);
        v_val_76_ = lean_ctor_get(v_x_71_, 0);
        lean_inc(v_val_76_);
        lean_dec_ref_known(v_x_71_, 1);
        v___x_77_ = lean_apply_1(v_h__2_73_, v_val_76_);
        return v___x_77_;
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_78_: *mut LeanObject,
    mut v_motive_79_: *mut LeanObject,
    mut v_x_80_: *mut LeanObject,
    mut v_h__1_81_: *mut LeanObject,
    mut v_h__2_82_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_80_) == 0 {
        let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_82_);
        v___x_83_ = lean_box(0);
        v___x_84_ = lean_apply_1(v_h__1_81_, v___x_83_);
        return v___x_84_;
    } else {
        let mut v_val_85_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_81_);
        v_val_85_ = lean_ctor_get(v_x_80_, 0);
        lean_inc(v_val_85_);
        lean_dec_ref_known(v_x_80_, 1);
        v___x_86_ = lean_apply_1(v_h__2_82_, v_val_85_);
        return v___x_86_;
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(
    mut v_x_87_: *mut LeanObject,
    mut v_h__1_88_: *mut LeanObject,
    mut v_h__2_89_: *mut LeanObject,
    mut v_h__3_90_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_87_) == 0 {
        let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_90_);
        lean_dec(v_h__2_89_);
        v___x_91_ = lean_box(0);
        v___x_92_ = lean_apply_1(v_h__1_88_, v___x_91_);
        return v___x_92_;
    } else {
        let mut v_tail_93_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_88_);
        v_tail_93_ = lean_ctor_get(v_x_87_, 1);
        if lean_obj_tag(v_tail_93_) == 0 {
            let mut v_head_94_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_90_);
            v_head_94_ = lean_ctor_get(v_x_87_, 0);
            lean_inc(v_head_94_);
            lean_dec_ref_known(v_x_87_, 2);
            v___x_95_ = lean_apply_1(v_h__2_89_, v_head_94_);
            return v___x_95_;
        } else {
            let mut v_head_96_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_93_);
            lean_dec(v_h__2_89_);
            v_head_96_ = lean_ctor_get(v_x_87_, 0);
            lean_inc(v_head_96_);
            lean_dec_ref_known(v_x_87_, 2);
            v___x_97_ = lean_apply_3(v_h__3_90_, v_head_96_, v_tail_93_, lean_box(0));
            return v___x_97_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(
    mut v_00_u03b1_98_: *mut LeanObject,
    mut v_motive_99_: *mut LeanObject,
    mut v_x_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
    mut v_h__3_103_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_100_) == 0 {
        let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_103_);
        lean_dec(v_h__2_102_);
        v___x_104_ = lean_box(0);
        v___x_105_ = lean_apply_1(v_h__1_101_, v___x_104_);
        return v___x_105_;
    } else {
        let mut v_tail_106_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_101_);
        v_tail_106_ = lean_ctor_get(v_x_100_, 1);
        if lean_obj_tag(v_tail_106_) == 0 {
            let mut v_head_107_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_103_);
            v_head_107_ = lean_ctor_get(v_x_100_, 0);
            lean_inc(v_head_107_);
            lean_dec_ref_known(v_x_100_, 2);
            v___x_108_ = lean_apply_1(v_h__2_102_, v_head_107_);
            return v___x_108_;
        } else {
            let mut v_head_109_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_106_);
            lean_dec(v_h__2_102_);
            v_head_109_ = lean_ctor_get(v_x_100_, 0);
            lean_inc(v_head_109_);
            lean_dec_ref_known(v_x_100_, 2);
            v___x_110_ = lean_apply_3(v_h__3_103_, v_head_109_, v_tail_106_, lean_box(0));
            return v___x_110_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter___redArg(
    mut v_x_111_: *mut LeanObject,
    mut v_x_112_: *mut LeanObject,
    mut v_h__1_113_: *mut LeanObject,
    mut v_h__2_114_: *mut LeanObject,
    mut v_h__3_115_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_111_) == 0 {
        let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_115_);
        lean_dec(v_h__2_114_);
        v___x_116_ = lean_apply_1(v_h__1_113_, v_x_112_);
        return v___x_116_;
    } else {
        let mut v_head_117_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_118_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_119_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_120_: u8 = 0;
        lean_dec(v_h__1_113_);
        v_head_117_ = lean_ctor_get(v_x_111_, 0);
        lean_inc(v_head_117_);
        v_tail_118_ = lean_ctor_get(v_x_111_, 1);
        lean_inc(v_tail_118_);
        lean_dec_ref_known(v_x_111_, 2);
        v_zero_119_ = lean_unsigned_to_nat(0);
        v_isZero_120_ = lean_nat_dec_eq(v_x_112_, v_zero_119_);
        if v_isZero_120_ == 1 {
            let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_115_);
            lean_dec(v_x_112_);
            v___x_121_ = lean_apply_2(v_h__2_114_, v_head_117_, v_tail_118_);
            return v___x_121_;
        } else {
            let mut v_one_122_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_114_);
            v_one_122_ = lean_unsigned_to_nat(1);
            v_n_123_ = lean_nat_sub(v_x_112_, v_one_122_);
            lean_dec(v_x_112_);
            v___x_124_ = lean_apply_3(v_h__3_115_, v_head_117_, v_tail_118_, v_n_123_);
            return v___x_124_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter(
    mut v_00_u03b1_125_: *mut LeanObject,
    mut v_motive_126_: *mut LeanObject,
    mut v_x_127_: *mut LeanObject,
    mut v_x_128_: *mut LeanObject,
    mut v_h__1_129_: *mut LeanObject,
    mut v_h__2_130_: *mut LeanObject,
    mut v_h__3_131_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_127_) == 0 {
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_131_);
        lean_dec(v_h__2_130_);
        v___x_132_ = lean_apply_1(v_h__1_129_, v_x_128_);
        return v___x_132_;
    } else {
        let mut v_head_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_134_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_135_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_136_: u8 = 0;
        lean_dec(v_h__1_129_);
        v_head_133_ = lean_ctor_get(v_x_127_, 0);
        lean_inc(v_head_133_);
        v_tail_134_ = lean_ctor_get(v_x_127_, 1);
        lean_inc(v_tail_134_);
        lean_dec_ref_known(v_x_127_, 2);
        v_zero_135_ = lean_unsigned_to_nat(0);
        v_isZero_136_ = lean_nat_dec_eq(v_x_128_, v_zero_135_);
        if v_isZero_136_ == 1 {
            let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_131_);
            lean_dec(v_x_128_);
            v___x_137_ = lean_apply_2(v_h__2_130_, v_head_133_, v_tail_134_);
            return v___x_137_;
        } else {
            let mut v_one_138_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_139_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_130_);
            v_one_138_ = lean_unsigned_to_nat(1);
            v_n_139_ = lean_nat_sub(v_x_128_, v_one_138_);
            lean_dec(v_x_128_);
            v___x_140_ = lean_apply_3(v_h__3_131_, v_head_133_, v_tail_134_, v_n_139_);
            return v___x_140_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_List_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Nat_Basic(builtin);
}
