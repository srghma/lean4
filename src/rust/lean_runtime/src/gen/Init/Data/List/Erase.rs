// Lean compiler output
// Module: Init.Data.List.Erase
// Imports: Init.BinderPredicates Init.Ext Init.NotationExtra Init.ByCases Init.Data.Bool Init.Data.List.Find Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.Nat.Lemmas Init.Omega Init.TacticsExtra
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_List_Erase_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_78_: *mut LeanObject,
    mut v_h__1_79_: *mut LeanObject,
    mut v_h__2_80_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_78_) == 0 {
        let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_80_);
        v___x_81_ = lean_box(0);
        v___x_82_ = lean_apply_1(v_h__1_79_, v___x_81_);
        return v___x_82_;
    } else {
        let mut v_val_83_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_79_);
        v_val_83_ = lean_ctor_get(v_x_78_, 0);
        lean_inc(v_val_83_);
        lean_dec_ref_known(v_x_78_, 1);
        v___x_84_ = lean_apply_1(v_h__2_80_, v_val_83_);
        return v___x_84_;
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_85_: *mut LeanObject,
    mut v_motive_86_: *mut LeanObject,
    mut v_x_87_: *mut LeanObject,
    mut v_h__1_88_: *mut LeanObject,
    mut v_h__2_89_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_87_) == 0 {
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_89_);
        v___x_90_ = lean_box(0);
        v___x_91_ = lean_apply_1(v_h__1_88_, v___x_90_);
        return v___x_91_;
    } else {
        let mut v_val_92_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_88_);
        v_val_92_ = lean_ctor_get(v_x_87_, 0);
        lean_inc(v_val_92_);
        lean_dec_ref_known(v_x_87_, 1);
        v___x_93_ = lean_apply_1(v_h__2_89_, v_val_92_);
        return v___x_93_;
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_eraseP__filterMap_match__1_splitter___redArg(
    mut v_x_94_: *mut LeanObject,
    mut v_h__1_95_: *mut LeanObject,
    mut v_h__2_96_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_94_) == 0 {
        let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_95_);
        v___x_97_ = lean_box(0);
        v___x_98_ = lean_apply_1(v_h__2_96_, v___x_97_);
        return v___x_98_;
    } else {
        let mut v_val_99_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_96_);
        v_val_99_ = lean_ctor_get(v_x_94_, 0);
        lean_inc(v_val_99_);
        lean_dec_ref_known(v_x_94_, 1);
        v___x_100_ = lean_apply_1(v_h__1_95_, v_val_99_);
        return v___x_100_;
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_eraseP__filterMap_match__1_splitter(
    mut v_00_u03b2_101_: *mut LeanObject,
    mut v_motive_102_: *mut LeanObject,
    mut v_x_103_: *mut LeanObject,
    mut v_h__1_104_: *mut LeanObject,
    mut v_h__2_105_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_103_) == 0 {
        let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_104_);
        v___x_106_ = lean_box(0);
        v___x_107_ = lean_apply_1(v_h__2_105_, v___x_106_);
        return v___x_107_;
    } else {
        let mut v_val_108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_105_);
        v_val_108_ = lean_ctor_get(v_x_103_, 0);
        lean_inc(v_val_108_);
        lean_dec_ref_known(v_x_103_, 1);
        v___x_109_ = lean_apply_1(v_h__1_104_, v_val_108_);
        return v___x_109_;
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_eraseP__eq__eraseIdx_match__1_splitter___redArg(
    mut v_x_110_: *mut LeanObject,
    mut v_h__1_111_: *mut LeanObject,
    mut v_h__2_112_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_110_) == 0 {
        let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_112_);
        v___x_113_ = lean_box(0);
        v___x_114_ = lean_apply_1(v_h__1_111_, v___x_113_);
        return v___x_114_;
    } else {
        let mut v_val_115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_111_);
        v_val_115_ = lean_ctor_get(v_x_110_, 0);
        lean_inc(v_val_115_);
        lean_dec_ref_known(v_x_110_, 1);
        v___x_116_ = lean_apply_1(v_h__2_112_, v_val_115_);
        return v___x_116_;
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_eraseP__eq__eraseIdx_match__1_splitter(
    mut v_motive_117_: *mut LeanObject,
    mut v_x_118_: *mut LeanObject,
    mut v_h__1_119_: *mut LeanObject,
    mut v_h__2_120_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_118_) == 0 {
        let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_120_);
        v___x_121_ = lean_box(0);
        v___x_122_ = lean_apply_1(v_h__1_119_, v___x_121_);
        return v___x_122_;
    } else {
        let mut v_val_123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_119_);
        v_val_123_ = lean_ctor_get(v_x_118_, 0);
        lean_inc(v_val_123_);
        lean_dec_ref_known(v_x_118_, 1);
        v___x_124_ = lean_apply_1(v_h__2_120_, v_val_123_);
        return v___x_124_;
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_eraseIdx_match__1_splitter___redArg(
    mut v_x_125_: *mut LeanObject,
    mut v_x_126_: *mut LeanObject,
    mut v_h__1_127_: *mut LeanObject,
    mut v_h__2_128_: *mut LeanObject,
    mut v_h__3_129_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_125_) == 0 {
        let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_129_);
        lean_dec(v_h__2_128_);
        v___x_130_ = lean_apply_1(v_h__1_127_, v_x_126_);
        return v___x_130_;
    } else {
        let mut v_head_131_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_134_: u8 = 0;
        lean_dec(v_h__1_127_);
        v_head_131_ = lean_ctor_get(v_x_125_, 0);
        lean_inc(v_head_131_);
        v_tail_132_ = lean_ctor_get(v_x_125_, 1);
        lean_inc(v_tail_132_);
        lean_dec_ref_known(v_x_125_, 2);
        v_zero_133_ = lean_unsigned_to_nat(0);
        v_isZero_134_ = lean_nat_dec_eq(v_x_126_, v_zero_133_);
        if v_isZero_134_ == 1 {
            let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_129_);
            lean_dec(v_x_126_);
            v___x_135_ = lean_apply_2(v_h__2_128_, v_head_131_, v_tail_132_);
            return v___x_135_;
        } else {
            let mut v_one_136_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_137_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_128_);
            v_one_136_ = lean_unsigned_to_nat(1);
            v_n_137_ = lean_nat_sub(v_x_126_, v_one_136_);
            lean_dec(v_x_126_);
            v___x_138_ = lean_apply_3(v_h__3_129_, v_head_131_, v_tail_132_, v_n_137_);
            return v___x_138_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Erase_0__List_eraseIdx_match__1_splitter(
    mut v_00_u03b1_139_: *mut LeanObject,
    mut v_motive_140_: *mut LeanObject,
    mut v_x_141_: *mut LeanObject,
    mut v_x_142_: *mut LeanObject,
    mut v_h__1_143_: *mut LeanObject,
    mut v_h__2_144_: *mut LeanObject,
    mut v_h__3_145_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_141_) == 0 {
        let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_145_);
        lean_dec(v_h__2_144_);
        v___x_146_ = lean_apply_1(v_h__1_143_, v_x_142_);
        return v___x_146_;
    } else {
        let mut v_head_147_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_148_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_149_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_150_: u8 = 0;
        lean_dec(v_h__1_143_);
        v_head_147_ = lean_ctor_get(v_x_141_, 0);
        lean_inc(v_head_147_);
        v_tail_148_ = lean_ctor_get(v_x_141_, 1);
        lean_inc(v_tail_148_);
        lean_dec_ref_known(v_x_141_, 2);
        v_zero_149_ = lean_unsigned_to_nat(0);
        v_isZero_150_ = lean_nat_dec_eq(v_x_142_, v_zero_149_);
        if v_isZero_150_ == 1 {
            let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_145_);
            lean_dec(v_x_142_);
            v___x_151_ = lean_apply_2(v_h__2_144_, v_head_147_, v_tail_148_);
            return v___x_151_;
        } else {
            let mut v_one_152_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_153_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_144_);
            v_one_152_ = lean_unsigned_to_nat(1);
            v_n_153_ = lean_nat_sub(v_x_142_, v_one_152_);
            lean_dec(v_x_142_);
            v___x_154_ = lean_apply_3(v_h__3_145_, v_head_147_, v_tail_148_, v_n_153_);
            return v___x_154_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Erase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
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
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_List_Erase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Erase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
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
    res = initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Erase(builtin);
}
