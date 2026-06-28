// Lean compiler output
// Module: Init.Data.List.Perm
// Imports: Init.Data.List.Attach Init.Data.List.Attach Init.Data.List.Erase Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.Nat.Lemmas
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Basic::l_List_isPerm___redArg;
use crate::r#gen::Init::Data::List::Erase::{
    initialize_Init_Data_List_Erase, runtime_initialize_Init_Data_List_Erase,
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
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_List_instTransPerm(mut v_00_u03b1_81_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    v___x_82_ = lean_box(0);
    return v___x_82_;
}
pub unsafe fn l_List_isSetoid(mut v_00_u03b1_83_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    v___x_84_ = lean_box(0);
    return v___x_84_;
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(
    mut v_x_85_: *mut LeanObject,
    mut v_x_86_: *mut LeanObject,
    mut v_h__1_87_: *mut LeanObject,
    mut v_h__2_88_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_86_) == 0 {
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_88_);
        v___x_89_ = lean_apply_1(v_h__1_87_, v_x_85_);
        return v___x_89_;
    } else {
        let mut v_head_90_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_91_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_87_);
        v_head_90_ = lean_ctor_get(v_x_86_, 0);
        lean_inc(v_head_90_);
        v_tail_91_ = lean_ctor_get(v_x_86_, 1);
        lean_inc(v_tail_91_);
        lean_dec_ref_known(v_x_86_, 2);
        v___x_92_ = lean_apply_3(v_h__2_88_, v_x_85_, v_head_90_, v_tail_91_);
        return v___x_92_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter(
    mut v_00_u03b1_93_: *mut LeanObject,
    mut v_00_u03b2_94_: *mut LeanObject,
    mut v_motive_95_: *mut LeanObject,
    mut v_x_96_: *mut LeanObject,
    mut v_x_97_: *mut LeanObject,
    mut v_h__1_98_: *mut LeanObject,
    mut v_h__2_99_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_97_) == 0 {
        let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_99_);
        v___x_100_ = lean_apply_1(v_h__1_98_, v_x_96_);
        return v___x_100_;
    } else {
        let mut v_head_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_98_);
        v_head_101_ = lean_ctor_get(v_x_97_, 0);
        lean_inc(v_head_101_);
        v_tail_102_ = lean_ctor_get(v_x_97_, 1);
        lean_inc(v_tail_102_);
        lean_dec_ref_known(v_x_97_, 2);
        v___x_103_ = lean_apply_3(v_h__2_99_, v_x_96_, v_head_101_, v_tail_102_);
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_104_: *mut LeanObject,
    mut v_x_105_: *mut LeanObject,
    mut v_h__1_106_: *mut LeanObject,
    mut v_h__2_107_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_104_) == 0 {
        let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_107_);
        v___x_108_ = lean_apply_1(v_h__1_106_, v_x_105_);
        return v___x_108_;
    } else {
        let mut v_head_109_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_106_);
        v_head_109_ = lean_ctor_get(v_x_104_, 0);
        lean_inc(v_head_109_);
        v_tail_110_ = lean_ctor_get(v_x_104_, 1);
        lean_inc(v_tail_110_);
        lean_dec_ref_known(v_x_104_, 2);
        v___x_111_ = lean_apply_3(v_h__2_107_, v_head_109_, v_tail_110_, v_x_105_);
        return v___x_111_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_112_: *mut LeanObject,
    mut v_motive_113_: *mut LeanObject,
    mut v_x_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
    mut v_h__1_116_: *mut LeanObject,
    mut v_h__2_117_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_114_) == 0 {
        let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_117_);
        v___x_118_ = lean_apply_1(v_h__1_116_, v_x_115_);
        return v___x_118_;
    } else {
        let mut v_head_119_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_116_);
        v_head_119_ = lean_ctor_get(v_x_114_, 0);
        lean_inc(v_head_119_);
        v_tail_120_ = lean_ctor_get(v_x_114_, 1);
        lean_inc(v_tail_120_);
        lean_dec_ref_known(v_x_114_, 2);
        v___x_121_ = lean_apply_3(v_h__2_117_, v_head_119_, v_tail_120_, v_x_115_);
        return v___x_121_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_122_: *mut LeanObject,
    mut v_h__1_123_: *mut LeanObject,
    mut v_h__2_124_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_122_) == 0 {
        let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_124_);
        v___x_125_ = lean_box(0);
        v___x_126_ = lean_apply_1(v_h__1_123_, v___x_125_);
        return v___x_126_;
    } else {
        let mut v_head_127_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_123_);
        v_head_127_ = lean_ctor_get(v_x_122_, 0);
        lean_inc(v_head_127_);
        v_tail_128_ = lean_ctor_get(v_x_122_, 1);
        lean_inc(v_tail_128_);
        lean_dec_ref_known(v_x_122_, 2);
        v___x_129_ = lean_apply_2(v_h__2_124_, v_head_127_, v_tail_128_);
        return v___x_129_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_130_: *mut LeanObject,
    mut v_motive_131_: *mut LeanObject,
    mut v_x_132_: *mut LeanObject,
    mut v_h__1_133_: *mut LeanObject,
    mut v_h__2_134_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_132_) == 0 {
        let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_134_);
        v___x_135_ = lean_box(0);
        v___x_136_ = lean_apply_1(v_h__1_133_, v___x_135_);
        return v___x_136_;
    } else {
        let mut v_head_137_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_133_);
        v_head_137_ = lean_ctor_get(v_x_132_, 0);
        lean_inc(v_head_137_);
        v_tail_138_ = lean_ctor_get(v_x_132_, 1);
        lean_inc(v_tail_138_);
        lean_dec_ref_known(v_x_132_, 2);
        v___x_139_ = lean_apply_2(v_h__2_134_, v_head_137_, v_tail_138_);
        return v___x_139_;
    }
}
pub unsafe fn l_List_decidablePerm___redArg(
    mut v_inst_140_: *mut LeanObject,
    mut v_l_u2081_141_: *mut LeanObject,
    mut v_l_u2082_142_: *mut LeanObject,
) -> u8 {
    let mut v___f_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_144_: u8 = 0;
    v___f_143_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_143_, 0, v_inst_140_);
    v___x_144_ = l_List_isPerm___redArg(v___f_143_, v_l_u2081_141_, v_l_u2082_142_);
    return v___x_144_;
}
pub unsafe fn l_List_decidablePerm___redArg___boxed(
    mut v_inst_145_: *mut LeanObject,
    mut v_l_u2081_146_: *mut LeanObject,
    mut v_l_u2082_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_148_: u8 = 0;
    let mut v_r_149_: *mut LeanObject = core::ptr::null_mut();
    v_res_148_ = l_List_decidablePerm___redArg(v_inst_145_, v_l_u2081_146_, v_l_u2082_147_);
    v_r_149_ = lean_box((v_res_148_) as usize);
    return v_r_149_;
}
pub unsafe fn l_List_decidablePerm(
    mut v_00_u03b1_150_: *mut LeanObject,
    mut v_inst_151_: *mut LeanObject,
    mut v_l_u2081_152_: *mut LeanObject,
    mut v_l_u2082_153_: *mut LeanObject,
) -> u8 {
    let mut v___x_154_: u8 = 0;
    v___x_154_ = l_List_decidablePerm___redArg(v_inst_151_, v_l_u2081_152_, v_l_u2082_153_);
    return v___x_154_;
}
pub unsafe fn l_List_decidablePerm___boxed(
    mut v_00_u03b1_155_: *mut LeanObject,
    mut v_inst_156_: *mut LeanObject,
    mut v_l_u2081_157_: *mut LeanObject,
    mut v_l_u2082_158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_159_: u8 = 0;
    let mut v_r_160_: *mut LeanObject = core::ptr::null_mut();
    v_res_159_ = l_List_decidablePerm(v_00_u03b1_155_, v_inst_156_, v_l_u2081_157_, v_l_u2082_158_);
    v_r_160_ = lean_box((v_res_159_) as usize);
    return v_r_160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Perm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
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
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Perm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Perm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
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
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Perm(builtin);
}
