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
pub unsafe fn l_List_instTransPerm(
    mut v_00_u03b1_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = crate::leanh::lean_box(0);
    return v___x_82_;
}
pub unsafe fn l_List_isSetoid(
    mut v_00_u03b1_83_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_84_ = crate::leanh::lean_box(0);
    return v___x_84_;
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(
    mut v_x_85_: *mut crate::leanh::LeanObject,
    mut v_x_86_: *mut crate::leanh::LeanObject,
    mut v_h__1_87_: *mut crate::leanh::LeanObject,
    mut v_h__2_88_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_86_) == 0 {
        let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_88_);
        v___x_89_ = crate::leanh::lean_apply_1(v_h__1_87_, v_x_85_);
        return v___x_89_;
    } else {
        let mut v_head_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_87_);
        v_head_90_ = crate::leanh::lean_ctor_get(v_x_86_, 0);
        crate::leanh::lean_inc(v_head_90_);
        v_tail_91_ = crate::leanh::lean_ctor_get(v_x_86_, 1);
        crate::leanh::lean_inc(v_tail_91_);
        crate::leanh::lean_dec_ref_known(v_x_86_, 2);
        v___x_92_ = crate::leanh::lean_apply_3(v_h__2_88_, v_x_85_, v_head_90_, v_tail_91_);
        return v___x_92_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter(
    mut v_00_u03b1_93_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_94_: *mut crate::leanh::LeanObject,
    mut v_motive_95_: *mut crate::leanh::LeanObject,
    mut v_x_96_: *mut crate::leanh::LeanObject,
    mut v_x_97_: *mut crate::leanh::LeanObject,
    mut v_h__1_98_: *mut crate::leanh::LeanObject,
    mut v_h__2_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_97_) == 0 {
        let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_99_);
        v___x_100_ = crate::leanh::lean_apply_1(v_h__1_98_, v_x_96_);
        return v___x_100_;
    } else {
        let mut v_head_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_98_);
        v_head_101_ = crate::leanh::lean_ctor_get(v_x_97_, 0);
        crate::leanh::lean_inc(v_head_101_);
        v_tail_102_ = crate::leanh::lean_ctor_get(v_x_97_, 1);
        crate::leanh::lean_inc(v_tail_102_);
        crate::leanh::lean_dec_ref_known(v_x_97_, 2);
        v___x_103_ = crate::leanh::lean_apply_3(v_h__2_99_, v_x_96_, v_head_101_, v_tail_102_);
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_104_: *mut crate::leanh::LeanObject,
    mut v_x_105_: *mut crate::leanh::LeanObject,
    mut v_h__1_106_: *mut crate::leanh::LeanObject,
    mut v_h__2_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_104_) == 0 {
        let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_107_);
        v___x_108_ = crate::leanh::lean_apply_1(v_h__1_106_, v_x_105_);
        return v___x_108_;
    } else {
        let mut v_head_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_106_);
        v_head_109_ = crate::leanh::lean_ctor_get(v_x_104_, 0);
        crate::leanh::lean_inc(v_head_109_);
        v_tail_110_ = crate::leanh::lean_ctor_get(v_x_104_, 1);
        crate::leanh::lean_inc(v_tail_110_);
        crate::leanh::lean_dec_ref_known(v_x_104_, 2);
        v___x_111_ = crate::leanh::lean_apply_3(v_h__2_107_, v_head_109_, v_tail_110_, v_x_105_);
        return v___x_111_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_112_: *mut crate::leanh::LeanObject,
    mut v_motive_113_: *mut crate::leanh::LeanObject,
    mut v_x_114_: *mut crate::leanh::LeanObject,
    mut v_x_115_: *mut crate::leanh::LeanObject,
    mut v_h__1_116_: *mut crate::leanh::LeanObject,
    mut v_h__2_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_114_) == 0 {
        let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_117_);
        v___x_118_ = crate::leanh::lean_apply_1(v_h__1_116_, v_x_115_);
        return v___x_118_;
    } else {
        let mut v_head_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_116_);
        v_head_119_ = crate::leanh::lean_ctor_get(v_x_114_, 0);
        crate::leanh::lean_inc(v_head_119_);
        v_tail_120_ = crate::leanh::lean_ctor_get(v_x_114_, 1);
        crate::leanh::lean_inc(v_tail_120_);
        crate::leanh::lean_dec_ref_known(v_x_114_, 2);
        v___x_121_ = crate::leanh::lean_apply_3(v_h__2_117_, v_head_119_, v_tail_120_, v_x_115_);
        return v___x_121_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_122_: *mut crate::leanh::LeanObject,
    mut v_h__1_123_: *mut crate::leanh::LeanObject,
    mut v_h__2_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_122_) == 0 {
        let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_124_);
        v___x_125_ = crate::leanh::lean_box(0);
        v___x_126_ = crate::leanh::lean_apply_1(v_h__1_123_, v___x_125_);
        return v___x_126_;
    } else {
        let mut v_head_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_123_);
        v_head_127_ = crate::leanh::lean_ctor_get(v_x_122_, 0);
        crate::leanh::lean_inc(v_head_127_);
        v_tail_128_ = crate::leanh::lean_ctor_get(v_x_122_, 1);
        crate::leanh::lean_inc(v_tail_128_);
        crate::leanh::lean_dec_ref_known(v_x_122_, 2);
        v___x_129_ = crate::leanh::lean_apply_2(v_h__2_124_, v_head_127_, v_tail_128_);
        return v___x_129_;
    }
}
pub unsafe fn l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_130_: *mut crate::leanh::LeanObject,
    mut v_motive_131_: *mut crate::leanh::LeanObject,
    mut v_x_132_: *mut crate::leanh::LeanObject,
    mut v_h__1_133_: *mut crate::leanh::LeanObject,
    mut v_h__2_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_132_) == 0 {
        let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_134_);
        v___x_135_ = crate::leanh::lean_box(0);
        v___x_136_ = crate::leanh::lean_apply_1(v_h__1_133_, v___x_135_);
        return v___x_136_;
    } else {
        let mut v_head_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_133_);
        v_head_137_ = crate::leanh::lean_ctor_get(v_x_132_, 0);
        crate::leanh::lean_inc(v_head_137_);
        v_tail_138_ = crate::leanh::lean_ctor_get(v_x_132_, 1);
        crate::leanh::lean_inc(v_tail_138_);
        crate::leanh::lean_dec_ref_known(v_x_132_, 2);
        v___x_139_ = crate::leanh::lean_apply_2(v_h__2_134_, v_head_137_, v_tail_138_);
        return v___x_139_;
    }
}
pub unsafe fn l_List_decidablePerm___redArg(
    mut v_inst_140_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_141_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_142_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: u8 = 0;
    v___f_143_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_143_, 0, v_inst_140_);
    v___x_144_ = l_List_isPerm___redArg(v___f_143_, v_l_u2081_141_, v_l_u2082_142_);
    return v___x_144_;
}
pub unsafe fn l_List_decidablePerm___redArg___boxed(
    mut v_inst_145_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_146_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_148_: u8 = 0;
    let mut v_r_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_148_ = l_List_decidablePerm___redArg(v_inst_145_, v_l_u2081_146_, v_l_u2082_147_);
    v_r_149_ = crate::leanh::lean_box((v_res_148_) as usize);
    return v_r_149_;
}
pub unsafe fn l_List_decidablePerm(
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_inst_151_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_152_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_153_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_154_: u8 = 0;
    v___x_154_ = l_List_decidablePerm___redArg(v_inst_151_, v_l_u2081_152_, v_l_u2082_153_);
    return v___x_154_;
}
pub unsafe fn l_List_decidablePerm___boxed(
    mut v_00_u03b1_155_: *mut crate::leanh::LeanObject,
    mut v_inst_156_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_157_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_159_: u8 = 0;
    let mut v_r_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_159_ = l_List_decidablePerm(v_00_u03b1_155_, v_inst_156_, v_l_u2081_157_, v_l_u2082_158_);
    v_r_160_ = crate::leanh::lean_box((v_res_159_) as usize);
    return v_r_160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Perm(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Perm(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Perm(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Perm(builtin);
}
