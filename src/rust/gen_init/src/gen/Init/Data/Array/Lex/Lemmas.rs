// Lean compiler output
// Module: Init.Data.Array.Lex.Lemmas
// Imports: Init.Data.Array.Lex.Basic Init.Data.Array.Lex.Basic Init.Data.Range.Polymorphic.NatLemmas Init.Data.BEq Init.Data.Array.DecidableEq Init.Data.Array.Lemmas Init.Data.Bool Init.Data.List.Lex Init.Data.Range.Polymorphic.Lemmas
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Array::Lex::Basic::{
    initialize_Init_Data_Array_Lex_Basic, l_Array_lex___redArg,
    runtime_initialize_Init_Data_Array_Lex_Basic,
};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Lex::{
    initialize_Init_Data_List_Lex, runtime_initialize_Init_Data_List_Lex,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Lemmas::{
    initialize_Init_Data_Range_Polymorphic_Lemmas,
    runtime_initialize_Init_Data_Range_Polymorphic_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::NatLemmas::{
    initialize_Init_Data_Range_Polymorphic_NatLemmas,
    runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas,
};
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_111_: *mut leanh::LeanObject,
    mut v_h__1_112_: *mut leanh::LeanObject,
    mut v_h__2_113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_111_) == 0 {
        let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_112_);
        v___x_114_ = leanh::lean_box(0);
        v___x_115_ = leanh::lean_apply_1(v_h__2_113_, v___x_114_);
        return v___x_115_;
    } else {
        let mut v_val_116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_113_);
        v_val_116_ = leanh::lean_ctor_get(v_x_111_, 0);
        leanh::lean_inc(v_val_116_);
        leanh::lean_dec_ref_known(v_x_111_, 1);
        v___x_117_ = leanh::lean_apply_1(v_h__1_112_, v_val_116_);
        return v___x_117_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_118_: *mut leanh::LeanObject,
    mut v_motive_119_: *mut leanh::LeanObject,
    mut v_x_120_: *mut leanh::LeanObject,
    mut v_h__1_121_: *mut leanh::LeanObject,
    mut v_h__2_122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_120_) == 0 {
        let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_121_);
        v___x_123_ = leanh::lean_box(0);
        v___x_124_ = leanh::lean_apply_1(v_h__2_122_, v___x_123_);
        return v___x_124_;
    } else {
        let mut v_val_125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_122_);
        v_val_125_ = leanh::lean_ctor_get(v_x_120_, 0);
        leanh::lean_inc(v_val_125_);
        leanh::lean_dec_ref_known(v_x_120_, 1);
        v___x_126_ = leanh::lean_apply_1(v_h__1_121_, v_val_125_);
        return v___x_126_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_127_: *mut leanh::LeanObject,
    mut v_h__1_128_: *mut leanh::LeanObject,
    mut v_h__2_129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_127_) == 0 {
        let mut v_a_130_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_129_);
        v_a_130_ = leanh::lean_ctor_get(v_x_127_, 0);
        leanh::lean_inc(v_a_130_);
        leanh::lean_dec_ref_known(v_x_127_, 1);
        v___x_131_ = leanh::lean_apply_1(v_h__1_128_, v_a_130_);
        return v___x_131_;
    } else {
        let mut v_a_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_128_);
        v_a_132_ = leanh::lean_ctor_get(v_x_127_, 0);
        leanh::lean_inc(v_a_132_);
        leanh::lean_dec_ref_known(v_x_127_, 1);
        v___x_133_ = leanh::lean_apply_1(v_h__2_129_, v_a_132_);
        return v___x_133_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_134_: *mut leanh::LeanObject,
    mut v_motive_135_: *mut leanh::LeanObject,
    mut v_x_136_: *mut leanh::LeanObject,
    mut v_h__1_137_: *mut leanh::LeanObject,
    mut v_h__2_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_136_) == 0 {
        let mut v_a_139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_138_);
        v_a_139_ = leanh::lean_ctor_get(v_x_136_, 0);
        leanh::lean_inc(v_a_139_);
        leanh::lean_dec_ref_known(v_x_136_, 1);
        v___x_140_ = leanh::lean_apply_1(v_h__1_137_, v_a_139_);
        return v___x_140_;
    } else {
        let mut v_a_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_137_);
        v_a_141_ = leanh::lean_ctor_get(v_x_136_, 0);
        leanh::lean_inc(v_a_141_);
        leanh::lean_dec_ref_known(v_x_136_, 1);
        v___x_142_ = leanh::lean_apply_1(v_h__2_138_, v_a_141_);
        return v___x_142_;
    }
}
pub unsafe fn l_Array_instTransLt(
    mut v_00_u03b1_143_: *mut leanh::LeanObject,
    mut v_inst_144_: *mut leanh::LeanObject,
    mut v_inst_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_146_ = leanh::lean_box(0);
    return v___x_146_;
}
pub unsafe fn l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(
    mut v_00_u03b1_147_: *mut leanh::LeanObject,
    mut v_inst_148_: *mut leanh::LeanObject,
    mut v_inst_149_: *mut leanh::LeanObject,
    mut v_inst_150_: *mut leanh::LeanObject,
    mut v_inst_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = leanh::lean_box(0);
    return v___x_152_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(
    mut v_inst_153_: *mut leanh::LeanObject,
    mut v_x1_154_: *mut leanh::LeanObject,
    mut v_x2_155_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    v___x_156_ = leanh::lean_apply_2(v_inst_153_, v_x1_154_, v_x2_155_);
    v___x_157_ = (leanh::lean_unbox(v___x_156_) as u8);
    return v___x_157_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(
    mut v_inst_158_: *mut leanh::LeanObject,
    mut v_x1_159_: *mut leanh::LeanObject,
    mut v_x2_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_161_: u8 = 0;
    let mut v_r_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_161_ =
        l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_158_, v_x1_159_, v_x2_160_);
    v_r_162_ = leanh::lean_box((v_res_161_) as usize);
    return v_r_162_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg(
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_inst_164_: *mut leanh::LeanObject,
    mut v_xs_165_: *mut leanh::LeanObject,
    mut v_ys_166_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: u8 = 0;
    v___f_167_ = leanh::lean_alloc_closure(
        l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_167_, 0, v_inst_164_);
    v___f_168_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_168_, 0, v_inst_163_);
    v___x_169_ = l_Array_lex___redArg(v___f_168_, v_xs_165_, v_ys_166_, v___f_167_);
    return v___x_169_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg___boxed(
    mut v_inst_170_: *mut leanh::LeanObject,
    mut v_inst_171_: *mut leanh::LeanObject,
    mut v_xs_172_: *mut leanh::LeanObject,
    mut v_ys_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_174_: u8 = 0;
    let mut v_r_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_174_ = l_Array_instDecidableLTOfDecidableEq___redArg(
        v_inst_170_,
        v_inst_171_,
        v_xs_172_,
        v_ys_173_,
    );
    v_r_175_ = leanh::lean_box((v_res_174_) as usize);
    return v_r_175_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq(
    mut v_00_u03b1_176_: *mut leanh::LeanObject,
    mut v_inst_177_: *mut leanh::LeanObject,
    mut v_inst_178_: *mut leanh::LeanObject,
    mut v_inst_179_: *mut leanh::LeanObject,
    mut v_xs_180_: *mut leanh::LeanObject,
    mut v_ys_181_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_182_: u8 = 0;
    v___x_182_ = l_Array_instDecidableLTOfDecidableEq___redArg(
        v_inst_177_,
        v_inst_179_,
        v_xs_180_,
        v_ys_181_,
    );
    return v___x_182_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___boxed(
    mut v_00_u03b1_183_: *mut leanh::LeanObject,
    mut v_inst_184_: *mut leanh::LeanObject,
    mut v_inst_185_: *mut leanh::LeanObject,
    mut v_inst_186_: *mut leanh::LeanObject,
    mut v_xs_187_: *mut leanh::LeanObject,
    mut v_ys_188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_189_: u8 = 0;
    let mut v_r_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_189_ = l_Array_instDecidableLTOfDecidableEq(
        v_00_u03b1_183_,
        v_inst_184_,
        v_inst_185_,
        v_inst_186_,
        v_xs_187_,
        v_ys_188_,
    );
    v_r_190_ = leanh::lean_box((v_res_189_) as usize);
    return v_r_190_;
}
pub unsafe fn l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
    mut v_inst_191_: *mut leanh::LeanObject,
    mut v_inst_192_: *mut leanh::LeanObject,
    mut v_xs_193_: *mut leanh::LeanObject,
    mut v_ys_194_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: u8 = 0;
    v___f_195_ = leanh::lean_alloc_closure(
        l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_195_, 0, v_inst_192_);
    v___f_196_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_196_, 0, v_inst_191_);
    v___x_197_ = l_Array_lex___redArg(v___f_196_, v_ys_194_, v_xs_193_, v___f_195_);
    if v___x_197_ == 0 {
        let mut v___x_198_: u8 = 0;
        v___x_198_ = 1;
        return v___x_198_;
    } else {
        let mut v___x_199_: u8 = 0;
        v___x_199_ = 0;
        return v___x_199_;
    }
}
pub unsafe fn l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(
    mut v_inst_200_: *mut leanh::LeanObject,
    mut v_inst_201_: *mut leanh::LeanObject,
    mut v_xs_202_: *mut leanh::LeanObject,
    mut v_ys_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_204_: u8 = 0;
    let mut v_r_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
        v_inst_200_,
        v_inst_201_,
        v_xs_202_,
        v_ys_203_,
    );
    v_r_205_ = leanh::lean_box((v_res_204_) as usize);
    return v_r_205_;
}
pub unsafe fn l_Array_instDecidableLEOfDecidableEqOfDecidableLT(
    mut v_00_u03b1_206_: *mut leanh::LeanObject,
    mut v_inst_207_: *mut leanh::LeanObject,
    mut v_inst_208_: *mut leanh::LeanObject,
    mut v_inst_209_: *mut leanh::LeanObject,
    mut v_xs_210_: *mut leanh::LeanObject,
    mut v_ys_211_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_212_: u8 = 0;
    v___x_212_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
        v_inst_207_,
        v_inst_209_,
        v_xs_210_,
        v_ys_211_,
    );
    return v___x_212_;
}
pub unsafe fn l_Array_instDecidableLEOfDecidableEqOfDecidableLT___boxed(
    mut v_00_u03b1_213_: *mut leanh::LeanObject,
    mut v_inst_214_: *mut leanh::LeanObject,
    mut v_inst_215_: *mut leanh::LeanObject,
    mut v_inst_216_: *mut leanh::LeanObject,
    mut v_xs_217_: *mut leanh::LeanObject,
    mut v_ys_218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_219_: u8 = 0;
    let mut v_r_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_219_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT(
        v_00_u03b1_213_,
        v_inst_214_,
        v_inst_215_,
        v_inst_216_,
        v_xs_217_,
        v_ys_218_,
    );
    v_r_220_ = leanh::lean_box((v_res_219_) as usize);
    return v_r_220_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Lex_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Lex_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Lex_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Lex_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lex_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Lex_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Lex_Lemmas(builtin);
}