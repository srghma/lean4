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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_111_: *mut LeanObject,
    mut v_h__1_112_: *mut LeanObject,
    mut v_h__2_113_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_111_) == 0 {
        let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_112_);
        v___x_114_ = lean_box(0);
        v___x_115_ = lean_apply_1(v_h__2_113_, v___x_114_);
        return v___x_115_;
    } else {
        let mut v_val_116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_113_);
        v_val_116_ = lean_ctor_get(v_x_111_, 0);
        lean_inc(v_val_116_);
        lean_dec_ref_known(v_x_111_, 1);
        v___x_117_ = lean_apply_1(v_h__1_112_, v_val_116_);
        return v___x_117_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_118_: *mut LeanObject,
    mut v_motive_119_: *mut LeanObject,
    mut v_x_120_: *mut LeanObject,
    mut v_h__1_121_: *mut LeanObject,
    mut v_h__2_122_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_120_) == 0 {
        let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_121_);
        v___x_123_ = lean_box(0);
        v___x_124_ = lean_apply_1(v_h__2_122_, v___x_123_);
        return v___x_124_;
    } else {
        let mut v_val_125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_122_);
        v_val_125_ = lean_ctor_get(v_x_120_, 0);
        lean_inc(v_val_125_);
        lean_dec_ref_known(v_x_120_, 1);
        v___x_126_ = lean_apply_1(v_h__1_121_, v_val_125_);
        return v___x_126_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_127_: *mut LeanObject,
    mut v_h__1_128_: *mut LeanObject,
    mut v_h__2_129_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_127_) == 0 {
        let mut v_a_130_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_129_);
        v_a_130_ = lean_ctor_get(v_x_127_, 0);
        lean_inc(v_a_130_);
        lean_dec_ref_known(v_x_127_, 1);
        v___x_131_ = lean_apply_1(v_h__1_128_, v_a_130_);
        return v___x_131_;
    } else {
        let mut v_a_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_128_);
        v_a_132_ = lean_ctor_get(v_x_127_, 0);
        lean_inc(v_a_132_);
        lean_dec_ref_known(v_x_127_, 1);
        v___x_133_ = lean_apply_1(v_h__2_129_, v_a_132_);
        return v___x_133_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_134_: *mut LeanObject,
    mut v_motive_135_: *mut LeanObject,
    mut v_x_136_: *mut LeanObject,
    mut v_h__1_137_: *mut LeanObject,
    mut v_h__2_138_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_136_) == 0 {
        let mut v_a_139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_138_);
        v_a_139_ = lean_ctor_get(v_x_136_, 0);
        lean_inc(v_a_139_);
        lean_dec_ref_known(v_x_136_, 1);
        v___x_140_ = lean_apply_1(v_h__1_137_, v_a_139_);
        return v___x_140_;
    } else {
        let mut v_a_141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_137_);
        v_a_141_ = lean_ctor_get(v_x_136_, 0);
        lean_inc(v_a_141_);
        lean_dec_ref_known(v_x_136_, 1);
        v___x_142_ = lean_apply_1(v_h__2_138_, v_a_141_);
        return v___x_142_;
    }
}
pub unsafe fn l_Array_instTransLt(
    mut v_00_u03b1_143_: *mut LeanObject,
    mut v_inst_144_: *mut LeanObject,
    mut v_inst_145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    v___x_146_ = lean_box(0);
    return v___x_146_;
}
pub unsafe fn l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(
    mut v_00_u03b1_147_: *mut LeanObject,
    mut v_inst_148_: *mut LeanObject,
    mut v_inst_149_: *mut LeanObject,
    mut v_inst_150_: *mut LeanObject,
    mut v_inst_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    v___x_152_ = lean_box(0);
    return v___x_152_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(
    mut v_inst_153_: *mut LeanObject,
    mut v_x1_154_: *mut LeanObject,
    mut v_x2_155_: *mut LeanObject,
) -> u8 {
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    v___x_156_ = lean_apply_2(v_inst_153_, v_x1_154_, v_x2_155_);
    v___x_157_ = (lean_unbox(v___x_156_) as u8);
    return v___x_157_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(
    mut v_inst_158_: *mut LeanObject,
    mut v_x1_159_: *mut LeanObject,
    mut v_x2_160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_161_: u8 = 0;
    let mut v_r_162_: *mut LeanObject = core::ptr::null_mut();
    v_res_161_ =
        l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_158_, v_x1_159_, v_x2_160_);
    v_r_162_ = lean_box((v_res_161_) as usize);
    return v_r_162_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg(
    mut v_inst_163_: *mut LeanObject,
    mut v_inst_164_: *mut LeanObject,
    mut v_xs_165_: *mut LeanObject,
    mut v_ys_166_: *mut LeanObject,
) -> u8 {
    let mut v___f_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: u8 = 0;
    v___f_167_ = lean_alloc_closure(
        l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_167_, 0, v_inst_164_);
    v___f_168_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_168_, 0, v_inst_163_);
    v___x_169_ = l_Array_lex___redArg(v___f_168_, v_xs_165_, v_ys_166_, v___f_167_);
    return v___x_169_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq___redArg___boxed(
    mut v_inst_170_: *mut LeanObject,
    mut v_inst_171_: *mut LeanObject,
    mut v_xs_172_: *mut LeanObject,
    mut v_ys_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_174_: u8 = 0;
    let mut v_r_175_: *mut LeanObject = core::ptr::null_mut();
    v_res_174_ = l_Array_instDecidableLTOfDecidableEq___redArg(
        v_inst_170_,
        v_inst_171_,
        v_xs_172_,
        v_ys_173_,
    );
    v_r_175_ = lean_box((v_res_174_) as usize);
    return v_r_175_;
}
pub unsafe fn l_Array_instDecidableLTOfDecidableEq(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_inst_177_: *mut LeanObject,
    mut v_inst_178_: *mut LeanObject,
    mut v_inst_179_: *mut LeanObject,
    mut v_xs_180_: *mut LeanObject,
    mut v_ys_181_: *mut LeanObject,
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
    mut v_00_u03b1_183_: *mut LeanObject,
    mut v_inst_184_: *mut LeanObject,
    mut v_inst_185_: *mut LeanObject,
    mut v_inst_186_: *mut LeanObject,
    mut v_xs_187_: *mut LeanObject,
    mut v_ys_188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_189_: u8 = 0;
    let mut v_r_190_: *mut LeanObject = core::ptr::null_mut();
    v_res_189_ = l_Array_instDecidableLTOfDecidableEq(
        v_00_u03b1_183_,
        v_inst_184_,
        v_inst_185_,
        v_inst_186_,
        v_xs_187_,
        v_ys_188_,
    );
    v_r_190_ = lean_box((v_res_189_) as usize);
    return v_r_190_;
}
pub unsafe fn l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
    mut v_inst_191_: *mut LeanObject,
    mut v_inst_192_: *mut LeanObject,
    mut v_xs_193_: *mut LeanObject,
    mut v_ys_194_: *mut LeanObject,
) -> u8 {
    let mut v___f_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: u8 = 0;
    v___f_195_ = lean_alloc_closure(
        l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_195_, 0, v_inst_192_);
    v___f_196_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_196_, 0, v_inst_191_);
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
    mut v_inst_200_: *mut LeanObject,
    mut v_inst_201_: *mut LeanObject,
    mut v_xs_202_: *mut LeanObject,
    mut v_ys_203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_204_: u8 = 0;
    let mut v_r_205_: *mut LeanObject = core::ptr::null_mut();
    v_res_204_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
        v_inst_200_,
        v_inst_201_,
        v_xs_202_,
        v_ys_203_,
    );
    v_r_205_ = lean_box((v_res_204_) as usize);
    return v_r_205_;
}
pub unsafe fn l_Array_instDecidableLEOfDecidableEqOfDecidableLT(
    mut v_00_u03b1_206_: *mut LeanObject,
    mut v_inst_207_: *mut LeanObject,
    mut v_inst_208_: *mut LeanObject,
    mut v_inst_209_: *mut LeanObject,
    mut v_xs_210_: *mut LeanObject,
    mut v_ys_211_: *mut LeanObject,
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
    mut v_00_u03b1_213_: *mut LeanObject,
    mut v_inst_214_: *mut LeanObject,
    mut v_inst_215_: *mut LeanObject,
    mut v_inst_216_: *mut LeanObject,
    mut v_xs_217_: *mut LeanObject,
    mut v_ys_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_219_: u8 = 0;
    let mut v_r_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_219_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT(
        v_00_u03b1_213_,
        v_inst_214_,
        v_inst_215_,
        v_inst_216_,
        v_xs_217_,
        v_ys_218_,
    );
    v_r_220_ = lean_box((v_res_219_) as usize);
    return v_r_220_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Lex_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Lex_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Lex_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Lex_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Lex_Lemmas(builtin);
}
