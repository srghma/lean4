// Lean compiler output
// Module: Init.Data.Vector.Lex
// Imports: Init.Data.Vector.Basic Init.Data.Array.Lex.Basic Init.Data.Range.Polymorphic.Lemmas Init.Data.Array.Lex.Basic Init.Data.BEq Init.Data.Vector.Basic Init.Data.Array.Lex.Lemmas Init.Data.Vector.Lemmas
use crate::r#gen::Init::Data::Array::Lex::Basic::{
    initialize_Init_Data_Array_Lex_Basic, runtime_initialize_Init_Data_Array_Lex_Basic,
};
use crate::r#gen::Init::Data::Array::Lex::Lemmas::{
    initialize_Init_Data_Array_Lex_Lemmas, runtime_initialize_Init_Data_Array_Lex_Lemmas,
};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Range::Polymorphic::Lemmas::{
    initialize_Init_Data_Range_Polymorphic_Lemmas,
    runtime_initialize_Init_Data_Range_Polymorphic_Lemmas,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, l_Vector_lex___redArg,
    runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
pub unsafe fn l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter___redArg(
    mut v_x_117_: *mut crate::leanh::LeanObject,
    mut v_h__1_118_: *mut crate::leanh::LeanObject,
    mut v_h__2_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_117_) == 0 {
        let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_118_);
        v___x_120_ = crate::leanh::lean_box(0);
        v___x_121_ = crate::leanh::lean_apply_1(v_h__2_119_, v___x_120_);
        return v___x_121_;
    } else {
        let mut v_val_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_119_);
        v_val_122_ = crate::leanh::lean_ctor_get(v_x_117_, 0);
        crate::leanh::lean_inc(v_val_122_);
        crate::leanh::lean_dec_ref_known(v_x_117_, 1);
        v___x_123_ = crate::leanh::lean_apply_1(v_h__1_118_, v_val_122_);
        return v___x_123_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Lex_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_124_: *mut crate::leanh::LeanObject,
    mut v_motive_125_: *mut crate::leanh::LeanObject,
    mut v_x_126_: *mut crate::leanh::LeanObject,
    mut v_h__1_127_: *mut crate::leanh::LeanObject,
    mut v_h__2_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_126_) == 0 {
        let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_127_);
        v___x_129_ = crate::leanh::lean_box(0);
        v___x_130_ = crate::leanh::lean_apply_1(v_h__2_128_, v___x_129_);
        return v___x_130_;
    } else {
        let mut v_val_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_128_);
        v_val_131_ = crate::leanh::lean_ctor_get(v_x_126_, 0);
        crate::leanh::lean_inc(v_val_131_);
        crate::leanh::lean_dec_ref_known(v_x_126_, 1);
        v___x_132_ = crate::leanh::lean_apply_1(v_h__1_127_, v_val_131_);
        return v___x_132_;
    }
}
pub unsafe fn l_Vector_instTransLt(
    mut v_00_u03b1_133_: *mut crate::leanh::LeanObject,
    mut v_n_134_: *mut crate::leanh::LeanObject,
    mut v_inst_135_: *mut crate::leanh::LeanObject,
    mut v_inst_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = crate::leanh::lean_box(0);
    return v___x_137_;
}
pub unsafe fn l_Vector_instTransLt___boxed(
    mut v_00_u03b1_138_: *mut crate::leanh::LeanObject,
    mut v_n_139_: *mut crate::leanh::LeanObject,
    mut v_inst_140_: *mut crate::leanh::LeanObject,
    mut v_inst_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ = l_Vector_instTransLt(v_00_u03b1_138_, v_n_139_, v_inst_140_, v_inst_141_);
    crate::leanh::lean_dec(v_n_139_);
    return v_res_142_;
}
pub unsafe fn l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(
    mut v_00_u03b1_143_: *mut crate::leanh::LeanObject,
    mut v_n_144_: *mut crate::leanh::LeanObject,
    mut v_inst_145_: *mut crate::leanh::LeanObject,
    mut v_inst_146_: *mut crate::leanh::LeanObject,
    mut v_inst_147_: *mut crate::leanh::LeanObject,
    mut v_inst_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = crate::leanh::lean_box(0);
    return v___x_149_;
}
pub unsafe fn l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder___boxed(
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_n_151_: *mut crate::leanh::LeanObject,
    mut v_inst_152_: *mut crate::leanh::LeanObject,
    mut v_inst_153_: *mut crate::leanh::LeanObject,
    mut v_inst_154_: *mut crate::leanh::LeanObject,
    mut v_inst_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_156_ = l_Vector_instTransLeOfLawfulOrderLTOfIsLinearOrder(
        v_00_u03b1_150_,
        v_n_151_,
        v_inst_152_,
        v_inst_153_,
        v_inst_154_,
        v_inst_155_,
    );
    crate::leanh::lean_dec(v_n_151_);
    return v_res_156_;
}
pub unsafe fn l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(
    mut v_inst_157_: *mut crate::leanh::LeanObject,
    mut v_x1_158_: *mut crate::leanh::LeanObject,
    mut v_x2_159_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: u8 = 0;
    v___x_160_ = crate::leanh::lean_apply_2(v_inst_157_, v_x1_158_, v_x2_159_);
    v___x_161_ = (crate::leanh::lean_unbox(v___x_160_) as u8);
    return v___x_161_;
}
pub unsafe fn l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(
    mut v_inst_162_: *mut crate::leanh::LeanObject,
    mut v_x1_163_: *mut crate::leanh::LeanObject,
    mut v_x2_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_165_: u8 = 0;
    let mut v_r_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_165_ =
        l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_162_, v_x1_163_, v_x2_164_);
    v_r_166_ = crate::leanh::lean_box((v_res_165_) as usize);
    return v_r_166_;
}
pub unsafe fn l_Vector_instDecidableLTOfDecidableEq___redArg(
    mut v_n_167_: *mut crate::leanh::LeanObject,
    mut v_inst_168_: *mut crate::leanh::LeanObject,
    mut v_inst_169_: *mut crate::leanh::LeanObject,
    mut v_xs_170_: *mut crate::leanh::LeanObject,
    mut v_ys_171_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: u8 = 0;
    v___f_172_ = crate::leanh::lean_alloc_closure(
        l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_172_, 0, v_inst_169_);
    v___f_173_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_173_, 0, v_inst_168_);
    v___x_174_ = l_Vector_lex___redArg(v_n_167_, v___f_173_, v_xs_170_, v_ys_171_, v___f_172_);
    return v___x_174_;
}
pub unsafe fn l_Vector_instDecidableLTOfDecidableEq___redArg___boxed(
    mut v_n_175_: *mut crate::leanh::LeanObject,
    mut v_inst_176_: *mut crate::leanh::LeanObject,
    mut v_inst_177_: *mut crate::leanh::LeanObject,
    mut v_xs_178_: *mut crate::leanh::LeanObject,
    mut v_ys_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: u8 = 0;
    let mut v_r_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l_Vector_instDecidableLTOfDecidableEq___redArg(
        v_n_175_,
        v_inst_176_,
        v_inst_177_,
        v_xs_178_,
        v_ys_179_,
    );
    v_r_181_ = crate::leanh::lean_box((v_res_180_) as usize);
    return v_r_181_;
}
pub unsafe fn l_Vector_instDecidableLTOfDecidableEq(
    mut v_00_u03b1_182_: *mut crate::leanh::LeanObject,
    mut v_n_183_: *mut crate::leanh::LeanObject,
    mut v_inst_184_: *mut crate::leanh::LeanObject,
    mut v_inst_185_: *mut crate::leanh::LeanObject,
    mut v_inst_186_: *mut crate::leanh::LeanObject,
    mut v_xs_187_: *mut crate::leanh::LeanObject,
    mut v_ys_188_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_189_: u8 = 0;
    v___x_189_ = l_Vector_instDecidableLTOfDecidableEq___redArg(
        v_n_183_,
        v_inst_184_,
        v_inst_186_,
        v_xs_187_,
        v_ys_188_,
    );
    return v___x_189_;
}
pub unsafe fn l_Vector_instDecidableLTOfDecidableEq___boxed(
    mut v_00_u03b1_190_: *mut crate::leanh::LeanObject,
    mut v_n_191_: *mut crate::leanh::LeanObject,
    mut v_inst_192_: *mut crate::leanh::LeanObject,
    mut v_inst_193_: *mut crate::leanh::LeanObject,
    mut v_inst_194_: *mut crate::leanh::LeanObject,
    mut v_xs_195_: *mut crate::leanh::LeanObject,
    mut v_ys_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_197_: u8 = 0;
    let mut v_r_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_197_ = l_Vector_instDecidableLTOfDecidableEq(
        v_00_u03b1_190_,
        v_n_191_,
        v_inst_192_,
        v_inst_193_,
        v_inst_194_,
        v_xs_195_,
        v_ys_196_,
    );
    v_r_198_ = crate::leanh::lean_box((v_res_197_) as usize);
    return v_r_198_;
}
pub unsafe fn l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
    mut v_n_199_: *mut crate::leanh::LeanObject,
    mut v_inst_200_: *mut crate::leanh::LeanObject,
    mut v_inst_201_: *mut crate::leanh::LeanObject,
    mut v_xs_202_: *mut crate::leanh::LeanObject,
    mut v_ys_203_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: u8 = 0;
    v___f_204_ = crate::leanh::lean_alloc_closure(
        l_Vector_instDecidableLTOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_204_, 0, v_inst_201_);
    v___f_205_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_205_, 0, v_inst_200_);
    v___x_206_ = l_Vector_lex___redArg(v_n_199_, v___f_205_, v_ys_203_, v_xs_202_, v___f_204_);
    if v___x_206_ == 0 {
        let mut v___x_207_: u8 = 0;
        v___x_207_ = 1;
        return v___x_207_;
    } else {
        let mut v___x_208_: u8 = 0;
        v___x_208_ = 0;
        return v___x_208_;
    }
}
pub unsafe fn l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(
    mut v_n_209_: *mut crate::leanh::LeanObject,
    mut v_inst_210_: *mut crate::leanh::LeanObject,
    mut v_inst_211_: *mut crate::leanh::LeanObject,
    mut v_xs_212_: *mut crate::leanh::LeanObject,
    mut v_ys_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_214_: u8 = 0;
    let mut v_r_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
        v_n_209_,
        v_inst_210_,
        v_inst_211_,
        v_xs_212_,
        v_ys_213_,
    );
    v_r_215_ = crate::leanh::lean_box((v_res_214_) as usize);
    return v_r_215_;
}
pub unsafe fn l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(
    mut v_00_u03b1_216_: *mut crate::leanh::LeanObject,
    mut v_n_217_: *mut crate::leanh::LeanObject,
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_inst_219_: *mut crate::leanh::LeanObject,
    mut v_inst_220_: *mut crate::leanh::LeanObject,
    mut v_xs_221_: *mut crate::leanh::LeanObject,
    mut v_ys_222_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_223_: u8 = 0;
    v___x_223_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___redArg(
        v_n_217_,
        v_inst_218_,
        v_inst_220_,
        v_xs_221_,
        v_ys_222_,
    );
    return v___x_223_;
}
pub unsafe fn l_Vector_instDecidableLEOfDecidableEqOfDecidableLT___boxed(
    mut v_00_u03b1_224_: *mut crate::leanh::LeanObject,
    mut v_n_225_: *mut crate::leanh::LeanObject,
    mut v_inst_226_: *mut crate::leanh::LeanObject,
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_inst_228_: *mut crate::leanh::LeanObject,
    mut v_xs_229_: *mut crate::leanh::LeanObject,
    mut v_ys_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_231_: u8 = 0;
    let mut v_r_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_231_ = l_Vector_instDecidableLEOfDecidableEqOfDecidableLT(
        v_00_u03b1_224_,
        v_n_225_,
        v_inst_226_,
        v_inst_227_,
        v_inst_228_,
        v_xs_229_,
        v_ys_230_,
    );
    v_r_232_ = crate::leanh::lean_box((v_res_231_) as usize);
    return v_r_232_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Lex(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Lex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Lex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lex_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lex_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lex_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Lex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Lex(builtin);
}
