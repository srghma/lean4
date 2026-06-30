// Lean compiler output
// Module: Init.Data.Vector.Lemmas
// Imports: Init.Data.Array.Basic Init.Data.Vector.Basic Init.Data.Vector.Basic Init.Data.List.MapIdx Init.ByCases Init.Data.Array.Bootstrap Init.Data.Array.Count Init.Data.Array.Find Init.Data.Array.OfFn Init.Data.Bool Init.Data.Fin.Lemmas Init.Data.List.TakeDrop Init.Data.Nat.Simproc Init.TacticsExtra
use crate::ffi::lean_array_fget_borrowed;
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l_Array_contains___redArg,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Count::{
    initialize_Init_Data_Array_Count, runtime_initialize_Init_Data_Array_Count,
};
use crate::r#gen::Init::Data::Array::Find::{
    initialize_Init_Data_Array_Find, runtime_initialize_Init_Data_Array_Find,
};
use crate::r#gen::Init::Data::Array::OfFn::{
    initialize_Init_Data_Array_OfFn, runtime_initialize_Init_Data_Array_OfFn,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::MapIdx::{
    initialize_Init_Data_List_MapIdx, runtime_initialize_Init_Data_List_MapIdx,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    l_Nat_decidableBallLT___redArg, l_Nat_decidableExistsLT_x27___redArg,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
pub unsafe fn l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(
    mut v_xs_160_: *mut leanh::LeanObject,
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_n_162_: *mut leanh::LeanObject,
    mut v_h_163_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: u8 = 0;
    v___x_164_ = lean_array_fget_borrowed(v_xs_160_, v_n_162_);
    leanh::lean_inc(v___x_164_);
    v___x_165_ = leanh::lean_apply_1(v_inst_161_, v___x_164_);
    v___x_166_ = (leanh::lean_unbox(v___x_165_) as u8);
    return v___x_166_;
}
pub unsafe fn l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(
    mut v_xs_167_: *mut leanh::LeanObject,
    mut v_inst_168_: *mut leanh::LeanObject,
    mut v_n_169_: *mut leanh::LeanObject,
    mut v_h_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_171_: u8 = 0;
    let mut v_r_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_171_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(
        v_xs_167_,
        v_inst_168_,
        v_n_169_,
        v_h_170_,
    );
    leanh::lean_dec(v_n_169_);
    leanh::lean_dec_ref(v_xs_167_);
    v_r_172_ = leanh::lean_box((v_res_171_) as usize);
    return v_r_172_;
}
pub unsafe fn l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(
    mut v_n_173_: *mut leanh::LeanObject,
    mut v_xs_174_: *mut leanh::LeanObject,
    mut v_inst_175_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: u8 = 0;
    v___f_176_ = leanh::lean_alloc_closure(
        l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_176_, 0, v_xs_174_);
    leanh::lean_closure_set(v___f_176_, 1, v_inst_175_);
    v___x_177_ = l_Nat_decidableBallLT___redArg(v_n_173_, v___f_176_);
    return v___x_177_;
}
pub unsafe fn l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(
    mut v_n_178_: *mut leanh::LeanObject,
    mut v_xs_179_: *mut leanh::LeanObject,
    mut v_inst_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_181_: u8 = 0;
    let mut v_r_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(
        v_n_178_,
        v_xs_179_,
        v_inst_180_,
    );
    leanh::lean_dec(v_n_178_);
    v_r_182_ = leanh::lean_box((v_res_181_) as usize);
    return v_r_182_;
}
pub unsafe fn l_Vector_instDecidableForallForallMemOfDecidablePred(
    mut v_00_u03b1_183_: *mut leanh::LeanObject,
    mut v_n_184_: *mut leanh::LeanObject,
    mut v_xs_185_: *mut leanh::LeanObject,
    mut v_p_186_: *mut leanh::LeanObject,
    mut v_inst_187_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_188_: u8 = 0;
    v___x_188_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(
        v_n_184_,
        v_xs_185_,
        v_inst_187_,
    );
    return v___x_188_;
}
pub unsafe fn l_Vector_instDecidableForallForallMemOfDecidablePred___boxed(
    mut v_00_u03b1_189_: *mut leanh::LeanObject,
    mut v_n_190_: *mut leanh::LeanObject,
    mut v_xs_191_: *mut leanh::LeanObject,
    mut v_p_192_: *mut leanh::LeanObject,
    mut v_inst_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_194_: u8 = 0;
    let mut v_r_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Vector_instDecidableForallForallMemOfDecidablePred(
        v_00_u03b1_189_,
        v_n_190_,
        v_xs_191_,
        v_p_192_,
        v_inst_193_,
    );
    leanh::lean_dec(v_n_190_);
    v_r_195_ = leanh::lean_box((v_res_194_) as usize);
    return v_r_195_;
}
pub unsafe fn l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(
    mut v_xs_196_: *mut leanh::LeanObject,
    mut v_inst_197_: *mut leanh::LeanObject,
    mut v_m_198_: *mut leanh::LeanObject,
    mut v_h_199_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: u8 = 0;
    v___x_200_ = lean_array_fget_borrowed(v_xs_196_, v_m_198_);
    leanh::lean_inc(v___x_200_);
    v___x_201_ = leanh::lean_apply_1(v_inst_197_, v___x_200_);
    v___x_202_ = (leanh::lean_unbox(v___x_201_) as u8);
    return v___x_202_;
}
pub unsafe fn l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed(
    mut v_xs_203_: *mut leanh::LeanObject,
    mut v_inst_204_: *mut leanh::LeanObject,
    mut v_m_205_: *mut leanh::LeanObject,
    mut v_h_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_207_: u8 = 0;
    let mut v_r_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_207_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(
        v_xs_203_,
        v_inst_204_,
        v_m_205_,
        v_h_206_,
    );
    leanh::lean_dec(v_m_205_);
    leanh::lean_dec_ref(v_xs_203_);
    v_r_208_ = leanh::lean_box((v_res_207_) as usize);
    return v_r_208_;
}
pub unsafe fn l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(
    mut v_n_209_: *mut leanh::LeanObject,
    mut v_xs_210_: *mut leanh::LeanObject,
    mut v_inst_211_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: u8 = 0;
    v___f_212_ = leanh::lean_alloc_closure(
        l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_212_, 0, v_xs_210_);
    leanh::lean_closure_set(v___f_212_, 1, v_inst_211_);
    v___x_213_ = l_Nat_decidableExistsLT_x27___redArg(v_n_209_, v___f_212_);
    return v___x_213_;
}
pub unsafe fn l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(
    mut v_n_214_: *mut leanh::LeanObject,
    mut v_xs_215_: *mut leanh::LeanObject,
    mut v_inst_216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_217_: u8 = 0;
    let mut v_r_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_217_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(
        v_n_214_,
        v_xs_215_,
        v_inst_216_,
    );
    leanh::lean_dec(v_n_214_);
    v_r_218_ = leanh::lean_box((v_res_217_) as usize);
    return v_r_218_;
}
pub unsafe fn l_Vector_instDecidableExistsAndMemOfDecidablePred(
    mut v_00_u03b1_219_: *mut leanh::LeanObject,
    mut v_n_220_: *mut leanh::LeanObject,
    mut v_xs_221_: *mut leanh::LeanObject,
    mut v_p_222_: *mut leanh::LeanObject,
    mut v_inst_223_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_224_: u8 = 0;
    v___x_224_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(
        v_n_220_,
        v_xs_221_,
        v_inst_223_,
    );
    return v___x_224_;
}
pub unsafe fn l_Vector_instDecidableExistsAndMemOfDecidablePred___boxed(
    mut v_00_u03b1_225_: *mut leanh::LeanObject,
    mut v_n_226_: *mut leanh::LeanObject,
    mut v_xs_227_: *mut leanh::LeanObject,
    mut v_p_228_: *mut leanh::LeanObject,
    mut v_inst_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_230_: u8 = 0;
    let mut v_r_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Vector_instDecidableExistsAndMemOfDecidablePred(
        v_00_u03b1_225_,
        v_n_226_,
        v_xs_227_,
        v_p_228_,
        v_inst_229_,
    );
    leanh::lean_dec(v_n_226_);
    v_r_231_ = leanh::lean_box((v_res_230_) as usize);
    return v_r_231_;
}
pub unsafe fn l_Vector_instDecidableMemOfLawfulBEq___redArg(
    mut v_inst_232_: *mut leanh::LeanObject,
    mut v_a_233_: *mut leanh::LeanObject,
    mut v_as_234_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_235_: u8 = 0;
    v___x_235_ = l_Array_contains___redArg(v_inst_232_, v_as_234_, v_a_233_);
    return v___x_235_;
}
pub unsafe fn l_Vector_instDecidableMemOfLawfulBEq___redArg___boxed(
    mut v_inst_236_: *mut leanh::LeanObject,
    mut v_a_237_: *mut leanh::LeanObject,
    mut v_as_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_239_: u8 = 0;
    let mut v_r_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_239_ = l_Vector_instDecidableMemOfLawfulBEq___redArg(v_inst_236_, v_a_237_, v_as_238_);
    v_r_240_ = leanh::lean_box((v_res_239_) as usize);
    return v_r_240_;
}
pub unsafe fn l_Vector_instDecidableMemOfLawfulBEq(
    mut v_00_u03b1_241_: *mut leanh::LeanObject,
    mut v_n_242_: *mut leanh::LeanObject,
    mut v_inst_243_: *mut leanh::LeanObject,
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_a_245_: *mut leanh::LeanObject,
    mut v_as_246_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_247_: u8 = 0;
    v___x_247_ = l_Array_contains___redArg(v_inst_243_, v_as_246_, v_a_245_);
    return v___x_247_;
}
pub unsafe fn l_Vector_instDecidableMemOfLawfulBEq___boxed(
    mut v_00_u03b1_248_: *mut leanh::LeanObject,
    mut v_n_249_: *mut leanh::LeanObject,
    mut v_inst_250_: *mut leanh::LeanObject,
    mut v_inst_251_: *mut leanh::LeanObject,
    mut v_a_252_: *mut leanh::LeanObject,
    mut v_as_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_254_: u8 = 0;
    let mut v_r_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Vector_instDecidableMemOfLawfulBEq(
        v_00_u03b1_248_,
        v_n_249_,
        v_inst_250_,
        v_inst_251_,
        v_a_252_,
        v_as_253_,
    );
    leanh::lean_dec(v_n_249_);
    v_r_255_ = leanh::lean_box((v_res_254_) as usize);
    return v_r_255_;
}
pub unsafe fn l_Vector_instDecidableForallVectorZero___redArg(mut v_x_256_: u8) -> u8 {
    return v_x_256_;
}
pub unsafe fn l_Vector_instDecidableForallVectorZero___redArg___boxed(
    mut v_x_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18__boxed_258_: u8 = 0;
    let mut v_res_259_: u8 = 0;
    let mut v_r_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_258_ = (leanh::lean_unbox(v_x_257_) as u8);
    v_res_259_ = l_Vector_instDecidableForallVectorZero___redArg(v_x_18__boxed_258_);
    v_r_260_ = leanh::lean_box((v_res_259_) as usize);
    return v_r_260_;
}
pub unsafe fn l_Vector_instDecidableForallVectorZero(
    mut v_00_u03b1_261_: *mut leanh::LeanObject,
    mut v_P_262_: *mut leanh::LeanObject,
    mut v_x_263_: u8,
) -> u8 {
    return v_x_263_;
}
pub unsafe fn l_Vector_instDecidableForallVectorZero___boxed(
    mut v_00_u03b1_264_: *mut leanh::LeanObject,
    mut v_P_265_: *mut leanh::LeanObject,
    mut v_x_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_267_: u8 = 0;
    let mut v_res_268_: u8 = 0;
    let mut v_r_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_267_ = (leanh::lean_unbox(v_x_266_) as u8);
    v_res_268_ =
        l_Vector_instDecidableForallVectorZero(v_00_u03b1_264_, v_P_265_, v_x_21__boxed_267_);
    v_r_269_ = leanh::lean_box((v_res_268_) as usize);
    return v_r_269_;
}
pub unsafe fn l_Vector_instDecidableForallVectorSucc___redArg(mut v_inst_270_: u8) -> u8 {
    return v_inst_270_;
}
pub unsafe fn l_Vector_instDecidableForallVectorSucc___redArg___boxed(
    mut v_inst_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_8__boxed_272_: u8 = 0;
    let mut v_res_273_: u8 = 0;
    let mut v_r_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_272_ = (leanh::lean_unbox(v_inst_271_) as u8);
    v_res_273_ = l_Vector_instDecidableForallVectorSucc___redArg(v_inst_8__boxed_272_);
    v_r_274_ = leanh::lean_box((v_res_273_) as usize);
    return v_r_274_;
}
pub unsafe fn l_Vector_instDecidableForallVectorSucc(
    mut v_00_u03b1_275_: *mut leanh::LeanObject,
    mut v_n_276_: *mut leanh::LeanObject,
    mut v_P_277_: *mut leanh::LeanObject,
    mut v_inst_278_: u8,
) -> u8 {
    return v_inst_278_;
}
pub unsafe fn l_Vector_instDecidableForallVectorSucc___boxed(
    mut v_00_u03b1_279_: *mut leanh::LeanObject,
    mut v_n_280_: *mut leanh::LeanObject,
    mut v_P_281_: *mut leanh::LeanObject,
    mut v_inst_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_11__boxed_283_: u8 = 0;
    let mut v_res_284_: u8 = 0;
    let mut v_r_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_11__boxed_283_ = (leanh::lean_unbox(v_inst_282_) as u8);
    v_res_284_ = l_Vector_instDecidableForallVectorSucc(
        v_00_u03b1_279_,
        v_n_280_,
        v_P_281_,
        v_inst_11__boxed_283_,
    );
    leanh::lean_dec(v_n_280_);
    v_r_285_ = leanh::lean_box((v_res_284_) as usize);
    return v_r_285_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorZero___redArg(mut v_inst_286_: u8) -> u8 {
    return v_inst_286_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorZero___redArg___boxed(
    mut v_inst_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_27__boxed_288_: u8 = 0;
    let mut v_res_289_: u8 = 0;
    let mut v_r_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_27__boxed_288_ = (leanh::lean_unbox(v_inst_287_) as u8);
    v_res_289_ = l_Vector_instDecidableExistsVectorZero___redArg(v_inst_27__boxed_288_);
    v_r_290_ = leanh::lean_box((v_res_289_) as usize);
    return v_r_290_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorZero(
    mut v_00_u03b1_291_: *mut leanh::LeanObject,
    mut v_P_292_: *mut leanh::LeanObject,
    mut v_inst_293_: u8,
) -> u8 {
    return v_inst_293_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorZero___boxed(
    mut v_00_u03b1_294_: *mut leanh::LeanObject,
    mut v_P_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_30__boxed_297_: u8 = 0;
    let mut v_res_298_: u8 = 0;
    let mut v_r_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_30__boxed_297_ = (leanh::lean_unbox(v_inst_296_) as u8);
    v_res_298_ =
        l_Vector_instDecidableExistsVectorZero(v_00_u03b1_294_, v_P_295_, v_inst_30__boxed_297_);
    v_r_299_ = leanh::lean_box((v_res_298_) as usize);
    return v_r_299_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorSucc___redArg(mut v_inst_300_: u8) -> u8 {
    if v_inst_300_ == 0 {
        let mut v___x_301_: u8 = 0;
        v___x_301_ = 1;
        return v___x_301_;
    } else {
        let mut v___x_302_: u8 = 0;
        v___x_302_ = 0;
        return v___x_302_;
    }
}
pub unsafe fn l_Vector_instDecidableExistsVectorSucc___redArg___boxed(
    mut v_inst_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_14__boxed_304_: u8 = 0;
    let mut v_res_305_: u8 = 0;
    let mut v_r_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_14__boxed_304_ = (leanh::lean_unbox(v_inst_303_) as u8);
    v_res_305_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_14__boxed_304_);
    v_r_306_ = leanh::lean_box((v_res_305_) as usize);
    return v_r_306_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorSucc(
    mut v_00_u03b1_307_: *mut leanh::LeanObject,
    mut v_n_308_: *mut leanh::LeanObject,
    mut v_P_309_: *mut leanh::LeanObject,
    mut v_inst_310_: u8,
) -> u8 {
    let mut v___x_311_: u8 = 0;
    v___x_311_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_310_);
    return v___x_311_;
}
pub unsafe fn l_Vector_instDecidableExistsVectorSucc___boxed(
    mut v_00_u03b1_312_: *mut leanh::LeanObject,
    mut v_n_313_: *mut leanh::LeanObject,
    mut v_P_314_: *mut leanh::LeanObject,
    mut v_inst_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_21__boxed_316_: u8 = 0;
    let mut v_res_317_: u8 = 0;
    let mut v_r_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_21__boxed_316_ = (leanh::lean_unbox(v_inst_315_) as u8);
    v_res_317_ = l_Vector_instDecidableExistsVectorSucc(
        v_00_u03b1_312_,
        v_n_313_,
        v_P_314_,
        v_inst_21__boxed_316_,
    );
    leanh::lean_dec(v_n_313_);
    v_r_318_ = leanh::lean_box((v_res_317_) as usize);
    return v_r_318_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MapIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Count(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_OfFn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Lemmas(
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
pub unsafe fn initialize_Init_Data_Vector_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MapIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Count(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_OfFn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Lemmas(builtin);
}