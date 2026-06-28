// Lean compiler output
// Module: Init.Data.List.Sublist
// Imports: Init.BinderPredicates Init.Ext Init.PropLemmas Init.Data.Bool Init.Data.List.Lemmas Init.Data.List.TakeDrop Init.TacticsExtra
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_isInfixOf__internal___redArg, l_List_isPrefixOf___redArg, l_List_isSublist___redArg,
    l_List_isSuffixOf___redArg,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_List_instTransSubsetMem(mut v_00_u03b1_157_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    v___x_158_ = lean_box(0);
    return v___x_158_;
}
pub unsafe fn l_List_instTransSubset(mut v_00_u03b1_159_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    v___x_160_ = lean_box(0);
    return v___x_160_;
}
pub unsafe fn l_List_instTransSublist(mut v_00_u03b1_161_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    v___x_162_ = lean_box(0);
    return v___x_162_;
}
pub unsafe fn l_List_instTransSublistSubset(
    mut v_00_u03b1_163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    v___x_164_ = lean_box(0);
    return v___x_164_;
}
pub unsafe fn l_List_instTransSubsetSublist(
    mut v_00_u03b1_165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    v___x_166_ = lean_box(0);
    return v___x_166_;
}
pub unsafe fn l_List_instTransSublistMem(mut v_00_u03b1_167_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ = lean_box(0);
    return v___x_168_;
}
pub unsafe fn l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_169_: *mut LeanObject,
    mut v_h__1_170_: *mut LeanObject,
    mut v_h__2_171_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_169_) == 0 {
        let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_171_);
        v___x_172_ = lean_box(0);
        v___x_173_ = lean_apply_1(v_h__1_170_, v___x_172_);
        return v___x_173_;
    } else {
        let mut v_val_174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_170_);
        v_val_174_ = lean_ctor_get(v_x_169_, 0);
        lean_inc(v_val_174_);
        lean_dec_ref_known(v_x_169_, 1);
        v___x_175_ = lean_apply_1(v_h__2_171_, v_val_174_);
        return v___x_175_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sublist_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_176_: *mut LeanObject,
    mut v_motive_177_: *mut LeanObject,
    mut v_x_178_: *mut LeanObject,
    mut v_h__1_179_: *mut LeanObject,
    mut v_h__2_180_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_178_) == 0 {
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_180_);
        v___x_181_ = lean_box(0);
        v___x_182_ = lean_apply_1(v_h__1_179_, v___x_181_);
        return v___x_182_;
    } else {
        let mut v_val_183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_179_);
        v_val_183_ = lean_ctor_get(v_x_178_, 0);
        lean_inc(v_val_183_);
        lean_dec_ref_known(v_x_178_, 1);
        v___x_184_ = lean_apply_1(v_h__2_180_, v_val_183_);
        return v___x_184_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter___redArg(
    mut v_x_185_: *mut LeanObject,
    mut v_x_186_: *mut LeanObject,
    mut v_h__1_187_: *mut LeanObject,
    mut v_h__2_188_: *mut LeanObject,
    mut v_h__3_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_185_) == 0 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_189_);
        lean_dec(v_h__2_188_);
        v___x_190_ = lean_apply_1(v_h__1_187_, v_x_186_);
        return v___x_190_;
    } else {
        lean_dec(v_h__1_187_);
        if lean_obj_tag(v_x_186_) == 0 {
            let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_189_);
            v___x_191_ = lean_apply_2(v_h__2_188_, v_x_185_, lean_box(0));
            return v___x_191_;
        } else {
            let mut v_head_192_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_193_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_194_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_195_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_188_);
            v_head_192_ = lean_ctor_get(v_x_185_, 0);
            lean_inc(v_head_192_);
            v_tail_193_ = lean_ctor_get(v_x_185_, 1);
            lean_inc(v_tail_193_);
            lean_dec_ref_known(v_x_185_, 2);
            v_head_194_ = lean_ctor_get(v_x_186_, 0);
            lean_inc(v_head_194_);
            v_tail_195_ = lean_ctor_get(v_x_186_, 1);
            lean_inc(v_tail_195_);
            lean_dec_ref_known(v_x_186_, 2);
            v___x_196_ = lean_apply_4(
                v_h__3_189_,
                v_head_192_,
                v_tail_193_,
                v_head_194_,
                v_tail_195_,
            );
            return v___x_196_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sublist_0__List_isSublist_match__1_splitter(
    mut v_00_u03b1_197_: *mut LeanObject,
    mut v_motive_198_: *mut LeanObject,
    mut v_x_199_: *mut LeanObject,
    mut v_x_200_: *mut LeanObject,
    mut v_h__1_201_: *mut LeanObject,
    mut v_h__2_202_: *mut LeanObject,
    mut v_h__3_203_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_199_) == 0 {
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_203_);
        lean_dec(v_h__2_202_);
        v___x_204_ = lean_apply_1(v_h__1_201_, v_x_200_);
        return v___x_204_;
    } else {
        lean_dec(v_h__1_201_);
        if lean_obj_tag(v_x_200_) == 0 {
            let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_203_);
            v___x_205_ = lean_apply_2(v_h__2_202_, v_x_199_, lean_box(0));
            return v___x_205_;
        } else {
            let mut v_head_206_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_207_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_208_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_202_);
            v_head_206_ = lean_ctor_get(v_x_199_, 0);
            lean_inc(v_head_206_);
            v_tail_207_ = lean_ctor_get(v_x_199_, 1);
            lean_inc(v_tail_207_);
            lean_dec_ref_known(v_x_199_, 2);
            v_head_208_ = lean_ctor_get(v_x_200_, 0);
            lean_inc(v_head_208_);
            v_tail_209_ = lean_ctor_get(v_x_200_, 1);
            lean_inc(v_tail_209_);
            lean_dec_ref_known(v_x_200_, 2);
            v___x_210_ = lean_apply_4(
                v_h__3_203_,
                v_head_206_,
                v_tail_207_,
                v_head_208_,
                v_tail_209_,
            );
            return v___x_210_;
        }
    }
}
pub unsafe fn l_List_instDecidableSublistOfDecidableEq___redArg(
    mut v_inst_211_: *mut LeanObject,
    mut v_l_u2081_212_: *mut LeanObject,
    mut v_l_u2082_213_: *mut LeanObject,
) -> u8 {
    let mut v___f_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    v___f_214_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_214_, 0, v_inst_211_);
    v___x_215_ = l_List_isSublist___redArg(v___f_214_, v_l_u2081_212_, v_l_u2082_213_);
    return v___x_215_;
}
pub unsafe fn l_List_instDecidableSublistOfDecidableEq___redArg___boxed(
    mut v_inst_216_: *mut LeanObject,
    mut v_l_u2081_217_: *mut LeanObject,
    mut v_l_u2082_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_219_: u8 = 0;
    let mut v_r_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_219_ = l_List_instDecidableSublistOfDecidableEq___redArg(
        v_inst_216_,
        v_l_u2081_217_,
        v_l_u2082_218_,
    );
    v_r_220_ = lean_box((v_res_219_) as usize);
    return v_r_220_;
}
pub unsafe fn l_List_instDecidableSublistOfDecidableEq(
    mut v_00_u03b1_221_: *mut LeanObject,
    mut v_inst_222_: *mut LeanObject,
    mut v_l_u2081_223_: *mut LeanObject,
    mut v_l_u2082_224_: *mut LeanObject,
) -> u8 {
    let mut v___x_225_: u8 = 0;
    v___x_225_ = l_List_instDecidableSublistOfDecidableEq___redArg(
        v_inst_222_,
        v_l_u2081_223_,
        v_l_u2082_224_,
    );
    return v___x_225_;
}
pub unsafe fn l_List_instDecidableSublistOfDecidableEq___boxed(
    mut v_00_u03b1_226_: *mut LeanObject,
    mut v_inst_227_: *mut LeanObject,
    mut v_l_u2081_228_: *mut LeanObject,
    mut v_l_u2082_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_230_: u8 = 0;
    let mut v_r_231_: *mut LeanObject = core::ptr::null_mut();
    v_res_230_ = l_List_instDecidableSublistOfDecidableEq(
        v_00_u03b1_226_,
        v_inst_227_,
        v_l_u2081_228_,
        v_l_u2082_229_,
    );
    v_r_231_ = lean_box((v_res_230_) as usize);
    return v_r_231_;
}
pub unsafe fn l_List_instDecidableIsPrefixOfDecidableEq___redArg(
    mut v_inst_232_: *mut LeanObject,
    mut v_l_u2081_233_: *mut LeanObject,
    mut v_l_u2082_234_: *mut LeanObject,
) -> u8 {
    let mut v___f_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: u8 = 0;
    v___f_235_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_235_, 0, v_inst_232_);
    v___x_236_ = l_List_isPrefixOf___redArg(v___f_235_, v_l_u2081_233_, v_l_u2082_234_);
    return v___x_236_;
}
pub unsafe fn l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(
    mut v_inst_237_: *mut LeanObject,
    mut v_l_u2081_238_: *mut LeanObject,
    mut v_l_u2082_239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_240_: u8 = 0;
    let mut v_r_241_: *mut LeanObject = core::ptr::null_mut();
    v_res_240_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(
        v_inst_237_,
        v_l_u2081_238_,
        v_l_u2082_239_,
    );
    v_r_241_ = lean_box((v_res_240_) as usize);
    return v_r_241_;
}
pub unsafe fn l_List_instDecidableIsPrefixOfDecidableEq(
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_inst_243_: *mut LeanObject,
    mut v_l_u2081_244_: *mut LeanObject,
    mut v_l_u2082_245_: *mut LeanObject,
) -> u8 {
    let mut v___x_246_: u8 = 0;
    v___x_246_ = l_List_instDecidableIsPrefixOfDecidableEq___redArg(
        v_inst_243_,
        v_l_u2081_244_,
        v_l_u2082_245_,
    );
    return v___x_246_;
}
pub unsafe fn l_List_instDecidableIsPrefixOfDecidableEq___boxed(
    mut v_00_u03b1_247_: *mut LeanObject,
    mut v_inst_248_: *mut LeanObject,
    mut v_l_u2081_249_: *mut LeanObject,
    mut v_l_u2082_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_251_: u8 = 0;
    let mut v_r_252_: *mut LeanObject = core::ptr::null_mut();
    v_res_251_ = l_List_instDecidableIsPrefixOfDecidableEq(
        v_00_u03b1_247_,
        v_inst_248_,
        v_l_u2081_249_,
        v_l_u2082_250_,
    );
    v_r_252_ = lean_box((v_res_251_) as usize);
    return v_r_252_;
}
pub unsafe fn l_List_instDecidableIsSuffixOfDecidableEq___redArg(
    mut v_inst_253_: *mut LeanObject,
    mut v_l_u2081_254_: *mut LeanObject,
    mut v_l_u2082_255_: *mut LeanObject,
) -> u8 {
    let mut v___f_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: u8 = 0;
    v___f_256_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_256_, 0, v_inst_253_);
    v___x_257_ = l_List_isSuffixOf___redArg(v___f_256_, v_l_u2081_254_, v_l_u2082_255_);
    return v___x_257_;
}
pub unsafe fn l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(
    mut v_inst_258_: *mut LeanObject,
    mut v_l_u2081_259_: *mut LeanObject,
    mut v_l_u2082_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: u8 = 0;
    let mut v_r_262_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(
        v_inst_258_,
        v_l_u2081_259_,
        v_l_u2082_260_,
    );
    v_r_262_ = lean_box((v_res_261_) as usize);
    return v_r_262_;
}
pub unsafe fn l_List_instDecidableIsSuffixOfDecidableEq(
    mut v_00_u03b1_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
    mut v_l_u2081_265_: *mut LeanObject,
    mut v_l_u2082_266_: *mut LeanObject,
) -> u8 {
    let mut v___x_267_: u8 = 0;
    v___x_267_ = l_List_instDecidableIsSuffixOfDecidableEq___redArg(
        v_inst_264_,
        v_l_u2081_265_,
        v_l_u2082_266_,
    );
    return v___x_267_;
}
pub unsafe fn l_List_instDecidableIsSuffixOfDecidableEq___boxed(
    mut v_00_u03b1_268_: *mut LeanObject,
    mut v_inst_269_: *mut LeanObject,
    mut v_l_u2081_270_: *mut LeanObject,
    mut v_l_u2082_271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_272_: u8 = 0;
    let mut v_r_273_: *mut LeanObject = core::ptr::null_mut();
    v_res_272_ = l_List_instDecidableIsSuffixOfDecidableEq(
        v_00_u03b1_268_,
        v_inst_269_,
        v_l_u2081_270_,
        v_l_u2082_271_,
    );
    v_r_273_ = lean_box((v_res_272_) as usize);
    return v_r_273_;
}
pub unsafe fn l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_274_) == 0 {
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_276_);
        v___x_277_ = lean_box(0);
        v___x_278_ = lean_apply_1(v_h__1_275_, v___x_277_);
        return v___x_278_;
    } else {
        let mut v_head_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_275_);
        v_head_279_ = lean_ctor_get(v_x_274_, 0);
        lean_inc(v_head_279_);
        v_tail_280_ = lean_ctor_get(v_x_274_, 1);
        lean_inc(v_tail_280_);
        lean_dec_ref_known(v_x_274_, 2);
        v___x_281_ = lean_apply_2(v_h__2_276_, v_head_279_, v_tail_280_);
        return v___x_281_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sublist_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_282_: *mut LeanObject,
    mut v_motive_283_: *mut LeanObject,
    mut v_x_284_: *mut LeanObject,
    mut v_h__1_285_: *mut LeanObject,
    mut v_h__2_286_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_284_) == 0 {
        let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_286_);
        v___x_287_ = lean_box(0);
        v___x_288_ = lean_apply_1(v_h__1_285_, v___x_287_);
        return v___x_288_;
    } else {
        let mut v_head_289_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_285_);
        v_head_289_ = lean_ctor_get(v_x_284_, 0);
        lean_inc(v_head_289_);
        v_tail_290_ = lean_ctor_get(v_x_284_, 1);
        lean_inc(v_tail_290_);
        lean_dec_ref_known(v_x_284_, 2);
        v___x_291_ = lean_apply_2(v_h__2_286_, v_head_289_, v_tail_290_);
        return v___x_291_;
    }
}
pub unsafe fn l_List_instDecidableIsInfixOfDecidableEq___redArg(
    mut v_inst_292_: *mut LeanObject,
    mut v_l_u2081_293_: *mut LeanObject,
    mut v_l_u2082_294_: *mut LeanObject,
) -> u8 {
    let mut v___f_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: u8 = 0;
    v___f_295_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_295_, 0, v_inst_292_);
    v___x_296_ = l_List_isInfixOf__internal___redArg(v___f_295_, v_l_u2081_293_, v_l_u2082_294_);
    return v___x_296_;
}
pub unsafe fn l_List_instDecidableIsInfixOfDecidableEq___redArg___boxed(
    mut v_inst_297_: *mut LeanObject,
    mut v_l_u2081_298_: *mut LeanObject,
    mut v_l_u2082_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_300_: u8 = 0;
    let mut v_r_301_: *mut LeanObject = core::ptr::null_mut();
    v_res_300_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(
        v_inst_297_,
        v_l_u2081_298_,
        v_l_u2082_299_,
    );
    v_r_301_ = lean_box((v_res_300_) as usize);
    return v_r_301_;
}
pub unsafe fn l_List_instDecidableIsInfixOfDecidableEq(
    mut v_00_u03b1_302_: *mut LeanObject,
    mut v_inst_303_: *mut LeanObject,
    mut v_l_u2081_304_: *mut LeanObject,
    mut v_l_u2082_305_: *mut LeanObject,
) -> u8 {
    let mut v___x_306_: u8 = 0;
    v___x_306_ = l_List_instDecidableIsInfixOfDecidableEq___redArg(
        v_inst_303_,
        v_l_u2081_304_,
        v_l_u2082_305_,
    );
    return v___x_306_;
}
pub unsafe fn l_List_instDecidableIsInfixOfDecidableEq___boxed(
    mut v_00_u03b1_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
    mut v_l_u2081_309_: *mut LeanObject,
    mut v_l_u2082_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_311_: u8 = 0;
    let mut v_r_312_: *mut LeanObject = core::ptr::null_mut();
    v_res_311_ = l_List_instDecidableIsInfixOfDecidableEq(
        v_00_u03b1_307_,
        v_inst_308_,
        v_l_u2081_309_,
        v_l_u2082_310_,
    );
    v_r_312_ = lean_box((v_res_311_) as usize);
    return v_r_312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sublist(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
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
pub unsafe fn meta_initialize_Init_Data_List_Sublist(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Sublist(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Sublist(builtin);
}
