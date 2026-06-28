// Lean compiler output
// Module: Std.Data.DHashMap.Internal.AssocList.Lemmas
// Imports: Std.Data.DHashMap.Internal.AssocList.Basic Std.Data.DHashMap.Internal.AssocList.Basic Std.Data.Internal.List.Associative Init.ByCases Init.Data.Array.Bootstrap
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
    runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
};
use crate::r#gen::Std::Data::Internal::List::Associative::{
    initialize_Std_Data_Internal_List_Associative,
    runtime_initialize_Std_Data_Internal_List_Associative,
};
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(
    mut v_x_203_: *mut crate::leanh::LeanObject,
    mut v_x_204_: *mut crate::leanh::LeanObject,
    mut v_h__1_205_: *mut crate::leanh::LeanObject,
    mut v_h__2_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_204_) == 0 {
        let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_206_);
        v___x_207_ = crate::leanh::lean_apply_1(v_h__1_205_, v_x_203_);
        return v___x_207_;
    } else {
        let mut v_key_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_205_);
        v_key_208_ = crate::leanh::lean_ctor_get(v_x_204_, 0);
        crate::leanh::lean_inc(v_key_208_);
        v_value_209_ = crate::leanh::lean_ctor_get(v_x_204_, 1);
        crate::leanh::lean_inc(v_value_209_);
        v_tail_210_ = crate::leanh::lean_ctor_get(v_x_204_, 2);
        crate::leanh::lean_inc(v_tail_210_);
        crate::leanh::lean_dec_ref_known(v_x_204_, 3);
        v___x_211_ = crate::leanh::lean_apply_4(
            v_h__2_206_,
            v_x_203_,
            v_key_208_,
            v_value_209_,
            v_tail_210_,
        );
        return v___x_211_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(
    mut v_00_u03b1_212_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_214_: *mut crate::leanh::LeanObject,
    mut v_motive_215_: *mut crate::leanh::LeanObject,
    mut v_x_216_: *mut crate::leanh::LeanObject,
    mut v_x_217_: *mut crate::leanh::LeanObject,
    mut v_h__1_218_: *mut crate::leanh::LeanObject,
    mut v_h__2_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_219_);
        v___x_220_ = crate::leanh::lean_apply_1(v_h__1_218_, v_x_216_);
        return v___x_220_;
    } else {
        let mut v_key_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_218_);
        v_key_221_ = crate::leanh::lean_ctor_get(v_x_217_, 0);
        crate::leanh::lean_inc(v_key_221_);
        v_value_222_ = crate::leanh::lean_ctor_get(v_x_217_, 1);
        crate::leanh::lean_inc(v_value_222_);
        v_tail_223_ = crate::leanh::lean_ctor_get(v_x_217_, 2);
        crate::leanh::lean_inc(v_tail_223_);
        crate::leanh::lean_dec_ref_known(v_x_217_, 3);
        v___x_224_ = crate::leanh::lean_apply_4(
            v_h__2_219_,
            v_x_216_,
            v_key_221_,
            v_value_222_,
            v_tail_223_,
        );
        return v___x_224_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter___redArg(
    mut v_x_225_: *mut crate::leanh::LeanObject,
    mut v_h__1_226_: *mut crate::leanh::LeanObject,
    mut v_h__2_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_225_) == 0 {
        let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_227_);
        v___x_228_ = crate::leanh::lean_box(0);
        v___x_229_ = crate::leanh::lean_apply_1(v_h__1_226_, v___x_228_);
        return v___x_229_;
    } else {
        let mut v_key_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_226_);
        v_key_230_ = crate::leanh::lean_ctor_get(v_x_225_, 0);
        crate::leanh::lean_inc(v_key_230_);
        v_value_231_ = crate::leanh::lean_ctor_get(v_x_225_, 1);
        crate::leanh::lean_inc(v_value_231_);
        v_tail_232_ = crate::leanh::lean_ctor_get(v_x_225_, 2);
        crate::leanh::lean_inc(v_tail_232_);
        crate::leanh::lean_dec_ref_known(v_x_225_, 3);
        v___x_233_ = crate::leanh::lean_apply_3(v_h__2_227_, v_key_230_, v_value_231_, v_tail_232_);
        return v___x_233_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter(
    mut v_00_u03b1_234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_235_: *mut crate::leanh::LeanObject,
    mut v_motive_236_: *mut crate::leanh::LeanObject,
    mut v_x_237_: *mut crate::leanh::LeanObject,
    mut v_h__1_238_: *mut crate::leanh::LeanObject,
    mut v_h__2_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_237_) == 0 {
        let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_239_);
        v___x_240_ = crate::leanh::lean_box(0);
        v___x_241_ = crate::leanh::lean_apply_1(v_h__1_238_, v___x_240_);
        return v___x_241_;
    } else {
        let mut v_key_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_238_);
        v_key_242_ = crate::leanh::lean_ctor_get(v_x_237_, 0);
        crate::leanh::lean_inc(v_key_242_);
        v_value_243_ = crate::leanh::lean_ctor_get(v_x_237_, 1);
        crate::leanh::lean_inc(v_value_243_);
        v_tail_244_ = crate::leanh::lean_ctor_get(v_x_237_, 2);
        crate::leanh::lean_inc(v_tail_244_);
        crate::leanh::lean_dec_ref_known(v_x_237_, 3);
        v___x_245_ = crate::leanh::lean_apply_3(v_h__2_239_, v_key_242_, v_value_243_, v_tail_244_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(
    mut v_x_246_: *mut crate::leanh::LeanObject,
    mut v_h__1_247_: *mut crate::leanh::LeanObject,
    mut v_h__2_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_246_) == 0 {
        let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_248_);
        v___x_249_ = crate::leanh::lean_box(0);
        v___x_250_ = crate::leanh::lean_apply_1(v_h__1_247_, v___x_249_);
        return v___x_250_;
    } else {
        let mut v_key_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_247_);
        v_key_251_ = crate::leanh::lean_ctor_get(v_x_246_, 0);
        crate::leanh::lean_inc(v_key_251_);
        v_value_252_ = crate::leanh::lean_ctor_get(v_x_246_, 1);
        crate::leanh::lean_inc(v_value_252_);
        v_tail_253_ = crate::leanh::lean_ctor_get(v_x_246_, 2);
        crate::leanh::lean_inc(v_tail_253_);
        crate::leanh::lean_dec_ref_known(v_x_246_, 3);
        v___x_254_ = crate::leanh::lean_apply_3(v_h__2_248_, v_key_251_, v_value_252_, v_tail_253_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(
    mut v_00_u03b1_255_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_256_: *mut crate::leanh::LeanObject,
    mut v_motive_257_: *mut crate::leanh::LeanObject,
    mut v_x_258_: *mut crate::leanh::LeanObject,
    mut v_h__1_259_: *mut crate::leanh::LeanObject,
    mut v_h__2_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_258_) == 0 {
        let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_260_);
        v___x_261_ = crate::leanh::lean_box(0);
        v___x_262_ = crate::leanh::lean_apply_1(v_h__1_259_, v___x_261_);
        return v___x_262_;
    } else {
        let mut v_key_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_259_);
        v_key_263_ = crate::leanh::lean_ctor_get(v_x_258_, 0);
        crate::leanh::lean_inc(v_key_263_);
        v_value_264_ = crate::leanh::lean_ctor_get(v_x_258_, 1);
        crate::leanh::lean_inc(v_value_264_);
        v_tail_265_ = crate::leanh::lean_ctor_get(v_x_258_, 2);
        crate::leanh::lean_inc(v_tail_265_);
        crate::leanh::lean_dec_ref_known(v_x_258_, 3);
        v___x_266_ = crate::leanh::lean_apply_3(v_h__2_260_, v_key_263_, v_value_264_, v_tail_265_);
        return v___x_266_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(
    mut v_x_267_: *mut crate::leanh::LeanObject,
    mut v_h__1_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_key_269_ = crate::leanh::lean_ctor_get(v_x_267_, 0);
    crate::leanh::lean_inc(v_key_269_);
    v_value_270_ = crate::leanh::lean_ctor_get(v_x_267_, 1);
    crate::leanh::lean_inc(v_value_270_);
    v_tail_271_ = crate::leanh::lean_ctor_get(v_x_267_, 2);
    crate::leanh::lean_inc(v_tail_271_);
    crate::leanh::lean_dec(v_x_267_);
    v___x_272_ = crate::leanh::lean_apply_4(
        v_h__1_268_,
        v_key_269_,
        v_value_270_,
        v_tail_271_,
        crate::leanh::lean_box(0),
    );
    return v___x_272_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(
    mut v_00_u03b1_273_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_274_: *mut crate::leanh::LeanObject,
    mut v_inst_275_: *mut crate::leanh::LeanObject,
    mut v_a_276_: *mut crate::leanh::LeanObject,
    mut v_motive_277_: *mut crate::leanh::LeanObject,
    mut v_x_278_: *mut crate::leanh::LeanObject,
    mut v_x_279_: *mut crate::leanh::LeanObject,
    mut v_h__1_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_key_281_ = crate::leanh::lean_ctor_get(v_x_278_, 0);
    crate::leanh::lean_inc(v_key_281_);
    v_value_282_ = crate::leanh::lean_ctor_get(v_x_278_, 1);
    crate::leanh::lean_inc(v_value_282_);
    v_tail_283_ = crate::leanh::lean_ctor_get(v_x_278_, 2);
    crate::leanh::lean_inc(v_tail_283_);
    crate::leanh::lean_dec(v_x_278_);
    v___x_284_ = crate::leanh::lean_apply_4(
        v_h__1_280_,
        v_key_281_,
        v_value_282_,
        v_tail_283_,
        crate::leanh::lean_box(0),
    );
    return v___x_284_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(
    mut v_00_u03b1_285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_a_288_: *mut crate::leanh::LeanObject,
    mut v_motive_289_: *mut crate::leanh::LeanObject,
    mut v_x_290_: *mut crate::leanh::LeanObject,
    mut v_x_291_: *mut crate::leanh::LeanObject,
    mut v_h__1_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(v_00_u03b1_285_, v_00_u03b2_286_, v_inst_287_, v_a_288_, v_motive_289_, v_x_290_, v_x_291_, v_h__1_292_);
    crate::leanh::lean_dec(v_a_288_);
    crate::leanh::lean_dec_ref(v_inst_287_);
    return v_res_293_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(
    mut v_x_294_: *mut crate::leanh::LeanObject,
    mut v_h__1_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_key_296_ = crate::leanh::lean_ctor_get(v_x_294_, 0);
    crate::leanh::lean_inc(v_key_296_);
    v_value_297_ = crate::leanh::lean_ctor_get(v_x_294_, 1);
    crate::leanh::lean_inc(v_value_297_);
    v_tail_298_ = crate::leanh::lean_ctor_get(v_x_294_, 2);
    crate::leanh::lean_inc(v_tail_298_);
    crate::leanh::lean_dec(v_x_294_);
    v___x_299_ = crate::leanh::lean_apply_4(
        v_h__1_295_,
        v_key_296_,
        v_value_297_,
        v_tail_298_,
        crate::leanh::lean_box(0),
    );
    return v___x_299_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(
    mut v_00_u03b1_300_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_301_: *mut crate::leanh::LeanObject,
    mut v_inst_302_: *mut crate::leanh::LeanObject,
    mut v_a_303_: *mut crate::leanh::LeanObject,
    mut v_motive_304_: *mut crate::leanh::LeanObject,
    mut v_x_305_: *mut crate::leanh::LeanObject,
    mut v_x_306_: *mut crate::leanh::LeanObject,
    mut v_h__1_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_key_308_ = crate::leanh::lean_ctor_get(v_x_305_, 0);
    crate::leanh::lean_inc(v_key_308_);
    v_value_309_ = crate::leanh::lean_ctor_get(v_x_305_, 1);
    crate::leanh::lean_inc(v_value_309_);
    v_tail_310_ = crate::leanh::lean_ctor_get(v_x_305_, 2);
    crate::leanh::lean_inc(v_tail_310_);
    crate::leanh::lean_dec(v_x_305_);
    v___x_311_ = crate::leanh::lean_apply_4(
        v_h__1_307_,
        v_key_308_,
        v_value_309_,
        v_tail_310_,
        crate::leanh::lean_box(0),
    );
    return v___x_311_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(
    mut v_00_u03b1_312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_313_: *mut crate::leanh::LeanObject,
    mut v_inst_314_: *mut crate::leanh::LeanObject,
    mut v_a_315_: *mut crate::leanh::LeanObject,
    mut v_motive_316_: *mut crate::leanh::LeanObject,
    mut v_x_317_: *mut crate::leanh::LeanObject,
    mut v_x_318_: *mut crate::leanh::LeanObject,
    mut v_h__1_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(v_00_u03b1_312_, v_00_u03b2_313_, v_inst_314_, v_a_315_, v_motive_316_, v_x_317_, v_x_318_, v_h__1_319_);
    crate::leanh::lean_dec(v_a_315_);
    crate::leanh::lean_dec_ref(v_inst_314_);
    return v_res_320_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(
    mut v_x_321_: *mut crate::leanh::LeanObject,
    mut v_h__1_322_: *mut crate::leanh::LeanObject,
    mut v_h__2_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_321_) == 0 {
        let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_323_);
        v___x_324_ = crate::leanh::lean_box(0);
        v___x_325_ = crate::leanh::lean_apply_1(v_h__1_322_, v___x_324_);
        return v___x_325_;
    } else {
        let mut v_val_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_322_);
        v_val_326_ = crate::leanh::lean_ctor_get(v_x_321_, 0);
        crate::leanh::lean_inc(v_val_326_);
        crate::leanh::lean_dec_ref_known(v_x_321_, 1);
        v___x_327_ = crate::leanh::lean_apply_1(v_h__2_323_, v_val_326_);
        return v___x_327_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(
    mut v_00_u03b1_328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_329_: *mut crate::leanh::LeanObject,
    mut v_a_330_: *mut crate::leanh::LeanObject,
    mut v_motive_331_: *mut crate::leanh::LeanObject,
    mut v_x_332_: *mut crate::leanh::LeanObject,
    mut v_h__1_333_: *mut crate::leanh::LeanObject,
    mut v_h__2_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_332_) == 0 {
        let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_334_);
        v___x_335_ = crate::leanh::lean_box(0);
        v___x_336_ = crate::leanh::lean_apply_1(v_h__1_333_, v___x_335_);
        return v___x_336_;
    } else {
        let mut v_val_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_333_);
        v_val_337_ = crate::leanh::lean_ctor_get(v_x_332_, 0);
        crate::leanh::lean_inc(v_val_337_);
        crate::leanh::lean_dec_ref_known(v_x_332_, 1);
        v___x_338_ = crate::leanh::lean_apply_1(v_h__2_334_, v_val_337_);
        return v___x_338_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(
    mut v_00_u03b1_339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_340_: *mut crate::leanh::LeanObject,
    mut v_a_341_: *mut crate::leanh::LeanObject,
    mut v_motive_342_: *mut crate::leanh::LeanObject,
    mut v_x_343_: *mut crate::leanh::LeanObject,
    mut v_h__1_344_: *mut crate::leanh::LeanObject,
    mut v_h__2_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(v_00_u03b1_339_, v_00_u03b2_340_, v_a_341_, v_motive_342_, v_x_343_, v_h__1_344_, v_h__2_345_);
    crate::leanh::lean_dec(v_a_341_);
    return v_res_346_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_347_: *mut crate::leanh::LeanObject,
    mut v_h__1_348_: *mut crate::leanh::LeanObject,
    mut v_h__2_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_347_) == 0 {
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_349_);
        v___x_350_ = crate::leanh::lean_box(0);
        v___x_351_ = crate::leanh::lean_apply_1(v_h__1_348_, v___x_350_);
        return v___x_351_;
    } else {
        let mut v_val_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_348_);
        v_val_352_ = crate::leanh::lean_ctor_get(v_x_347_, 0);
        crate::leanh::lean_inc(v_val_352_);
        crate::leanh::lean_dec_ref_known(v_x_347_, 1);
        v___x_353_ = crate::leanh::lean_apply_1(v_h__2_349_, v_val_352_);
        return v___x_353_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_354_: *mut crate::leanh::LeanObject,
    mut v_motive_355_: *mut crate::leanh::LeanObject,
    mut v_x_356_: *mut crate::leanh::LeanObject,
    mut v_h__1_357_: *mut crate::leanh::LeanObject,
    mut v_h__2_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_356_) == 0 {
        let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_358_);
        v___x_359_ = crate::leanh::lean_box(0);
        v___x_360_ = crate::leanh::lean_apply_1(v_h__1_357_, v___x_359_);
        return v___x_360_;
    } else {
        let mut v_val_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_357_);
        v_val_361_ = crate::leanh::lean_ctor_get(v_x_356_, 0);
        crate::leanh::lean_inc(v_val_361_);
        crate::leanh::lean_dec_ref_known(v_x_356_, 1);
        v___x_362_ = crate::leanh::lean_apply_1(v_h__2_358_, v_val_361_);
        return v___x_362_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_363_: *mut crate::leanh::LeanObject,
    mut v_h__1_364_: *mut crate::leanh::LeanObject,
    mut v_h__2_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_363_) == 0 {
        let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_365_);
        v___x_366_ = crate::leanh::lean_box(0);
        v___x_367_ = crate::leanh::lean_apply_1(v_h__1_364_, v___x_366_);
        return v___x_367_;
    } else {
        let mut v_val_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_364_);
        v_val_368_ = crate::leanh::lean_ctor_get(v_x_363_, 0);
        crate::leanh::lean_inc(v_val_368_);
        crate::leanh::lean_dec_ref_known(v_x_363_, 1);
        v___x_369_ = crate::leanh::lean_apply_1(v_h__2_365_, v_val_368_);
        return v___x_369_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_370_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_371_: *mut crate::leanh::LeanObject,
    mut v_k_372_: *mut crate::leanh::LeanObject,
    mut v_motive_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
    mut v_h__1_375_: *mut crate::leanh::LeanObject,
    mut v_h__2_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_374_) == 0 {
        let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_376_);
        v___x_377_ = crate::leanh::lean_box(0);
        v___x_378_ = crate::leanh::lean_apply_1(v_h__1_375_, v___x_377_);
        return v___x_378_;
    } else {
        let mut v_val_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_375_);
        v_val_379_ = crate::leanh::lean_ctor_get(v_x_374_, 0);
        crate::leanh::lean_inc(v_val_379_);
        crate::leanh::lean_dec_ref_known(v_x_374_, 1);
        v___x_380_ = crate::leanh::lean_apply_1(v_h__2_376_, v_val_379_);
        return v___x_380_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_382_: *mut crate::leanh::LeanObject,
    mut v_k_383_: *mut crate::leanh::LeanObject,
    mut v_motive_384_: *mut crate::leanh::LeanObject,
    mut v_x_385_: *mut crate::leanh::LeanObject,
    mut v_h__1_386_: *mut crate::leanh::LeanObject,
    mut v_h__2_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_381_, v_00_u03b2_382_, v_k_383_, v_motive_384_, v_x_385_, v_h__1_386_, v_h__2_387_);
    crate::leanh::lean_dec(v_k_383_);
    return v_res_388_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(
    mut v_x_389_: *mut crate::leanh::LeanObject,
    mut v_h__1_390_: *mut crate::leanh::LeanObject,
    mut v_h__2_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_389_) == 0 {
        let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_391_);
        v___x_392_ = crate::leanh::lean_box(0);
        v___x_393_ = crate::leanh::lean_apply_1(v_h__1_390_, v___x_392_);
        return v___x_393_;
    } else {
        let mut v_val_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_390_);
        v_val_394_ = crate::leanh::lean_ctor_get(v_x_389_, 0);
        crate::leanh::lean_inc(v_val_394_);
        crate::leanh::lean_dec_ref_known(v_x_389_, 1);
        v___x_395_ = crate::leanh::lean_apply_1(v_h__2_391_, v_val_394_);
        return v___x_395_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(
    mut v_00_u03b2_396_: *mut crate::leanh::LeanObject,
    mut v_motive_397_: *mut crate::leanh::LeanObject,
    mut v_x_398_: *mut crate::leanh::LeanObject,
    mut v_h__1_399_: *mut crate::leanh::LeanObject,
    mut v_h__2_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_398_) == 0 {
        let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_400_);
        v___x_401_ = crate::leanh::lean_box(0);
        v___x_402_ = crate::leanh::lean_apply_1(v_h__1_399_, v___x_401_);
        return v___x_402_;
    } else {
        let mut v_val_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_399_);
        v_val_403_ = crate::leanh::lean_ctor_get(v_x_398_, 0);
        crate::leanh::lean_inc(v_val_403_);
        crate::leanh::lean_dec_ref_known(v_x_398_, 1);
        v___x_404_ = crate::leanh::lean_apply_1(v_h__2_400_, v_val_403_);
        return v___x_404_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
}
