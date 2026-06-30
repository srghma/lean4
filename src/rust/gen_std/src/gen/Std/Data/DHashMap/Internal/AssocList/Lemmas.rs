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
    mut v_x_203_: *mut leanh::LeanObject,
    mut v_x_204_: *mut leanh::LeanObject,
    mut v_h__1_205_: *mut leanh::LeanObject,
    mut v_h__2_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_204_) == 0 {
        let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_206_);
        v___x_207_ = leanh::lean_apply_1(v_h__1_205_, v_x_203_);
        return v___x_207_;
    } else {
        let mut v_key_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_205_);
        v_key_208_ = leanh::lean_ctor_get(v_x_204_, 0);
        leanh::lean_inc(v_key_208_);
        v_value_209_ = leanh::lean_ctor_get(v_x_204_, 1);
        leanh::lean_inc(v_value_209_);
        v_tail_210_ = leanh::lean_ctor_get(v_x_204_, 2);
        leanh::lean_inc(v_tail_210_);
        leanh::lean_dec_ref_known(v_x_204_, 3);
        v___x_211_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_212_: *mut leanh::LeanObject,
    mut v_00_u03b2_213_: *mut leanh::LeanObject,
    mut v_00_u03b4_214_: *mut leanh::LeanObject,
    mut v_motive_215_: *mut leanh::LeanObject,
    mut v_x_216_: *mut leanh::LeanObject,
    mut v_x_217_: *mut leanh::LeanObject,
    mut v_h__1_218_: *mut leanh::LeanObject,
    mut v_h__2_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_219_);
        v___x_220_ = leanh::lean_apply_1(v_h__1_218_, v_x_216_);
        return v___x_220_;
    } else {
        let mut v_key_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_218_);
        v_key_221_ = leanh::lean_ctor_get(v_x_217_, 0);
        leanh::lean_inc(v_key_221_);
        v_value_222_ = leanh::lean_ctor_get(v_x_217_, 1);
        leanh::lean_inc(v_value_222_);
        v_tail_223_ = leanh::lean_ctor_get(v_x_217_, 2);
        leanh::lean_inc(v_tail_223_);
        leanh::lean_dec_ref_known(v_x_217_, 3);
        v___x_224_ = leanh::lean_apply_4(
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
    mut v_x_225_: *mut leanh::LeanObject,
    mut v_h__1_226_: *mut leanh::LeanObject,
    mut v_h__2_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_225_) == 0 {
        let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_227_);
        v___x_228_ = leanh::lean_box(0);
        v___x_229_ = leanh::lean_apply_1(v_h__1_226_, v___x_228_);
        return v___x_229_;
    } else {
        let mut v_key_230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_226_);
        v_key_230_ = leanh::lean_ctor_get(v_x_225_, 0);
        leanh::lean_inc(v_key_230_);
        v_value_231_ = leanh::lean_ctor_get(v_x_225_, 1);
        leanh::lean_inc(v_value_231_);
        v_tail_232_ = leanh::lean_ctor_get(v_x_225_, 2);
        leanh::lean_inc(v_tail_232_);
        leanh::lean_dec_ref_known(v_x_225_, 3);
        v___x_233_ = leanh::lean_apply_3(v_h__2_227_, v_key_230_, v_value_231_, v_tail_232_);
        return v___x_233_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter(
    mut v_00_u03b1_234_: *mut leanh::LeanObject,
    mut v_00_u03b2_235_: *mut leanh::LeanObject,
    mut v_motive_236_: *mut leanh::LeanObject,
    mut v_x_237_: *mut leanh::LeanObject,
    mut v_h__1_238_: *mut leanh::LeanObject,
    mut v_h__2_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_237_) == 0 {
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_239_);
        v___x_240_ = leanh::lean_box(0);
        v___x_241_ = leanh::lean_apply_1(v_h__1_238_, v___x_240_);
        return v___x_241_;
    } else {
        let mut v_key_242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_238_);
        v_key_242_ = leanh::lean_ctor_get(v_x_237_, 0);
        leanh::lean_inc(v_key_242_);
        v_value_243_ = leanh::lean_ctor_get(v_x_237_, 1);
        leanh::lean_inc(v_value_243_);
        v_tail_244_ = leanh::lean_ctor_get(v_x_237_, 2);
        leanh::lean_inc(v_tail_244_);
        leanh::lean_dec_ref_known(v_x_237_, 3);
        v___x_245_ = leanh::lean_apply_3(v_h__2_239_, v_key_242_, v_value_243_, v_tail_244_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(
    mut v_x_246_: *mut leanh::LeanObject,
    mut v_h__1_247_: *mut leanh::LeanObject,
    mut v_h__2_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_246_) == 0 {
        let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_248_);
        v___x_249_ = leanh::lean_box(0);
        v___x_250_ = leanh::lean_apply_1(v_h__1_247_, v___x_249_);
        return v___x_250_;
    } else {
        let mut v_key_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_247_);
        v_key_251_ = leanh::lean_ctor_get(v_x_246_, 0);
        leanh::lean_inc(v_key_251_);
        v_value_252_ = leanh::lean_ctor_get(v_x_246_, 1);
        leanh::lean_inc(v_value_252_);
        v_tail_253_ = leanh::lean_ctor_get(v_x_246_, 2);
        leanh::lean_inc(v_tail_253_);
        leanh::lean_dec_ref_known(v_x_246_, 3);
        v___x_254_ = leanh::lean_apply_3(v_h__2_248_, v_key_251_, v_value_252_, v_tail_253_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(
    mut v_00_u03b1_255_: *mut leanh::LeanObject,
    mut v_00_u03b2_256_: *mut leanh::LeanObject,
    mut v_motive_257_: *mut leanh::LeanObject,
    mut v_x_258_: *mut leanh::LeanObject,
    mut v_h__1_259_: *mut leanh::LeanObject,
    mut v_h__2_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_258_) == 0 {
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_260_);
        v___x_261_ = leanh::lean_box(0);
        v___x_262_ = leanh::lean_apply_1(v_h__1_259_, v___x_261_);
        return v___x_262_;
    } else {
        let mut v_key_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_259_);
        v_key_263_ = leanh::lean_ctor_get(v_x_258_, 0);
        leanh::lean_inc(v_key_263_);
        v_value_264_ = leanh::lean_ctor_get(v_x_258_, 1);
        leanh::lean_inc(v_value_264_);
        v_tail_265_ = leanh::lean_ctor_get(v_x_258_, 2);
        leanh::lean_inc(v_tail_265_);
        leanh::lean_dec_ref_known(v_x_258_, 3);
        v___x_266_ = leanh::lean_apply_3(v_h__2_260_, v_key_263_, v_value_264_, v_tail_265_);
        return v___x_266_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(
    mut v_x_267_: *mut leanh::LeanObject,
    mut v_h__1_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_key_269_ = leanh::lean_ctor_get(v_x_267_, 0);
    leanh::lean_inc(v_key_269_);
    v_value_270_ = leanh::lean_ctor_get(v_x_267_, 1);
    leanh::lean_inc(v_value_270_);
    v_tail_271_ = leanh::lean_ctor_get(v_x_267_, 2);
    leanh::lean_inc(v_tail_271_);
    leanh::lean_dec(v_x_267_);
    v___x_272_ = leanh::lean_apply_4(
        v_h__1_268_,
        v_key_269_,
        v_value_270_,
        v_tail_271_,
        leanh::lean_box(0),
    );
    return v___x_272_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(
    mut v_00_u03b1_273_: *mut leanh::LeanObject,
    mut v_00_u03b2_274_: *mut leanh::LeanObject,
    mut v_inst_275_: *mut leanh::LeanObject,
    mut v_a_276_: *mut leanh::LeanObject,
    mut v_motive_277_: *mut leanh::LeanObject,
    mut v_x_278_: *mut leanh::LeanObject,
    mut v_x_279_: *mut leanh::LeanObject,
    mut v_h__1_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_key_281_ = leanh::lean_ctor_get(v_x_278_, 0);
    leanh::lean_inc(v_key_281_);
    v_value_282_ = leanh::lean_ctor_get(v_x_278_, 1);
    leanh::lean_inc(v_value_282_);
    v_tail_283_ = leanh::lean_ctor_get(v_x_278_, 2);
    leanh::lean_inc(v_tail_283_);
    leanh::lean_dec(v_x_278_);
    v___x_284_ = leanh::lean_apply_4(
        v_h__1_280_,
        v_key_281_,
        v_value_282_,
        v_tail_283_,
        leanh::lean_box(0),
    );
    return v___x_284_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(
    mut v_00_u03b1_285_: *mut leanh::LeanObject,
    mut v_00_u03b2_286_: *mut leanh::LeanObject,
    mut v_inst_287_: *mut leanh::LeanObject,
    mut v_a_288_: *mut leanh::LeanObject,
    mut v_motive_289_: *mut leanh::LeanObject,
    mut v_x_290_: *mut leanh::LeanObject,
    mut v_x_291_: *mut leanh::LeanObject,
    mut v_h__1_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(v_00_u03b1_285_, v_00_u03b2_286_, v_inst_287_, v_a_288_, v_motive_289_, v_x_290_, v_x_291_, v_h__1_292_);
    leanh::lean_dec(v_a_288_);
    leanh::lean_dec_ref(v_inst_287_);
    return v_res_293_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_h__1_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_key_296_ = leanh::lean_ctor_get(v_x_294_, 0);
    leanh::lean_inc(v_key_296_);
    v_value_297_ = leanh::lean_ctor_get(v_x_294_, 1);
    leanh::lean_inc(v_value_297_);
    v_tail_298_ = leanh::lean_ctor_get(v_x_294_, 2);
    leanh::lean_inc(v_tail_298_);
    leanh::lean_dec(v_x_294_);
    v___x_299_ = leanh::lean_apply_4(
        v_h__1_295_,
        v_key_296_,
        v_value_297_,
        v_tail_298_,
        leanh::lean_box(0),
    );
    return v___x_299_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(
    mut v_00_u03b1_300_: *mut leanh::LeanObject,
    mut v_00_u03b2_301_: *mut leanh::LeanObject,
    mut v_inst_302_: *mut leanh::LeanObject,
    mut v_a_303_: *mut leanh::LeanObject,
    mut v_motive_304_: *mut leanh::LeanObject,
    mut v_x_305_: *mut leanh::LeanObject,
    mut v_x_306_: *mut leanh::LeanObject,
    mut v_h__1_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_key_308_ = leanh::lean_ctor_get(v_x_305_, 0);
    leanh::lean_inc(v_key_308_);
    v_value_309_ = leanh::lean_ctor_get(v_x_305_, 1);
    leanh::lean_inc(v_value_309_);
    v_tail_310_ = leanh::lean_ctor_get(v_x_305_, 2);
    leanh::lean_inc(v_tail_310_);
    leanh::lean_dec(v_x_305_);
    v___x_311_ = leanh::lean_apply_4(
        v_h__1_307_,
        v_key_308_,
        v_value_309_,
        v_tail_310_,
        leanh::lean_box(0),
    );
    return v___x_311_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(
    mut v_00_u03b1_312_: *mut leanh::LeanObject,
    mut v_00_u03b2_313_: *mut leanh::LeanObject,
    mut v_inst_314_: *mut leanh::LeanObject,
    mut v_a_315_: *mut leanh::LeanObject,
    mut v_motive_316_: *mut leanh::LeanObject,
    mut v_x_317_: *mut leanh::LeanObject,
    mut v_x_318_: *mut leanh::LeanObject,
    mut v_h__1_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(v_00_u03b1_312_, v_00_u03b2_313_, v_inst_314_, v_a_315_, v_motive_316_, v_x_317_, v_x_318_, v_h__1_319_);
    leanh::lean_dec(v_a_315_);
    leanh::lean_dec_ref(v_inst_314_);
    return v_res_320_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(
    mut v_x_321_: *mut leanh::LeanObject,
    mut v_h__1_322_: *mut leanh::LeanObject,
    mut v_h__2_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_321_) == 0 {
        let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_323_);
        v___x_324_ = leanh::lean_box(0);
        v___x_325_ = leanh::lean_apply_1(v_h__1_322_, v___x_324_);
        return v___x_325_;
    } else {
        let mut v_val_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_322_);
        v_val_326_ = leanh::lean_ctor_get(v_x_321_, 0);
        leanh::lean_inc(v_val_326_);
        leanh::lean_dec_ref_known(v_x_321_, 1);
        v___x_327_ = leanh::lean_apply_1(v_h__2_323_, v_val_326_);
        return v___x_327_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(
    mut v_00_u03b1_328_: *mut leanh::LeanObject,
    mut v_00_u03b2_329_: *mut leanh::LeanObject,
    mut v_a_330_: *mut leanh::LeanObject,
    mut v_motive_331_: *mut leanh::LeanObject,
    mut v_x_332_: *mut leanh::LeanObject,
    mut v_h__1_333_: *mut leanh::LeanObject,
    mut v_h__2_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_332_) == 0 {
        let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_334_);
        v___x_335_ = leanh::lean_box(0);
        v___x_336_ = leanh::lean_apply_1(v_h__1_333_, v___x_335_);
        return v___x_336_;
    } else {
        let mut v_val_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_333_);
        v_val_337_ = leanh::lean_ctor_get(v_x_332_, 0);
        leanh::lean_inc(v_val_337_);
        leanh::lean_dec_ref_known(v_x_332_, 1);
        v___x_338_ = leanh::lean_apply_1(v_h__2_334_, v_val_337_);
        return v___x_338_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(
    mut v_00_u03b1_339_: *mut leanh::LeanObject,
    mut v_00_u03b2_340_: *mut leanh::LeanObject,
    mut v_a_341_: *mut leanh::LeanObject,
    mut v_motive_342_: *mut leanh::LeanObject,
    mut v_x_343_: *mut leanh::LeanObject,
    mut v_h__1_344_: *mut leanh::LeanObject,
    mut v_h__2_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(v_00_u03b1_339_, v_00_u03b2_340_, v_a_341_, v_motive_342_, v_x_343_, v_h__1_344_, v_h__2_345_);
    leanh::lean_dec(v_a_341_);
    return v_res_346_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_347_: *mut leanh::LeanObject,
    mut v_h__1_348_: *mut leanh::LeanObject,
    mut v_h__2_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_347_) == 0 {
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_349_);
        v___x_350_ = leanh::lean_box(0);
        v___x_351_ = leanh::lean_apply_1(v_h__1_348_, v___x_350_);
        return v___x_351_;
    } else {
        let mut v_val_352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_348_);
        v_val_352_ = leanh::lean_ctor_get(v_x_347_, 0);
        leanh::lean_inc(v_val_352_);
        leanh::lean_dec_ref_known(v_x_347_, 1);
        v___x_353_ = leanh::lean_apply_1(v_h__2_349_, v_val_352_);
        return v___x_353_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_354_: *mut leanh::LeanObject,
    mut v_motive_355_: *mut leanh::LeanObject,
    mut v_x_356_: *mut leanh::LeanObject,
    mut v_h__1_357_: *mut leanh::LeanObject,
    mut v_h__2_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_356_) == 0 {
        let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_358_);
        v___x_359_ = leanh::lean_box(0);
        v___x_360_ = leanh::lean_apply_1(v_h__1_357_, v___x_359_);
        return v___x_360_;
    } else {
        let mut v_val_361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_357_);
        v_val_361_ = leanh::lean_ctor_get(v_x_356_, 0);
        leanh::lean_inc(v_val_361_);
        leanh::lean_dec_ref_known(v_x_356_, 1);
        v___x_362_ = leanh::lean_apply_1(v_h__2_358_, v_val_361_);
        return v___x_362_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_363_: *mut leanh::LeanObject,
    mut v_h__1_364_: *mut leanh::LeanObject,
    mut v_h__2_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_363_) == 0 {
        let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_365_);
        v___x_366_ = leanh::lean_box(0);
        v___x_367_ = leanh::lean_apply_1(v_h__1_364_, v___x_366_);
        return v___x_367_;
    } else {
        let mut v_val_368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_364_);
        v_val_368_ = leanh::lean_ctor_get(v_x_363_, 0);
        leanh::lean_inc(v_val_368_);
        leanh::lean_dec_ref_known(v_x_363_, 1);
        v___x_369_ = leanh::lean_apply_1(v_h__2_365_, v_val_368_);
        return v___x_369_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_370_: *mut leanh::LeanObject,
    mut v_00_u03b2_371_: *mut leanh::LeanObject,
    mut v_k_372_: *mut leanh::LeanObject,
    mut v_motive_373_: *mut leanh::LeanObject,
    mut v_x_374_: *mut leanh::LeanObject,
    mut v_h__1_375_: *mut leanh::LeanObject,
    mut v_h__2_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_374_) == 0 {
        let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_376_);
        v___x_377_ = leanh::lean_box(0);
        v___x_378_ = leanh::lean_apply_1(v_h__1_375_, v___x_377_);
        return v___x_378_;
    } else {
        let mut v_val_379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_375_);
        v_val_379_ = leanh::lean_ctor_get(v_x_374_, 0);
        leanh::lean_inc(v_val_379_);
        leanh::lean_dec_ref_known(v_x_374_, 1);
        v___x_380_ = leanh::lean_apply_1(v_h__2_376_, v_val_379_);
        return v___x_380_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_381_: *mut leanh::LeanObject,
    mut v_00_u03b2_382_: *mut leanh::LeanObject,
    mut v_k_383_: *mut leanh::LeanObject,
    mut v_motive_384_: *mut leanh::LeanObject,
    mut v_x_385_: *mut leanh::LeanObject,
    mut v_h__1_386_: *mut leanh::LeanObject,
    mut v_h__2_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_381_, v_00_u03b2_382_, v_k_383_, v_motive_384_, v_x_385_, v_h__1_386_, v_h__2_387_);
    leanh::lean_dec(v_k_383_);
    return v_res_388_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(
    mut v_x_389_: *mut leanh::LeanObject,
    mut v_h__1_390_: *mut leanh::LeanObject,
    mut v_h__2_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_389_) == 0 {
        let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_391_);
        v___x_392_ = leanh::lean_box(0);
        v___x_393_ = leanh::lean_apply_1(v_h__1_390_, v___x_392_);
        return v___x_393_;
    } else {
        let mut v_val_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_390_);
        v_val_394_ = leanh::lean_ctor_get(v_x_389_, 0);
        leanh::lean_inc(v_val_394_);
        leanh::lean_dec_ref_known(v_x_389_, 1);
        v___x_395_ = leanh::lean_apply_1(v_h__2_391_, v_val_394_);
        return v___x_395_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(
    mut v_00_u03b2_396_: *mut leanh::LeanObject,
    mut v_motive_397_: *mut leanh::LeanObject,
    mut v_x_398_: *mut leanh::LeanObject,
    mut v_h__1_399_: *mut leanh::LeanObject,
    mut v_h__2_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_398_) == 0 {
        let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_400_);
        v___x_401_ = leanh::lean_box(0);
        v___x_402_ = leanh::lean_apply_1(v_h__1_399_, v___x_401_);
        return v___x_402_;
    } else {
        let mut v_val_403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_399_);
        v_val_403_ = leanh::lean_ctor_get(v_x_398_, 0);
        leanh::lean_inc(v_val_403_);
        leanh::lean_dec_ref_known(v_x_398_, 1);
        v___x_404_ = leanh::lean_apply_1(v_h__2_400_, v_val_403_);
        return v___x_404_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Associative(builtin);
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
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
}