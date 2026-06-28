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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_3, lean_apply_4, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(
    mut v_x_203_: *mut LeanObject,
    mut v_x_204_: *mut LeanObject,
    mut v_h__1_205_: *mut LeanObject,
    mut v_h__2_206_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_204_) == 0 {
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_206_);
        v___x_207_ = lean_apply_1(v_h__1_205_, v_x_203_);
        return v___x_207_;
    } else {
        let mut v_key_208_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_209_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_205_);
        v_key_208_ = lean_ctor_get(v_x_204_, 0);
        lean_inc(v_key_208_);
        v_value_209_ = lean_ctor_get(v_x_204_, 1);
        lean_inc(v_value_209_);
        v_tail_210_ = lean_ctor_get(v_x_204_, 2);
        lean_inc(v_tail_210_);
        lean_dec_ref_known(v_x_204_, 3);
        v___x_211_ = lean_apply_4(v_h__2_206_, v_x_203_, v_key_208_, v_value_209_, v_tail_210_);
        return v___x_211_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(
    mut v_00_u03b1_212_: *mut LeanObject,
    mut v_00_u03b2_213_: *mut LeanObject,
    mut v_00_u03b4_214_: *mut LeanObject,
    mut v_motive_215_: *mut LeanObject,
    mut v_x_216_: *mut LeanObject,
    mut v_x_217_: *mut LeanObject,
    mut v_h__1_218_: *mut LeanObject,
    mut v_h__2_219_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_219_);
        v___x_220_ = lean_apply_1(v_h__1_218_, v_x_216_);
        return v___x_220_;
    } else {
        let mut v_key_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_218_);
        v_key_221_ = lean_ctor_get(v_x_217_, 0);
        lean_inc(v_key_221_);
        v_value_222_ = lean_ctor_get(v_x_217_, 1);
        lean_inc(v_value_222_);
        v_tail_223_ = lean_ctor_get(v_x_217_, 2);
        lean_inc(v_tail_223_);
        lean_dec_ref_known(v_x_217_, 3);
        v___x_224_ = lean_apply_4(v_h__2_219_, v_x_216_, v_key_221_, v_value_222_, v_tail_223_);
        return v___x_224_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter___redArg(
    mut v_x_225_: *mut LeanObject,
    mut v_h__1_226_: *mut LeanObject,
    mut v_h__2_227_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_225_) == 0 {
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_227_);
        v___x_228_ = lean_box(0);
        v___x_229_ = lean_apply_1(v_h__1_226_, v___x_228_);
        return v___x_229_;
    } else {
        let mut v_key_230_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_226_);
        v_key_230_ = lean_ctor_get(v_x_225_, 0);
        lean_inc(v_key_230_);
        v_value_231_ = lean_ctor_get(v_x_225_, 1);
        lean_inc(v_value_231_);
        v_tail_232_ = lean_ctor_get(v_x_225_, 2);
        lean_inc(v_tail_232_);
        lean_dec_ref_known(v_x_225_, 3);
        v___x_233_ = lean_apply_3(v_h__2_227_, v_key_230_, v_value_231_, v_tail_232_);
        return v___x_233_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter(
    mut v_00_u03b1_234_: *mut LeanObject,
    mut v_00_u03b2_235_: *mut LeanObject,
    mut v_motive_236_: *mut LeanObject,
    mut v_x_237_: *mut LeanObject,
    mut v_h__1_238_: *mut LeanObject,
    mut v_h__2_239_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_237_) == 0 {
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_239_);
        v___x_240_ = lean_box(0);
        v___x_241_ = lean_apply_1(v_h__1_238_, v___x_240_);
        return v___x_241_;
    } else {
        let mut v_key_242_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_243_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_238_);
        v_key_242_ = lean_ctor_get(v_x_237_, 0);
        lean_inc(v_key_242_);
        v_value_243_ = lean_ctor_get(v_x_237_, 1);
        lean_inc(v_value_243_);
        v_tail_244_ = lean_ctor_get(v_x_237_, 2);
        lean_inc(v_tail_244_);
        lean_dec_ref_known(v_x_237_, 3);
        v___x_245_ = lean_apply_3(v_h__2_239_, v_key_242_, v_value_243_, v_tail_244_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(
    mut v_x_246_: *mut LeanObject,
    mut v_h__1_247_: *mut LeanObject,
    mut v_h__2_248_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_246_) == 0 {
        let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_248_);
        v___x_249_ = lean_box(0);
        v___x_250_ = lean_apply_1(v_h__1_247_, v___x_249_);
        return v___x_250_;
    } else {
        let mut v_key_251_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_252_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_247_);
        v_key_251_ = lean_ctor_get(v_x_246_, 0);
        lean_inc(v_key_251_);
        v_value_252_ = lean_ctor_get(v_x_246_, 1);
        lean_inc(v_value_252_);
        v_tail_253_ = lean_ctor_get(v_x_246_, 2);
        lean_inc(v_tail_253_);
        lean_dec_ref_known(v_x_246_, 3);
        v___x_254_ = lean_apply_3(v_h__2_248_, v_key_251_, v_value_252_, v_tail_253_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(
    mut v_00_u03b1_255_: *mut LeanObject,
    mut v_00_u03b2_256_: *mut LeanObject,
    mut v_motive_257_: *mut LeanObject,
    mut v_x_258_: *mut LeanObject,
    mut v_h__1_259_: *mut LeanObject,
    mut v_h__2_260_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_258_) == 0 {
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_260_);
        v___x_261_ = lean_box(0);
        v___x_262_ = lean_apply_1(v_h__1_259_, v___x_261_);
        return v___x_262_;
    } else {
        let mut v_key_263_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_264_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_259_);
        v_key_263_ = lean_ctor_get(v_x_258_, 0);
        lean_inc(v_key_263_);
        v_value_264_ = lean_ctor_get(v_x_258_, 1);
        lean_inc(v_value_264_);
        v_tail_265_ = lean_ctor_get(v_x_258_, 2);
        lean_inc(v_tail_265_);
        lean_dec_ref_known(v_x_258_, 3);
        v___x_266_ = lean_apply_3(v_h__2_260_, v_key_263_, v_value_264_, v_tail_265_);
        return v___x_266_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(
    mut v_x_267_: *mut LeanObject,
    mut v_h__1_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v_key_269_ = lean_ctor_get(v_x_267_, 0);
    lean_inc(v_key_269_);
    v_value_270_ = lean_ctor_get(v_x_267_, 1);
    lean_inc(v_value_270_);
    v_tail_271_ = lean_ctor_get(v_x_267_, 2);
    lean_inc(v_tail_271_);
    lean_dec(v_x_267_);
    v___x_272_ = lean_apply_4(
        v_h__1_268_,
        v_key_269_,
        v_value_270_,
        v_tail_271_,
        lean_box(0),
    );
    return v___x_272_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(
    mut v_00_u03b1_273_: *mut LeanObject,
    mut v_00_u03b2_274_: *mut LeanObject,
    mut v_inst_275_: *mut LeanObject,
    mut v_a_276_: *mut LeanObject,
    mut v_motive_277_: *mut LeanObject,
    mut v_x_278_: *mut LeanObject,
    mut v_x_279_: *mut LeanObject,
    mut v_h__1_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    v_key_281_ = lean_ctor_get(v_x_278_, 0);
    lean_inc(v_key_281_);
    v_value_282_ = lean_ctor_get(v_x_278_, 1);
    lean_inc(v_value_282_);
    v_tail_283_ = lean_ctor_get(v_x_278_, 2);
    lean_inc(v_tail_283_);
    lean_dec(v_x_278_);
    v___x_284_ = lean_apply_4(
        v_h__1_280_,
        v_key_281_,
        v_value_282_,
        v_tail_283_,
        lean_box(0),
    );
    return v___x_284_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(
    mut v_00_u03b1_285_: *mut LeanObject,
    mut v_00_u03b2_286_: *mut LeanObject,
    mut v_inst_287_: *mut LeanObject,
    mut v_a_288_: *mut LeanObject,
    mut v_motive_289_: *mut LeanObject,
    mut v_x_290_: *mut LeanObject,
    mut v_x_291_: *mut LeanObject,
    mut v_h__1_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_293_: *mut LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(v_00_u03b1_285_, v_00_u03b2_286_, v_inst_287_, v_a_288_, v_motive_289_, v_x_290_, v_x_291_, v_h__1_292_);
    lean_dec(v_a_288_);
    lean_dec_ref(v_inst_287_);
    return v_res_293_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(
    mut v_x_294_: *mut LeanObject,
    mut v_h__1_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    v_key_296_ = lean_ctor_get(v_x_294_, 0);
    lean_inc(v_key_296_);
    v_value_297_ = lean_ctor_get(v_x_294_, 1);
    lean_inc(v_value_297_);
    v_tail_298_ = lean_ctor_get(v_x_294_, 2);
    lean_inc(v_tail_298_);
    lean_dec(v_x_294_);
    v___x_299_ = lean_apply_4(
        v_h__1_295_,
        v_key_296_,
        v_value_297_,
        v_tail_298_,
        lean_box(0),
    );
    return v___x_299_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(
    mut v_00_u03b1_300_: *mut LeanObject,
    mut v_00_u03b2_301_: *mut LeanObject,
    mut v_inst_302_: *mut LeanObject,
    mut v_a_303_: *mut LeanObject,
    mut v_motive_304_: *mut LeanObject,
    mut v_x_305_: *mut LeanObject,
    mut v_x_306_: *mut LeanObject,
    mut v_h__1_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    v_key_308_ = lean_ctor_get(v_x_305_, 0);
    lean_inc(v_key_308_);
    v_value_309_ = lean_ctor_get(v_x_305_, 1);
    lean_inc(v_value_309_);
    v_tail_310_ = lean_ctor_get(v_x_305_, 2);
    lean_inc(v_tail_310_);
    lean_dec(v_x_305_);
    v___x_311_ = lean_apply_4(
        v_h__1_307_,
        v_key_308_,
        v_value_309_,
        v_tail_310_,
        lean_box(0),
    );
    return v___x_311_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(
    mut v_00_u03b1_312_: *mut LeanObject,
    mut v_00_u03b2_313_: *mut LeanObject,
    mut v_inst_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
    mut v_motive_316_: *mut LeanObject,
    mut v_x_317_: *mut LeanObject,
    mut v_x_318_: *mut LeanObject,
    mut v_h__1_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_320_: *mut LeanObject = core::ptr::null_mut();
    v_res_320_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(v_00_u03b1_312_, v_00_u03b2_313_, v_inst_314_, v_a_315_, v_motive_316_, v_x_317_, v_x_318_, v_h__1_319_);
    lean_dec(v_a_315_);
    lean_dec_ref(v_inst_314_);
    return v_res_320_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(
    mut v_x_321_: *mut LeanObject,
    mut v_h__1_322_: *mut LeanObject,
    mut v_h__2_323_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_321_) == 0 {
        let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_323_);
        v___x_324_ = lean_box(0);
        v___x_325_ = lean_apply_1(v_h__1_322_, v___x_324_);
        return v___x_325_;
    } else {
        let mut v_val_326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_322_);
        v_val_326_ = lean_ctor_get(v_x_321_, 0);
        lean_inc(v_val_326_);
        lean_dec_ref_known(v_x_321_, 1);
        v___x_327_ = lean_apply_1(v_h__2_323_, v_val_326_);
        return v___x_327_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(
    mut v_00_u03b1_328_: *mut LeanObject,
    mut v_00_u03b2_329_: *mut LeanObject,
    mut v_a_330_: *mut LeanObject,
    mut v_motive_331_: *mut LeanObject,
    mut v_x_332_: *mut LeanObject,
    mut v_h__1_333_: *mut LeanObject,
    mut v_h__2_334_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_332_) == 0 {
        let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_334_);
        v___x_335_ = lean_box(0);
        v___x_336_ = lean_apply_1(v_h__1_333_, v___x_335_);
        return v___x_336_;
    } else {
        let mut v_val_337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_333_);
        v_val_337_ = lean_ctor_get(v_x_332_, 0);
        lean_inc(v_val_337_);
        lean_dec_ref_known(v_x_332_, 1);
        v___x_338_ = lean_apply_1(v_h__2_334_, v_val_337_);
        return v___x_338_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(
    mut v_00_u03b1_339_: *mut LeanObject,
    mut v_00_u03b2_340_: *mut LeanObject,
    mut v_a_341_: *mut LeanObject,
    mut v_motive_342_: *mut LeanObject,
    mut v_x_343_: *mut LeanObject,
    mut v_h__1_344_: *mut LeanObject,
    mut v_h__2_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(v_00_u03b1_339_, v_00_u03b2_340_, v_a_341_, v_motive_342_, v_x_343_, v_h__1_344_, v_h__2_345_);
    lean_dec(v_a_341_);
    return v_res_346_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_347_: *mut LeanObject,
    mut v_h__1_348_: *mut LeanObject,
    mut v_h__2_349_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_347_) == 0 {
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_349_);
        v___x_350_ = lean_box(0);
        v___x_351_ = lean_apply_1(v_h__1_348_, v___x_350_);
        return v___x_351_;
    } else {
        let mut v_val_352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_348_);
        v_val_352_ = lean_ctor_get(v_x_347_, 0);
        lean_inc(v_val_352_);
        lean_dec_ref_known(v_x_347_, 1);
        v___x_353_ = lean_apply_1(v_h__2_349_, v_val_352_);
        return v___x_353_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_354_: *mut LeanObject,
    mut v_motive_355_: *mut LeanObject,
    mut v_x_356_: *mut LeanObject,
    mut v_h__1_357_: *mut LeanObject,
    mut v_h__2_358_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_356_) == 0 {
        let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_358_);
        v___x_359_ = lean_box(0);
        v___x_360_ = lean_apply_1(v_h__1_357_, v___x_359_);
        return v___x_360_;
    } else {
        let mut v_val_361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_357_);
        v_val_361_ = lean_ctor_get(v_x_356_, 0);
        lean_inc(v_val_361_);
        lean_dec_ref_known(v_x_356_, 1);
        v___x_362_ = lean_apply_1(v_h__2_358_, v_val_361_);
        return v___x_362_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(
    mut v_x_363_: *mut LeanObject,
    mut v_h__1_364_: *mut LeanObject,
    mut v_h__2_365_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_363_) == 0 {
        let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_365_);
        v___x_366_ = lean_box(0);
        v___x_367_ = lean_apply_1(v_h__1_364_, v___x_366_);
        return v___x_367_;
    } else {
        let mut v_val_368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_364_);
        v_val_368_ = lean_ctor_get(v_x_363_, 0);
        lean_inc(v_val_368_);
        lean_dec_ref_known(v_x_363_, 1);
        v___x_369_ = lean_apply_1(v_h__2_365_, v_val_368_);
        return v___x_369_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(
    mut v_00_u03b1_370_: *mut LeanObject,
    mut v_00_u03b2_371_: *mut LeanObject,
    mut v_k_372_: *mut LeanObject,
    mut v_motive_373_: *mut LeanObject,
    mut v_x_374_: *mut LeanObject,
    mut v_h__1_375_: *mut LeanObject,
    mut v_h__2_376_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_374_) == 0 {
        let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_376_);
        v___x_377_ = lean_box(0);
        v___x_378_ = lean_apply_1(v_h__1_375_, v___x_377_);
        return v___x_378_;
    } else {
        let mut v_val_379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_375_);
        v_val_379_ = lean_ctor_get(v_x_374_, 0);
        lean_inc(v_val_379_);
        lean_dec_ref_known(v_x_374_, 1);
        v___x_380_ = lean_apply_1(v_h__2_376_, v_val_379_);
        return v___x_380_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(
    mut v_00_u03b1_381_: *mut LeanObject,
    mut v_00_u03b2_382_: *mut LeanObject,
    mut v_k_383_: *mut LeanObject,
    mut v_motive_384_: *mut LeanObject,
    mut v_x_385_: *mut LeanObject,
    mut v_h__1_386_: *mut LeanObject,
    mut v_h__2_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_388_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_381_, v_00_u03b2_382_, v_k_383_, v_motive_384_, v_x_385_, v_h__1_386_, v_h__2_387_);
    lean_dec(v_k_383_);
    return v_res_388_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(
    mut v_x_389_: *mut LeanObject,
    mut v_h__1_390_: *mut LeanObject,
    mut v_h__2_391_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_389_) == 0 {
        let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_391_);
        v___x_392_ = lean_box(0);
        v___x_393_ = lean_apply_1(v_h__1_390_, v___x_392_);
        return v___x_393_;
    } else {
        let mut v_val_394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_390_);
        v_val_394_ = lean_ctor_get(v_x_389_, 0);
        lean_inc(v_val_394_);
        lean_dec_ref_known(v_x_389_, 1);
        v___x_395_ = lean_apply_1(v_h__2_391_, v_val_394_);
        return v___x_395_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(
    mut v_00_u03b2_396_: *mut LeanObject,
    mut v_motive_397_: *mut LeanObject,
    mut v_x_398_: *mut LeanObject,
    mut v_h__1_399_: *mut LeanObject,
    mut v_h__2_400_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_398_) == 0 {
        let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_400_);
        v___x_401_ = lean_box(0);
        v___x_402_ = lean_apply_1(v_h__1_399_, v___x_401_);
        return v___x_402_;
    } else {
        let mut v_val_403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_399_);
        v_val_403_ = lean_ctor_get(v_x_398_, 0);
        lean_inc(v_val_403_);
        lean_dec_ref_known(v_x_398_, 1);
        v___x_404_ = lean_apply_1(v_h__2_400_, v_val_403_);
        return v___x_404_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
}
