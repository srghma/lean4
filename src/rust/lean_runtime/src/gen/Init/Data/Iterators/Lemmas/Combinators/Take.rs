// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Take
// Imports: Init.Data.Iterators.Combinators.Take Init.Data.Iterators.Lemmas.Combinators.Monadic.Take Init.Data.Iterators.Consumers.Access Init.Data.Iterators.Consumers.Collect Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Access Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.List.Nat.TakeDrop
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Take::{
    initialize_Init_Data_Iterators_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Access::{
    initialize_Init_Data_Iterators_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::Take::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Access::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg(
    mut v_n_213_: *mut LeanObject,
    mut v_h__1_214_: *mut LeanObject,
    mut v_h__2_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_217_: u8 = 0;
    v_zero_216_ = lean_unsigned_to_nat(0);
    v_isZero_217_ = lean_nat_dec_eq(v_n_213_, v_zero_216_);
    if v_isZero_217_ == 1 {
        let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_215_);
        v___x_218_ = lean_box(0);
        v___x_219_ = lean_apply_1(v_h__1_214_, v___x_218_);
        return v___x_219_;
    } else {
        let mut v_one_220_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_214_);
        v_one_220_ = lean_unsigned_to_nat(1);
        v_n_221_ = lean_nat_sub(v_n_213_, v_one_220_);
        v___x_222_ = lean_apply_1(v_h__2_215_, v_n_221_);
        return v___x_222_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(
    mut v_n_223_: *mut LeanObject,
    mut v_h__1_224_: *mut LeanObject,
    mut v_h__2_225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_226_: *mut LeanObject = core::ptr::null_mut();
    v_res_226_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_223_, v_h__1_224_, v_h__2_225_);
    lean_dec(v_n_223_);
    return v_res_226_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter(
    mut v_motive_227_: *mut LeanObject,
    mut v_n_228_: *mut LeanObject,
    mut v_h__1_229_: *mut LeanObject,
    mut v_h__2_230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_232_: u8 = 0;
    v_zero_231_ = lean_unsigned_to_nat(0);
    v_isZero_232_ = lean_nat_dec_eq(v_n_228_, v_zero_231_);
    if v_isZero_232_ == 1 {
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_230_);
        v___x_233_ = lean_box(0);
        v___x_234_ = lean_apply_1(v_h__1_229_, v___x_233_);
        return v___x_234_;
    } else {
        let mut v_one_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_229_);
        v_one_235_ = lean_unsigned_to_nat(1);
        v_n_236_ = lean_nat_sub(v_n_228_, v_one_235_);
        v___x_237_ = lean_apply_1(v_h__2_230_, v_n_236_);
        return v___x_237_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___boxed(
    mut v_motive_238_: *mut LeanObject,
    mut v_n_239_: *mut LeanObject,
    mut v_h__1_240_: *mut LeanObject,
    mut v_h__2_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_238_, v_n_239_, v_h__1_240_, v_h__2_241_);
    lean_dec(v_n_239_);
    return v_res_242_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___redArg(
    mut v_x_243_: *mut LeanObject,
    mut v_h__1_244_: *mut LeanObject,
    mut v_h__2_245_: *mut LeanObject,
    mut v_h__3_246_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_243_) {
        0 => {
            let mut v_it_247_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_246_);
            lean_dec(v_h__2_245_);
            v_it_247_ = lean_ctor_get(v_x_243_, 0);
            lean_inc(v_it_247_);
            v_out_248_ = lean_ctor_get(v_x_243_, 1);
            lean_inc(v_out_248_);
            lean_dec_ref_known(v_x_243_, 2);
            v___x_249_ = lean_apply_3(v_h__1_244_, v_it_247_, v_out_248_, lean_box(0));
            return v___x_249_;
        }
        1 => {
            let mut v_it_250_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_246_);
            lean_dec(v_h__1_244_);
            v_it_250_ = lean_ctor_get(v_x_243_, 0);
            lean_inc(v_it_250_);
            lean_dec_ref_known(v_x_243_, 1);
            v___x_251_ = lean_apply_2(v_h__2_245_, v_it_250_, lean_box(0));
            return v___x_251_;
        }
        _ => {
            let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_245_);
            lean_dec(v_h__1_244_);
            v___x_252_ = lean_apply_1(v_h__3_246_, lean_box(0));
            return v___x_252_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(
    mut v_00_u03b1_253_: *mut LeanObject,
    mut v_m_254_: *mut LeanObject,
    mut v_00_u03b2_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
    mut v_it_257_: *mut LeanObject,
    mut v_motive_258_: *mut LeanObject,
    mut v_x_259_: *mut LeanObject,
    mut v_h__1_260_: *mut LeanObject,
    mut v_h__2_261_: *mut LeanObject,
    mut v_h__3_262_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_259_) {
        0 => {
            let mut v_it_263_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_264_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_262_);
            lean_dec(v_h__2_261_);
            v_it_263_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_it_263_);
            v_out_264_ = lean_ctor_get(v_x_259_, 1);
            lean_inc(v_out_264_);
            lean_dec_ref_known(v_x_259_, 2);
            v___x_265_ = lean_apply_3(v_h__1_260_, v_it_263_, v_out_264_, lean_box(0));
            return v___x_265_;
        }
        1 => {
            let mut v_it_266_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_262_);
            lean_dec(v_h__1_260_);
            v_it_266_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_it_266_);
            lean_dec_ref_known(v_x_259_, 1);
            v___x_267_ = lean_apply_2(v_h__2_261_, v_it_266_, lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_261_);
            lean_dec(v_h__1_260_);
            v___x_268_ = lean_apply_1(v_h__3_262_, lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___boxed(
    mut v_00_u03b1_269_: *mut LeanObject,
    mut v_m_270_: *mut LeanObject,
    mut v_00_u03b2_271_: *mut LeanObject,
    mut v_inst_272_: *mut LeanObject,
    mut v_it_273_: *mut LeanObject,
    mut v_motive_274_: *mut LeanObject,
    mut v_x_275_: *mut LeanObject,
    mut v_h__1_276_: *mut LeanObject,
    mut v_h__2_277_: *mut LeanObject,
    mut v_h__3_278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_279_: *mut LeanObject = core::ptr::null_mut();
    v_res_279_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_269_, v_m_270_, v_00_u03b2_271_, v_inst_272_, v_it_273_, v_motive_274_, v_x_275_, v_h__1_276_, v_h__2_277_, v_h__3_278_);
    lean_dec(v_it_273_);
    lean_dec(v_inst_272_);
    return v_res_279_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(
    mut v_n_280_: *mut LeanObject,
    mut v_h__1_281_: *mut LeanObject,
    mut v_h__2_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_284_: u8 = 0;
    v_zero_283_ = lean_unsigned_to_nat(0);
    v_isZero_284_ = lean_nat_dec_eq(v_n_280_, v_zero_283_);
    if v_isZero_284_ == 1 {
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_282_);
        v___x_285_ = lean_box(0);
        v___x_286_ = lean_apply_1(v_h__1_281_, v___x_285_);
        return v___x_286_;
    } else {
        let mut v_one_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_281_);
        v_one_287_ = lean_unsigned_to_nat(1);
        v_n_288_ = lean_nat_sub(v_n_280_, v_one_287_);
        v___x_289_ = lean_apply_1(v_h__2_282_, v_n_288_);
        return v___x_289_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg___boxed(
    mut v_n_290_: *mut LeanObject,
    mut v_h__1_291_: *mut LeanObject,
    mut v_h__2_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_293_: *mut LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(v_n_290_, v_h__1_291_, v_h__2_292_);
    lean_dec(v_n_290_);
    return v_res_293_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(
    mut v_motive_294_: *mut LeanObject,
    mut v_n_295_: *mut LeanObject,
    mut v_h__1_296_: *mut LeanObject,
    mut v_h__2_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_299_: u8 = 0;
    v_zero_298_ = lean_unsigned_to_nat(0);
    v_isZero_299_ = lean_nat_dec_eq(v_n_295_, v_zero_298_);
    if v_isZero_299_ == 1 {
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_297_);
        v___x_300_ = lean_box(0);
        v___x_301_ = lean_apply_1(v_h__1_296_, v___x_300_);
        return v___x_301_;
    } else {
        let mut v_one_302_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_296_);
        v_one_302_ = lean_unsigned_to_nat(1);
        v_n_303_ = lean_nat_sub(v_n_295_, v_one_302_);
        v___x_304_ = lean_apply_1(v_h__2_297_, v_n_303_);
        return v___x_304_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___boxed(
    mut v_motive_305_: *mut LeanObject,
    mut v_n_306_: *mut LeanObject,
    mut v_h__1_307_: *mut LeanObject,
    mut v_h__2_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_309_: *mut LeanObject = core::ptr::null_mut();
    v_res_309_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(v_motive_305_, v_n_306_, v_h__1_307_, v_h__2_308_);
    lean_dec(v_n_306_);
    return v_res_309_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___redArg(
    mut v_x_310_: *mut LeanObject,
    mut v_h__1_311_: *mut LeanObject,
    mut v_h__2_312_: *mut LeanObject,
    mut v_h__3_313_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_310_) {
        0 => {
            let mut v_it_314_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_313_);
            lean_dec(v_h__2_312_);
            v_it_314_ = lean_ctor_get(v_x_310_, 0);
            lean_inc(v_it_314_);
            v_out_315_ = lean_ctor_get(v_x_310_, 1);
            lean_inc(v_out_315_);
            lean_dec_ref_known(v_x_310_, 2);
            v___x_316_ = lean_apply_3(v_h__1_311_, v_it_314_, v_out_315_, lean_box(0));
            return v___x_316_;
        }
        1 => {
            let mut v_it_317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_313_);
            lean_dec(v_h__1_311_);
            v_it_317_ = lean_ctor_get(v_x_310_, 0);
            lean_inc(v_it_317_);
            lean_dec_ref_known(v_x_310_, 1);
            v___x_318_ = lean_apply_2(v_h__2_312_, v_it_317_, lean_box(0));
            return v___x_318_;
        }
        _ => {
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_312_);
            lean_dec(v_h__1_311_);
            v___x_319_ = lean_apply_1(v_h__3_313_, lean_box(0));
            return v___x_319_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_00_u03b2_321_: *mut LeanObject,
    mut v_inst_322_: *mut LeanObject,
    mut v_it_323_: *mut LeanObject,
    mut v_motive_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
    mut v_h__1_326_: *mut LeanObject,
    mut v_h__2_327_: *mut LeanObject,
    mut v_h__3_328_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_325_) {
        0 => {
            let mut v_it_329_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_330_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_328_);
            lean_dec(v_h__2_327_);
            v_it_329_ = lean_ctor_get(v_x_325_, 0);
            lean_inc(v_it_329_);
            v_out_330_ = lean_ctor_get(v_x_325_, 1);
            lean_inc(v_out_330_);
            lean_dec_ref_known(v_x_325_, 2);
            v___x_331_ = lean_apply_3(v_h__1_326_, v_it_329_, v_out_330_, lean_box(0));
            return v___x_331_;
        }
        1 => {
            let mut v_it_332_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_328_);
            lean_dec(v_h__1_326_);
            v_it_332_ = lean_ctor_get(v_x_325_, 0);
            lean_inc(v_it_332_);
            lean_dec_ref_known(v_x_325_, 1);
            v___x_333_ = lean_apply_2(v_h__2_327_, v_it_332_, lean_box(0));
            return v___x_333_;
        }
        _ => {
            let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_327_);
            lean_dec(v_h__1_326_);
            v___x_334_ = lean_apply_1(v_h__3_328_, lean_box(0));
            return v___x_334_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___boxed(
    mut v_00_u03b1_335_: *mut LeanObject,
    mut v_00_u03b2_336_: *mut LeanObject,
    mut v_inst_337_: *mut LeanObject,
    mut v_it_338_: *mut LeanObject,
    mut v_motive_339_: *mut LeanObject,
    mut v_x_340_: *mut LeanObject,
    mut v_h__1_341_: *mut LeanObject,
    mut v_h__2_342_: *mut LeanObject,
    mut v_h__3_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_344_: *mut LeanObject = core::ptr::null_mut();
    v_res_344_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(v_00_u03b1_335_, v_00_u03b2_336_, v_inst_337_, v_it_338_, v_motive_339_, v_x_340_, v_h__1_341_, v_h__2_342_, v_h__3_343_);
    lean_dec(v_it_338_);
    lean_dec(v_inst_337_);
    return v_res_344_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(
    mut v_x_345_: *mut LeanObject,
    mut v_h__1_346_: *mut LeanObject,
    mut v_h__2_347_: *mut LeanObject,
    mut v_h__3_348_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_345_) {
        0 => {
            let mut v_it_349_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_348_);
            lean_dec(v_h__2_347_);
            v_it_349_ = lean_ctor_get(v_x_345_, 0);
            lean_inc(v_it_349_);
            v_out_350_ = lean_ctor_get(v_x_345_, 1);
            lean_inc(v_out_350_);
            lean_dec_ref_known(v_x_345_, 2);
            v___x_351_ = lean_apply_2(v_h__1_346_, v_it_349_, v_out_350_);
            return v___x_351_;
        }
        1 => {
            let mut v_it_352_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_348_);
            lean_dec(v_h__1_346_);
            v_it_352_ = lean_ctor_get(v_x_345_, 0);
            lean_inc(v_it_352_);
            lean_dec_ref_known(v_x_345_, 1);
            v___x_353_ = lean_apply_1(v_h__2_347_, v_it_352_);
            return v___x_353_;
        }
        _ => {
            let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_347_);
            lean_dec(v_h__1_346_);
            v___x_354_ = lean_box(0);
            v___x_355_ = lean_apply_1(v_h__3_348_, v___x_354_);
            return v___x_355_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(
    mut v_00_u03b1_356_: *mut LeanObject,
    mut v_00_u03b2_357_: *mut LeanObject,
    mut v_motive_358_: *mut LeanObject,
    mut v_x_359_: *mut LeanObject,
    mut v_h__1_360_: *mut LeanObject,
    mut v_h__2_361_: *mut LeanObject,
    mut v_h__3_362_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_359_) {
        0 => {
            let mut v_it_363_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_364_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_362_);
            lean_dec(v_h__2_361_);
            v_it_363_ = lean_ctor_get(v_x_359_, 0);
            lean_inc(v_it_363_);
            v_out_364_ = lean_ctor_get(v_x_359_, 1);
            lean_inc(v_out_364_);
            lean_dec_ref_known(v_x_359_, 2);
            v___x_365_ = lean_apply_2(v_h__1_360_, v_it_363_, v_out_364_);
            return v___x_365_;
        }
        1 => {
            let mut v_it_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_362_);
            lean_dec(v_h__1_360_);
            v_it_366_ = lean_ctor_get(v_x_359_, 0);
            lean_inc(v_it_366_);
            lean_dec_ref_known(v_x_359_, 1);
            v___x_367_ = lean_apply_1(v_h__2_361_, v_it_366_);
            return v___x_367_;
        }
        _ => {
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_361_);
            lean_dec(v_h__1_360_);
            v___x_368_ = lean_box(0);
            v___x_369_ = lean_apply_1(v_h__3_362_, v___x_368_);
            return v___x_369_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_370_: *mut LeanObject,
    mut v_h__1_371_: *mut LeanObject,
    mut v_h__2_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_374_: u8 = 0;
    v_zero_373_ = lean_unsigned_to_nat(0);
    v_isZero_374_ = lean_nat_dec_eq(v_n_370_, v_zero_373_);
    if v_isZero_374_ == 1 {
        let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_372_);
        v___x_375_ = lean_box(0);
        v___x_376_ = lean_apply_1(v_h__1_371_, v___x_375_);
        return v___x_376_;
    } else {
        let mut v_one_377_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_371_);
        v_one_377_ = lean_unsigned_to_nat(1);
        v_n_378_ = lean_nat_sub(v_n_370_, v_one_377_);
        v___x_379_ = lean_apply_1(v_h__2_372_, v_n_378_);
        return v___x_379_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_380_: *mut LeanObject,
    mut v_h__1_381_: *mut LeanObject,
    mut v_h__2_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_383_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_380_, v_h__1_381_, v_h__2_382_);
    lean_dec(v_n_380_);
    return v_res_383_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_384_: *mut LeanObject,
    mut v_n_385_: *mut LeanObject,
    mut v_h__1_386_: *mut LeanObject,
    mut v_h__2_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_389_: u8 = 0;
    v_zero_388_ = lean_unsigned_to_nat(0);
    v_isZero_389_ = lean_nat_dec_eq(v_n_385_, v_zero_388_);
    if v_isZero_389_ == 1 {
        let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_387_);
        v___x_390_ = lean_box(0);
        v___x_391_ = lean_apply_1(v_h__1_386_, v___x_390_);
        return v___x_391_;
    } else {
        let mut v_one_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_386_);
        v_one_392_ = lean_unsigned_to_nat(1);
        v_n_393_ = lean_nat_sub(v_n_385_, v_one_392_);
        v___x_394_ = lean_apply_1(v_h__2_387_, v_n_393_);
        return v___x_394_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_395_: *mut LeanObject,
    mut v_n_396_: *mut LeanObject,
    mut v_h__1_397_: *mut LeanObject,
    mut v_h__2_398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_399_: *mut LeanObject = core::ptr::null_mut();
    v_res_399_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_395_, v_n_396_, v_h__1_397_, v_h__2_398_);
    lean_dec(v_n_396_);
    return v_res_399_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_400_: *mut LeanObject,
    mut v_h__1_401_: *mut LeanObject,
    mut v_h__2_402_: *mut LeanObject,
    mut v_h__3_403_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_400_) {
        0 => {
            let mut v_it_404_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_405_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_403_);
            lean_dec(v_h__2_402_);
            v_it_404_ = lean_ctor_get(v_x_400_, 0);
            lean_inc(v_it_404_);
            v_out_405_ = lean_ctor_get(v_x_400_, 1);
            lean_inc(v_out_405_);
            lean_dec_ref_known(v_x_400_, 2);
            v___x_406_ = lean_apply_2(v_h__1_401_, v_it_404_, v_out_405_);
            return v___x_406_;
        }
        1 => {
            let mut v_it_407_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_403_);
            lean_dec(v_h__1_401_);
            v_it_407_ = lean_ctor_get(v_x_400_, 0);
            lean_inc(v_it_407_);
            lean_dec_ref_known(v_x_400_, 1);
            v___x_408_ = lean_apply_1(v_h__2_402_, v_it_407_);
            return v___x_408_;
        }
        _ => {
            let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_402_);
            lean_dec(v_h__1_401_);
            v___x_409_ = lean_box(0);
            v___x_410_ = lean_apply_1(v_h__3_403_, v___x_409_);
            return v___x_410_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_411_: *mut LeanObject,
    mut v_00_u03b2_412_: *mut LeanObject,
    mut v_motive_413_: *mut LeanObject,
    mut v_x_414_: *mut LeanObject,
    mut v_h__1_415_: *mut LeanObject,
    mut v_h__2_416_: *mut LeanObject,
    mut v_h__3_417_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_414_) {
        0 => {
            let mut v_it_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_417_);
            lean_dec(v_h__2_416_);
            v_it_418_ = lean_ctor_get(v_x_414_, 0);
            lean_inc(v_it_418_);
            v_out_419_ = lean_ctor_get(v_x_414_, 1);
            lean_inc(v_out_419_);
            lean_dec_ref_known(v_x_414_, 2);
            v___x_420_ = lean_apply_2(v_h__1_415_, v_it_418_, v_out_419_);
            return v___x_420_;
        }
        1 => {
            let mut v_it_421_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_417_);
            lean_dec(v_h__1_415_);
            v_it_421_ = lean_ctor_get(v_x_414_, 0);
            lean_inc(v_it_421_);
            lean_dec_ref_known(v_x_414_, 1);
            v___x_422_ = lean_apply_1(v_h__2_416_, v_it_421_);
            return v___x_422_;
        }
        _ => {
            let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_416_);
            lean_dec(v_h__1_415_);
            v___x_423_ = lean_box(0);
            v___x_424_ = lean_apply_1(v_h__3_417_, v___x_423_);
            return v___x_424_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
}
