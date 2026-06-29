// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.TakeWhile
// Imports: Std.Data.Iterators.Combinators.TakeWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile Std.Data.Iterators.Lemmas.Consumers Init.Data.List.TakeDrop Init.Data.List.ToArray Init.Data.Option.Lemmas Init.Omega
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::List::ToArray::{
    initialize_Init_Data_List_ToArray, runtime_initialize_Init_Data_List_ToArray,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Data::Iterators::Combinators::TakeWhile::{
    initialize_Std_Data_Iterators_Combinators_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::TakeWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::{
    initialize_Std_Data_Iterators_Lemmas_Consumers,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___redArg(
    mut v_x_223_: *mut crate::leanh::LeanObject,
    mut v_h__1_224_: *mut crate::leanh::LeanObject,
    mut v_h__2_225_: *mut crate::leanh::LeanObject,
    mut v_h__3_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_223_) {
        0 => {
            let mut v_it_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_226_);
            crate::leanh::lean_dec(v_h__2_225_);
            v_it_227_ = crate::leanh::lean_ctor_get(v_x_223_, 0);
            crate::leanh::lean_inc(v_it_227_);
            v_out_228_ = crate::leanh::lean_ctor_get(v_x_223_, 1);
            crate::leanh::lean_inc(v_out_228_);
            crate::leanh::lean_dec_ref_known(v_x_223_, 2);
            v___x_229_ = crate::leanh::lean_apply_3(
                v_h__1_224_,
                v_it_227_,
                v_out_228_,
                crate::leanh::lean_box(0),
            );
            return v___x_229_;
        }
        1 => {
            let mut v_it_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_226_);
            crate::leanh::lean_dec(v_h__1_224_);
            v_it_230_ = crate::leanh::lean_ctor_get(v_x_223_, 0);
            crate::leanh::lean_inc(v_it_230_);
            crate::leanh::lean_dec_ref_known(v_x_223_, 1);
            v___x_231_ =
                crate::leanh::lean_apply_2(v_h__2_225_, v_it_230_, crate::leanh::lean_box(0));
            return v___x_231_;
        }
        _ => {
            let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_225_);
            crate::leanh::lean_dec(v_h__1_224_);
            v___x_232_ = crate::leanh::lean_apply_1(v_h__3_226_, crate::leanh::lean_box(0));
            return v___x_232_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(
    mut v_00_u03b1_233_: *mut crate::leanh::LeanObject,
    mut v_m_234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_235_: *mut crate::leanh::LeanObject,
    mut v_inst_236_: *mut crate::leanh::LeanObject,
    mut v_it_237_: *mut crate::leanh::LeanObject,
    mut v_motive_238_: *mut crate::leanh::LeanObject,
    mut v_x_239_: *mut crate::leanh::LeanObject,
    mut v_h__1_240_: *mut crate::leanh::LeanObject,
    mut v_h__2_241_: *mut crate::leanh::LeanObject,
    mut v_h__3_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_239_) {
        0 => {
            let mut v_it_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_242_);
            crate::leanh::lean_dec(v_h__2_241_);
            v_it_243_ = crate::leanh::lean_ctor_get(v_x_239_, 0);
            crate::leanh::lean_inc(v_it_243_);
            v_out_244_ = crate::leanh::lean_ctor_get(v_x_239_, 1);
            crate::leanh::lean_inc(v_out_244_);
            crate::leanh::lean_dec_ref_known(v_x_239_, 2);
            v___x_245_ = crate::leanh::lean_apply_3(
                v_h__1_240_,
                v_it_243_,
                v_out_244_,
                crate::leanh::lean_box(0),
            );
            return v___x_245_;
        }
        1 => {
            let mut v_it_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_242_);
            crate::leanh::lean_dec(v_h__1_240_);
            v_it_246_ = crate::leanh::lean_ctor_get(v_x_239_, 0);
            crate::leanh::lean_inc(v_it_246_);
            crate::leanh::lean_dec_ref_known(v_x_239_, 1);
            v___x_247_ =
                crate::leanh::lean_apply_2(v_h__2_241_, v_it_246_, crate::leanh::lean_box(0));
            return v___x_247_;
        }
        _ => {
            let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_241_);
            crate::leanh::lean_dec(v_h__1_240_);
            v___x_248_ = crate::leanh::lean_apply_1(v_h__3_242_, crate::leanh::lean_box(0));
            return v___x_248_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_249_: *mut crate::leanh::LeanObject,
    mut v_m_250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
    mut v_it_253_: *mut crate::leanh::LeanObject,
    mut v_motive_254_: *mut crate::leanh::LeanObject,
    mut v_x_255_: *mut crate::leanh::LeanObject,
    mut v_h__1_256_: *mut crate::leanh::LeanObject,
    mut v_h__2_257_: *mut crate::leanh::LeanObject,
    mut v_h__3_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_259_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(v_00_u03b1_249_, v_m_250_, v_00_u03b2_251_, v_inst_252_, v_it_253_, v_motive_254_, v_x_255_, v_h__1_256_, v_h__2_257_, v_h__3_258_);
    crate::leanh::lean_dec(v_it_253_);
    crate::leanh::lean_dec(v_inst_252_);
    return v_res_259_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(
    mut v_x_260_: u8,
    mut v_h__1_261_: *mut crate::leanh::LeanObject,
    mut v_h__2_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_260_ == 0 {
        let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_261_);
        v___x_263_ = crate::leanh::lean_apply_1(v_h__2_262_, crate::leanh::lean_box(0));
        return v___x_263_;
    } else {
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_262_);
        v___x_264_ = crate::leanh::lean_apply_1(v_h__1_261_, crate::leanh::lean_box(0));
        return v___x_264_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_265_: *mut crate::leanh::LeanObject,
    mut v_h__1_266_: *mut crate::leanh::LeanObject,
    mut v_h__2_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_268_: u8 = 0;
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_268_ = (crate::leanh::lean_unbox(v_x_265_) as u8);
    v_res_269_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_268_, v_h__1_266_, v_h__2_267_);
    return v_res_269_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(
    mut v_motive_270_: *mut crate::leanh::LeanObject,
    mut v_x_271_: u8,
    mut v_h__1_272_: *mut crate::leanh::LeanObject,
    mut v_h__2_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_271_ == 0 {
        let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_272_);
        v___x_274_ = crate::leanh::lean_apply_1(v_h__2_273_, crate::leanh::lean_box(0));
        return v___x_274_;
    } else {
        let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_273_);
        v___x_275_ = crate::leanh::lean_apply_1(v_h__1_272_, crate::leanh::lean_box(0));
        return v___x_275_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___boxed(
    mut v_motive_276_: *mut crate::leanh::LeanObject,
    mut v_x_277_: *mut crate::leanh::LeanObject,
    mut v_h__1_278_: *mut crate::leanh::LeanObject,
    mut v_h__2_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_280_: u8 = 0;
    let mut v_res_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_280_ = (crate::leanh::lean_unbox(v_x_277_) as u8);
    v_res_281_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(v_motive_276_, v_x_33__boxed_280_, v_h__1_278_, v_h__2_279_);
    return v_res_281_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___redArg(
    mut v_x_282_: *mut crate::leanh::LeanObject,
    mut v_h__1_283_: *mut crate::leanh::LeanObject,
    mut v_h__2_284_: *mut crate::leanh::LeanObject,
    mut v_h__3_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_282_) {
        0 => {
            let mut v_it_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_285_);
            crate::leanh::lean_dec(v_h__2_284_);
            v_it_286_ = crate::leanh::lean_ctor_get(v_x_282_, 0);
            crate::leanh::lean_inc(v_it_286_);
            v_out_287_ = crate::leanh::lean_ctor_get(v_x_282_, 1);
            crate::leanh::lean_inc(v_out_287_);
            crate::leanh::lean_dec_ref_known(v_x_282_, 2);
            v___x_288_ = crate::leanh::lean_apply_3(
                v_h__1_283_,
                v_it_286_,
                v_out_287_,
                crate::leanh::lean_box(0),
            );
            return v___x_288_;
        }
        1 => {
            let mut v_it_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_285_);
            crate::leanh::lean_dec(v_h__1_283_);
            v_it_289_ = crate::leanh::lean_ctor_get(v_x_282_, 0);
            crate::leanh::lean_inc(v_it_289_);
            crate::leanh::lean_dec_ref_known(v_x_282_, 1);
            v___x_290_ =
                crate::leanh::lean_apply_2(v_h__2_284_, v_it_289_, crate::leanh::lean_box(0));
            return v___x_290_;
        }
        _ => {
            let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_284_);
            crate::leanh::lean_dec(v_h__1_283_);
            v___x_291_ = crate::leanh::lean_apply_1(v_h__3_285_, crate::leanh::lean_box(0));
            return v___x_291_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(
    mut v_00_u03b1_292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
    mut v_it_295_: *mut crate::leanh::LeanObject,
    mut v_motive_296_: *mut crate::leanh::LeanObject,
    mut v_x_297_: *mut crate::leanh::LeanObject,
    mut v_h__1_298_: *mut crate::leanh::LeanObject,
    mut v_h__2_299_: *mut crate::leanh::LeanObject,
    mut v_h__3_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_297_) {
        0 => {
            let mut v_it_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_300_);
            crate::leanh::lean_dec(v_h__2_299_);
            v_it_301_ = crate::leanh::lean_ctor_get(v_x_297_, 0);
            crate::leanh::lean_inc(v_it_301_);
            v_out_302_ = crate::leanh::lean_ctor_get(v_x_297_, 1);
            crate::leanh::lean_inc(v_out_302_);
            crate::leanh::lean_dec_ref_known(v_x_297_, 2);
            v___x_303_ = crate::leanh::lean_apply_3(
                v_h__1_298_,
                v_it_301_,
                v_out_302_,
                crate::leanh::lean_box(0),
            );
            return v___x_303_;
        }
        1 => {
            let mut v_it_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_300_);
            crate::leanh::lean_dec(v_h__1_298_);
            v_it_304_ = crate::leanh::lean_ctor_get(v_x_297_, 0);
            crate::leanh::lean_inc(v_it_304_);
            crate::leanh::lean_dec_ref_known(v_x_297_, 1);
            v___x_305_ =
                crate::leanh::lean_apply_2(v_h__2_299_, v_it_304_, crate::leanh::lean_box(0));
            return v___x_305_;
        }
        _ => {
            let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_299_);
            crate::leanh::lean_dec(v_h__1_298_);
            v___x_306_ = crate::leanh::lean_apply_1(v_h__3_300_, crate::leanh::lean_box(0));
            return v___x_306_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___boxed(
    mut v_00_u03b1_307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
    mut v_it_310_: *mut crate::leanh::LeanObject,
    mut v_motive_311_: *mut crate::leanh::LeanObject,
    mut v_x_312_: *mut crate::leanh::LeanObject,
    mut v_h__1_313_: *mut crate::leanh::LeanObject,
    mut v_h__2_314_: *mut crate::leanh::LeanObject,
    mut v_h__3_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(v_00_u03b1_307_, v_00_u03b2_308_, v_inst_309_, v_it_310_, v_motive_311_, v_x_312_, v_h__1_313_, v_h__2_314_, v_h__3_315_);
    crate::leanh::lean_dec(v_it_310_);
    crate::leanh::lean_dec(v_inst_309_);
    return v_res_316_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(
    mut v_x_317_: u8,
    mut v_h__1_318_: *mut crate::leanh::LeanObject,
    mut v_h__2_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_317_ == 0 {
        let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_318_);
        v___x_320_ = crate::leanh::lean_apply_1(v_h__2_319_, crate::leanh::lean_box(0));
        return v___x_320_;
    } else {
        let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_319_);
        v___x_321_ = crate::leanh::lean_apply_1(v_h__1_318_, crate::leanh::lean_box(0));
        return v___x_321_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_322_: *mut crate::leanh::LeanObject,
    mut v_h__1_323_: *mut crate::leanh::LeanObject,
    mut v_h__2_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_325_: u8 = 0;
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_325_ = (crate::leanh::lean_unbox(v_x_322_) as u8);
    v_res_326_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_325_, v_h__1_323_, v_h__2_324_);
    return v_res_326_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(
    mut v_motive_327_: *mut crate::leanh::LeanObject,
    mut v_x_328_: u8,
    mut v_h__1_329_: *mut crate::leanh::LeanObject,
    mut v_h__2_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_328_ == 0 {
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_329_);
        v___x_331_ = crate::leanh::lean_apply_1(v_h__2_330_, crate::leanh::lean_box(0));
        return v___x_331_;
    } else {
        let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_330_);
        v___x_332_ = crate::leanh::lean_apply_1(v_h__1_329_, crate::leanh::lean_box(0));
        return v___x_332_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___boxed(
    mut v_motive_333_: *mut crate::leanh::LeanObject,
    mut v_x_334_: *mut crate::leanh::LeanObject,
    mut v_h__1_335_: *mut crate::leanh::LeanObject,
    mut v_h__2_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_337_: u8 = 0;
    let mut v_res_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_337_ = (crate::leanh::lean_unbox(v_x_334_) as u8);
    v_res_338_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(v_motive_333_, v_x_33__boxed_337_, v_h__1_335_, v_h__2_336_);
    return v_res_338_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter___redArg(
    mut v_x_339_: *mut crate::leanh::LeanObject,
    mut v_h__1_340_: *mut crate::leanh::LeanObject,
    mut v_h__2_341_: *mut crate::leanh::LeanObject,
    mut v_h__3_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_339_) {
        0 => {
            let mut v_it_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_342_);
            crate::leanh::lean_dec(v_h__2_341_);
            v_it_343_ = crate::leanh::lean_ctor_get(v_x_339_, 0);
            crate::leanh::lean_inc(v_it_343_);
            v_out_344_ = crate::leanh::lean_ctor_get(v_x_339_, 1);
            crate::leanh::lean_inc(v_out_344_);
            crate::leanh::lean_dec_ref_known(v_x_339_, 2);
            v___x_345_ = crate::leanh::lean_apply_2(v_h__1_340_, v_it_343_, v_out_344_);
            return v___x_345_;
        }
        1 => {
            let mut v_it_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_342_);
            crate::leanh::lean_dec(v_h__1_340_);
            v_it_346_ = crate::leanh::lean_ctor_get(v_x_339_, 0);
            crate::leanh::lean_inc(v_it_346_);
            crate::leanh::lean_dec_ref_known(v_x_339_, 1);
            v___x_347_ = crate::leanh::lean_apply_1(v_h__2_341_, v_it_346_);
            return v___x_347_;
        }
        _ => {
            let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_341_);
            crate::leanh::lean_dec(v_h__1_340_);
            v___x_348_ = crate::leanh::lean_box(0);
            v___x_349_ = crate::leanh::lean_apply_1(v_h__3_342_, v___x_348_);
            return v___x_349_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter(
    mut v_00_u03b1_350_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_351_: *mut crate::leanh::LeanObject,
    mut v_motive_352_: *mut crate::leanh::LeanObject,
    mut v_x_353_: *mut crate::leanh::LeanObject,
    mut v_h__1_354_: *mut crate::leanh::LeanObject,
    mut v_h__2_355_: *mut crate::leanh::LeanObject,
    mut v_h__3_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_353_) {
        0 => {
            let mut v_it_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_356_);
            crate::leanh::lean_dec(v_h__2_355_);
            v_it_357_ = crate::leanh::lean_ctor_get(v_x_353_, 0);
            crate::leanh::lean_inc(v_it_357_);
            v_out_358_ = crate::leanh::lean_ctor_get(v_x_353_, 1);
            crate::leanh::lean_inc(v_out_358_);
            crate::leanh::lean_dec_ref_known(v_x_353_, 2);
            v___x_359_ = crate::leanh::lean_apply_2(v_h__1_354_, v_it_357_, v_out_358_);
            return v___x_359_;
        }
        1 => {
            let mut v_it_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_356_);
            crate::leanh::lean_dec(v_h__1_354_);
            v_it_360_ = crate::leanh::lean_ctor_get(v_x_353_, 0);
            crate::leanh::lean_inc(v_it_360_);
            crate::leanh::lean_dec_ref_known(v_x_353_, 1);
            v___x_361_ = crate::leanh::lean_apply_1(v_h__2_355_, v_it_360_);
            return v___x_361_;
        }
        _ => {
            let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_355_);
            crate::leanh::lean_dec(v_h__1_354_);
            v___x_362_ = crate::leanh::lean_box(0);
            v___x_363_ = crate::leanh::lean_apply_1(v_h__3_356_, v___x_362_);
            return v___x_363_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(
    mut v_x_364_: u8,
    mut v_h__1_365_: *mut crate::leanh::LeanObject,
    mut v_h__2_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_364_ == 0 {
        let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_365_);
        v___x_367_ = crate::leanh::lean_box(0);
        v___x_368_ = crate::leanh::lean_apply_1(v_h__2_366_, v___x_367_);
        return v___x_368_;
    } else {
        let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_366_);
        v___x_369_ = crate::leanh::lean_box(0);
        v___x_370_ = crate::leanh::lean_apply_1(v_h__1_365_, v___x_369_);
        return v___x_370_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_371_: *mut crate::leanh::LeanObject,
    mut v_h__1_372_: *mut crate::leanh::LeanObject,
    mut v_h__2_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_374_: u8 = 0;
    let mut v_res_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_374_ = (crate::leanh::lean_unbox(v_x_371_) as u8);
    v_res_375_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_374_, v_h__1_372_, v_h__2_373_);
    return v_res_375_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(
    mut v_motive_376_: *mut crate::leanh::LeanObject,
    mut v_x_377_: u8,
    mut v_h__1_378_: *mut crate::leanh::LeanObject,
    mut v_h__2_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_377_ == 0 {
        let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_378_);
        v___x_380_ = crate::leanh::lean_box(0);
        v___x_381_ = crate::leanh::lean_apply_1(v_h__2_379_, v___x_380_);
        return v___x_381_;
    } else {
        let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_379_);
        v___x_382_ = crate::leanh::lean_box(0);
        v___x_383_ = crate::leanh::lean_apply_1(v_h__1_378_, v___x_382_);
        return v___x_383_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___boxed(
    mut v_motive_384_: *mut crate::leanh::LeanObject,
    mut v_x_385_: *mut crate::leanh::LeanObject,
    mut v_h__1_386_: *mut crate::leanh::LeanObject,
    mut v_h__2_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_388_: u8 = 0;
    let mut v_res_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_388_ = (crate::leanh::lean_unbox(v_x_385_) as u8);
    v_res_389_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(v_motive_384_, v_x_37__boxed_388_, v_h__1_386_, v_h__2_387_);
    return v_res_389_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(
    mut v_x_390_: *mut crate::leanh::LeanObject,
    mut v_h__1_391_: *mut crate::leanh::LeanObject,
    mut v_h__2_392_: *mut crate::leanh::LeanObject,
    mut v_h__3_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_390_) {
        0 => {
            let mut v_it_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_393_);
            crate::leanh::lean_dec(v_h__2_392_);
            v_it_394_ = crate::leanh::lean_ctor_get(v_x_390_, 0);
            crate::leanh::lean_inc(v_it_394_);
            v_out_395_ = crate::leanh::lean_ctor_get(v_x_390_, 1);
            crate::leanh::lean_inc(v_out_395_);
            crate::leanh::lean_dec_ref_known(v_x_390_, 2);
            v___x_396_ = crate::leanh::lean_apply_2(v_h__1_391_, v_it_394_, v_out_395_);
            return v___x_396_;
        }
        1 => {
            let mut v_it_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_393_);
            crate::leanh::lean_dec(v_h__1_391_);
            v_it_397_ = crate::leanh::lean_ctor_get(v_x_390_, 0);
            crate::leanh::lean_inc(v_it_397_);
            crate::leanh::lean_dec_ref_known(v_x_390_, 1);
            v___x_398_ = crate::leanh::lean_apply_1(v_h__2_392_, v_it_397_);
            return v___x_398_;
        }
        _ => {
            let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_392_);
            crate::leanh::lean_dec(v_h__1_391_);
            v___x_399_ = crate::leanh::lean_box(0);
            v___x_400_ = crate::leanh::lean_apply_1(v_h__3_393_, v___x_399_);
            return v___x_400_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(
    mut v_00_u03b1_401_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_402_: *mut crate::leanh::LeanObject,
    mut v_motive_403_: *mut crate::leanh::LeanObject,
    mut v_x_404_: *mut crate::leanh::LeanObject,
    mut v_h__1_405_: *mut crate::leanh::LeanObject,
    mut v_h__2_406_: *mut crate::leanh::LeanObject,
    mut v_h__3_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_404_) {
        0 => {
            let mut v_it_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_407_);
            crate::leanh::lean_dec(v_h__2_406_);
            v_it_408_ = crate::leanh::lean_ctor_get(v_x_404_, 0);
            crate::leanh::lean_inc(v_it_408_);
            v_out_409_ = crate::leanh::lean_ctor_get(v_x_404_, 1);
            crate::leanh::lean_inc(v_out_409_);
            crate::leanh::lean_dec_ref_known(v_x_404_, 2);
            v___x_410_ = crate::leanh::lean_apply_2(v_h__1_405_, v_it_408_, v_out_409_);
            return v___x_410_;
        }
        1 => {
            let mut v_it_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_407_);
            crate::leanh::lean_dec(v_h__1_405_);
            v_it_411_ = crate::leanh::lean_ctor_get(v_x_404_, 0);
            crate::leanh::lean_inc(v_it_411_);
            crate::leanh::lean_dec_ref_known(v_x_404_, 1);
            v___x_412_ = crate::leanh::lean_apply_1(v_h__2_406_, v_it_411_);
            return v___x_412_;
        }
        _ => {
            let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_406_);
            crate::leanh::lean_dec(v_h__1_405_);
            v___x_413_ = crate::leanh::lean_box(0);
            v___x_414_ = crate::leanh::lean_apply_1(v_h__3_407_, v___x_413_);
            return v___x_414_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_415_: *mut crate::leanh::LeanObject,
    mut v_h__1_416_: *mut crate::leanh::LeanObject,
    mut v_h__2_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_419_: u8 = 0;
    v_zero_418_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_419_ = lean_nat_dec_eq(v_n_415_, v_zero_418_);
    if v_isZero_419_ == 1 {
        let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_417_);
        v___x_420_ = crate::leanh::lean_box(0);
        v___x_421_ = crate::leanh::lean_apply_1(v_h__1_416_, v___x_420_);
        return v___x_421_;
    } else {
        let mut v_one_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_416_);
        v_one_422_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_423_ = lean_nat_sub(v_n_415_, v_one_422_);
        v___x_424_ = crate::leanh::lean_apply_1(v_h__2_417_, v_n_423_);
        return v___x_424_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_425_: *mut crate::leanh::LeanObject,
    mut v_h__1_426_: *mut crate::leanh::LeanObject,
    mut v_h__2_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_425_, v_h__1_426_, v_h__2_427_);
    crate::leanh::lean_dec(v_n_425_);
    return v_res_428_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_429_: *mut crate::leanh::LeanObject,
    mut v_n_430_: *mut crate::leanh::LeanObject,
    mut v_h__1_431_: *mut crate::leanh::LeanObject,
    mut v_h__2_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_434_: u8 = 0;
    v_zero_433_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_434_ = lean_nat_dec_eq(v_n_430_, v_zero_433_);
    if v_isZero_434_ == 1 {
        let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_432_);
        v___x_435_ = crate::leanh::lean_box(0);
        v___x_436_ = crate::leanh::lean_apply_1(v_h__1_431_, v___x_435_);
        return v___x_436_;
    } else {
        let mut v_one_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_431_);
        v_one_437_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_438_ = lean_nat_sub(v_n_430_, v_one_437_);
        v___x_439_ = crate::leanh::lean_apply_1(v_h__2_432_, v_n_438_);
        return v___x_439_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_440_: *mut crate::leanh::LeanObject,
    mut v_n_441_: *mut crate::leanh::LeanObject,
    mut v_h__1_442_: *mut crate::leanh::LeanObject,
    mut v_h__2_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_444_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_440_, v_n_441_, v_h__1_442_, v_h__2_443_);
    crate::leanh::lean_dec(v_n_441_);
    return v_res_444_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
}
