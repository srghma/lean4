// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Take
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Init.Classical Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub unsafe fn l_Std_IterM_take___redArg(
    mut v_n_192_: *mut LeanObject,
    mut v_it_193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    v___x_194_ = lean_unsigned_to_nat(1);
    v___x_195_ = lean_nat_add(v_n_192_, v___x_194_);
    v___x_196_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_196_, 0, v___x_195_);
    lean_ctor_set(v___x_196_, 1, v_it_193_);
    return v___x_196_;
}
pub unsafe fn l_Std_IterM_take___redArg___boxed(
    mut v_n_197_: *mut LeanObject,
    mut v_it_198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_199_: *mut LeanObject = core::ptr::null_mut();
    v_res_199_ = l_Std_IterM_take___redArg(v_n_197_, v_it_198_);
    lean_dec(v_n_197_);
    return v_res_199_;
}
pub unsafe fn l_Std_IterM_take(
    mut v_00_u03b1_200_: *mut LeanObject,
    mut v_m_201_: *mut LeanObject,
    mut v_00_u03b2_202_: *mut LeanObject,
    mut v_inst_203_: *mut LeanObject,
    mut v_n_204_: *mut LeanObject,
    mut v_it_205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    v___x_206_ = lean_unsigned_to_nat(1);
    v___x_207_ = lean_nat_add(v_n_204_, v___x_206_);
    v___x_208_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_208_, 0, v___x_207_);
    lean_ctor_set(v___x_208_, 1, v_it_205_);
    return v___x_208_;
}
pub unsafe fn l_Std_IterM_take___boxed(
    mut v_00_u03b1_209_: *mut LeanObject,
    mut v_m_210_: *mut LeanObject,
    mut v_00_u03b2_211_: *mut LeanObject,
    mut v_inst_212_: *mut LeanObject,
    mut v_n_213_: *mut LeanObject,
    mut v_it_214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_215_: *mut LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Std_IterM_take(
        v_00_u03b1_209_,
        v_m_210_,
        v_00_u03b2_211_,
        v_inst_212_,
        v_n_213_,
        v_it_214_,
    );
    lean_dec(v_n_213_);
    lean_dec(v_inst_212_);
    return v_res_215_;
}
pub unsafe fn l_Std_IterM_toTake___redArg(mut v_it_216_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    v___x_217_ = lean_unsigned_to_nat(0);
    v___x_218_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_218_, 0, v___x_217_);
    lean_ctor_set(v___x_218_, 1, v_it_216_);
    return v___x_218_;
}
pub unsafe fn l_Std_IterM_toTake(
    mut v_00_u03b1_219_: *mut LeanObject,
    mut v_m_220_: *mut LeanObject,
    mut v_00_u03b2_221_: *mut LeanObject,
    mut v_inst_222_: *mut LeanObject,
    mut v_inst_223_: *mut LeanObject,
    mut v_it_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    v___x_225_ = lean_unsigned_to_nat(0);
    v___x_226_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_226_, 0, v___x_225_);
    lean_ctor_set(v___x_226_, 1, v_it_224_);
    return v___x_226_;
}
pub unsafe fn l_Std_IterM_toTake___boxed(
    mut v_00_u03b1_227_: *mut LeanObject,
    mut v_m_228_: *mut LeanObject,
    mut v_00_u03b2_229_: *mut LeanObject,
    mut v_inst_230_: *mut LeanObject,
    mut v_inst_231_: *mut LeanObject,
    mut v_it_232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_233_: *mut LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Std_IterM_toTake(
        v_00_u03b1_227_,
        v_m_228_,
        v_00_u03b2_229_,
        v_inst_230_,
        v_inst_231_,
        v_it_232_,
    );
    lean_dec(v_inst_230_);
    return v_res_233_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(
    mut v_toApplicative_234_: *mut LeanObject,
    mut v_countdown_235_: *mut LeanObject,
    mut v___x_236_: *mut LeanObject,
    mut v_____do__lift_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_242_: u8 = 0;
    let mut v_toPure_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_250_: u8 = 0;
    let mut v_it_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_254_: u8 = 0;
    let mut v_toPure_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_261_: u8 = 0;
    let mut v_toPure_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_237_) {
                0 => {
                    v_it_238_ = lean_ctor_get(v_____do__lift_237_, 0);
                    v_out_239_ = lean_ctor_get(v_____do__lift_237_, 1);
                    v_isSharedCheck_250_ = (!lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_250_ == 0 {
                        v___x_241_ = v_____do__lift_237_;
                        v_isShared_242_ = v_isSharedCheck_250_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_239_);
                        lean_inc(v_it_238_);
                        lean_dec(v_____do__lift_237_);
                        v___x_241_ = lean_box(0);
                        v_isShared_242_ = v_isSharedCheck_250_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_251_ = lean_ctor_get(v_____do__lift_237_, 0);
                    v_isSharedCheck_261_ = (!lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_261_ == 0 {
                        v___x_253_ = v_____do__lift_237_;
                        v_isShared_254_ = v_isSharedCheck_261_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_251_);
                        lean_dec(v_____do__lift_237_);
                        v___x_253_ = lean_box(0);
                        v_isShared_254_ = v_isSharedCheck_261_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_countdown_235_);
                    v_toPure_262_ = lean_ctor_get(v_toApplicative_234_, 1);
                    lean_inc(v_toPure_262_);
                    lean_dec_ref(v_toApplicative_234_);
                    v___x_263_ = lean_box(2);
                    v___x_264_ = lean_apply_2(v_toPure_262_, lean_box(0), v___x_263_);
                    return v___x_264_;
                }
            },
            1 => {
                v_toPure_243_ = lean_ctor_get(v_toApplicative_234_, 1);
                lean_inc(v_toPure_243_);
                lean_dec_ref(v_toApplicative_234_);
                v___x_244_ = lean_nat_sub(v_countdown_235_, v___x_236_);
                lean_dec(v_countdown_235_);
                v___x_245_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_245_, 0, v___x_244_);
                lean_ctor_set(v___x_245_, 1, v_it_238_);
                if v_isShared_242_ == 0 {
                    lean_ctor_set(v___x_241_, 0, v___x_245_);
                    v___x_247_ = v___x_241_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
                    lean_ctor_set(v_reuseFailAlloc_249_, 1, v_out_239_);
                    v___x_247_ = v_reuseFailAlloc_249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_248_ = lean_apply_2(v_toPure_243_, lean_box(0), v___x_247_);
                return v___x_248_;
            }
            3 => {
                v_toPure_255_ = lean_ctor_get(v_toApplicative_234_, 1);
                lean_inc(v_toPure_255_);
                lean_dec_ref(v_toApplicative_234_);
                v___x_256_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_256_, 0, v_countdown_235_);
                lean_ctor_set(v___x_256_, 1, v_it_251_);
                if v_isShared_254_ == 0 {
                    lean_ctor_set(v___x_253_, 0, v___x_256_);
                    v___x_258_ = v___x_253_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
                    v___x_258_ = v_reuseFailAlloc_260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_259_ = lean_apply_2(v_toPure_255_, lean_box(0), v___x_258_);
                return v___x_259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed(
    mut v_toApplicative_265_: *mut LeanObject,
    mut v_countdown_266_: *mut LeanObject,
    mut v___x_267_: *mut LeanObject,
    mut v_____do__lift_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(
        v_toApplicative_265_,
        v_countdown_266_,
        v___x_267_,
        v_____do__lift_268_,
    );
    lean_dec(v___x_267_);
    return v_res_269_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg___lam__1(
    mut v_inst_270_: *mut LeanObject,
    mut v_inst_271_: *mut LeanObject,
    mut v_it_272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_countdown_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: u8 = 0;
    v_countdown_273_ = lean_ctor_get(v_it_272_, 0);
    lean_inc(v_countdown_273_);
    v_inner_274_ = lean_ctor_get(v_it_272_, 1);
    lean_inc(v_inner_274_);
    lean_dec_ref(v_it_272_);
    v___x_275_ = lean_unsigned_to_nat(1);
    v___x_276_ = lean_nat_dec_eq(v_countdown_273_, v___x_275_);
    if v___x_276_ == 0 {
        let mut v_toApplicative_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_277_ = lean_ctor_get(v_inst_270_, 0);
        lean_inc_ref(v_toApplicative_277_);
        v_toBind_278_ = lean_ctor_get(v_inst_270_, 1);
        lean_inc(v_toBind_278_);
        lean_dec_ref(v_inst_270_);
        v___f_279_ = lean_alloc_closure(
            l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_279_, 0, v_toApplicative_277_);
        lean_closure_set(v___f_279_, 1, v_countdown_273_);
        lean_closure_set(v___f_279_, 2, v___x_275_);
        v___x_280_ = lean_apply_1(v_inst_271_, v_inner_274_);
        v___x_281_ = lean_apply_4(
            v_toBind_278_,
            lean_box(0),
            lean_box(0),
            v___x_280_,
            v___f_279_,
        );
        return v___x_281_;
    } else {
        let mut v_toApplicative_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inner_274_);
        lean_dec(v_countdown_273_);
        lean_dec(v_inst_271_);
        v_toApplicative_282_ = lean_ctor_get(v_inst_270_, 0);
        lean_inc_ref(v_toApplicative_282_);
        lean_dec_ref(v_inst_270_);
        v_toPure_283_ = lean_ctor_get(v_toApplicative_282_, 1);
        lean_inc(v_toPure_283_);
        lean_dec_ref(v_toApplicative_282_);
        v___x_284_ = lean_box(2);
        v___x_285_ = lean_apply_2(v_toPure_283_, lean_box(0), v___x_284_);
        return v___x_285_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg(
    mut v_inst_286_: *mut LeanObject,
    mut v_inst_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_288_: *mut LeanObject = core::ptr::null_mut();
    v___f_288_ = lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_288_, 0, v_inst_286_);
    lean_closure_set(v___f_288_, 1, v_inst_287_);
    return v___f_288_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator(
    mut v_00_u03b1_289_: *mut LeanObject,
    mut v_m_290_: *mut LeanObject,
    mut v_00_u03b2_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_294_: *mut LeanObject = core::ptr::null_mut();
    v___f_294_ = lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_294_, 0, v_inst_292_);
    lean_closure_set(v___f_294_, 1, v_inst_293_);
    return v___f_294_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(
    mut v_00_u03b1_295_: *mut LeanObject,
    mut v_m_296_: *mut LeanObject,
    mut v_00_u03b2_297_: *mut LeanObject,
    mut v_inst_298_: *mut LeanObject,
    mut v_inst_299_: *mut LeanObject,
    mut v_inst_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = lean_box(0);
    return v___x_301_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___boxed(
    mut v_00_u03b1_302_: *mut LeanObject,
    mut v_m_303_: *mut LeanObject,
    mut v_00_u03b2_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
    mut v_inst_306_: *mut LeanObject,
    mut v_inst_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_308_: *mut LeanObject = core::ptr::null_mut();
    v_res_308_ = l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(v_00_u03b1_302_, v_m_303_, v_00_u03b2_304_, v_inst_305_, v_inst_306_, v_inst_307_);
    lean_dec(v_inst_306_);
    lean_dec_ref(v_inst_305_);
    return v_res_308_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0(
    mut v_toPure_309_: *mut LeanObject,
    mut v_recur_310_: *mut LeanObject,
    mut v_it_311_: *mut LeanObject,
    mut v_____do__lift_312_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_312_) == 0 {
        let mut v_a_313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_311_);
        lean_dec(v_recur_310_);
        v_a_313_ = lean_ctor_get(v_____do__lift_312_, 0);
        lean_inc(v_a_313_);
        lean_dec_ref_known(v_____do__lift_312_, 1);
        v___x_314_ = lean_apply_2(v_toPure_309_, lean_box(0), v_a_313_);
        return v___x_314_;
    } else {
        let mut v_a_315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_309_);
        v_a_315_ = lean_ctor_get(v_____do__lift_312_, 0);
        lean_inc(v_a_315_);
        lean_dec_ref_known(v_____do__lift_312_, 1);
        v___x_316_ = lean_apply_4(v_recur_310_, v_it_311_, v_a_315_, lean_box(0), lean_box(0));
        return v___x_316_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1(
    mut v_toPure_317_: *mut LeanObject,
    mut v_recur_318_: *mut LeanObject,
    mut v___y_319_: *mut LeanObject,
    mut v_acc_320_: *mut LeanObject,
    mut v_toBind_321_: *mut LeanObject,
    mut v_s_322_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_322_) {
        0 => {
            let mut v_it_323_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
            v_it_323_ = lean_ctor_get(v_s_322_, 0);
            lean_inc(v_it_323_);
            v_out_324_ = lean_ctor_get(v_s_322_, 1);
            lean_inc(v_out_324_);
            lean_dec_ref_known(v_s_322_, 2);
            v___f_325_ = lean_alloc_closure(
                l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_325_, 0, v_toPure_317_);
            lean_closure_set(v___f_325_, 1, v_recur_318_);
            lean_closure_set(v___f_325_, 2, v_it_323_);
            v___x_326_ = lean_apply_3(v___y_319_, v_out_324_, lean_box(0), v_acc_320_);
            v___x_327_ = lean_apply_4(
                v_toBind_321_,
                lean_box(0),
                lean_box(0),
                v___x_326_,
                v___f_325_,
            );
            return v___x_327_;
        }
        1 => {
            let mut v_it_328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_321_);
            lean_dec(v___y_319_);
            lean_dec(v_toPure_317_);
            v_it_328_ = lean_ctor_get(v_s_322_, 0);
            lean_inc(v_it_328_);
            lean_dec_ref_known(v_s_322_, 1);
            v___x_329_ = lean_apply_4(
                v_recur_318_,
                v_it_328_,
                v_acc_320_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_329_;
        }
        _ => {
            let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_321_);
            lean_dec(v___y_319_);
            lean_dec(v_recur_318_);
            v___x_330_ = lean_apply_2(v_toPure_317_, lean_box(0), v_acc_320_);
            return v___x_330_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3(
    mut v_toPure_331_: *mut LeanObject,
    mut v___y_332_: *mut LeanObject,
    mut v_toBind_333_: *mut LeanObject,
    mut v_inst_334_: *mut LeanObject,
    mut v_inst_335_: *mut LeanObject,
    mut v_lift_336_: *mut LeanObject,
    mut v_it_337_: *mut LeanObject,
    mut v_acc_338_: *mut LeanObject,
    mut v_hP_339_: *mut LeanObject,
    mut v_recur_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_countdown_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: u8 = 0;
    v_countdown_341_ = lean_ctor_get(v_it_337_, 0);
    lean_inc(v_countdown_341_);
    v_inner_342_ = lean_ctor_get(v_it_337_, 1);
    lean_inc(v_inner_342_);
    lean_dec_ref(v_it_337_);
    v___f_343_ = lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_343_, 0, v_toPure_331_);
    lean_closure_set(v___f_343_, 1, v_recur_340_);
    lean_closure_set(v___f_343_, 2, v___y_332_);
    lean_closure_set(v___f_343_, 3, v_acc_338_);
    lean_closure_set(v___f_343_, 4, v_toBind_333_);
    v___x_344_ = lean_unsigned_to_nat(1);
    v___x_345_ = lean_nat_dec_eq(v_countdown_341_, v___x_344_);
    if v___x_345_ == 0 {
        let mut v_toApplicative_346_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_346_ = lean_ctor_get(v_inst_334_, 0);
        lean_inc_ref(v_toApplicative_346_);
        v_toBind_347_ = lean_ctor_get(v_inst_334_, 1);
        lean_inc(v_toBind_347_);
        lean_dec_ref(v_inst_334_);
        v___f_348_ = lean_alloc_closure(
            l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_348_, 0, v_toApplicative_346_);
        lean_closure_set(v___f_348_, 1, v_countdown_341_);
        lean_closure_set(v___f_348_, 2, v___x_344_);
        v___x_349_ = lean_apply_1(v_inst_335_, v_inner_342_);
        v___x_350_ = lean_apply_4(
            v_toBind_347_,
            lean_box(0),
            lean_box(0),
            v___x_349_,
            v___f_348_,
        );
        v___x_351_ = lean_apply_4(
            v_lift_336_,
            lean_box(0),
            lean_box(0),
            v___f_343_,
            v___x_350_,
        );
        return v___x_351_;
    } else {
        let mut v_toApplicative_352_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inner_342_);
        lean_dec(v_countdown_341_);
        lean_dec(v_inst_335_);
        v_toApplicative_352_ = lean_ctor_get(v_inst_334_, 0);
        lean_inc_ref(v_toApplicative_352_);
        lean_dec_ref(v_inst_334_);
        v_toPure_353_ = lean_ctor_get(v_toApplicative_352_, 1);
        lean_inc(v_toPure_353_);
        lean_dec_ref(v_toApplicative_352_);
        v___x_354_ = lean_box(2);
        v___x_355_ = lean_apply_2(v_toPure_353_, lean_box(0), v___x_354_);
        v___x_356_ = lean_apply_4(
            v_lift_336_,
            lean_box(0),
            lean_box(0),
            v___f_343_,
            v___x_355_,
        );
        return v___x_356_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2(
    mut v_inst_357_: *mut LeanObject,
    mut v_inst_358_: *mut LeanObject,
    mut v_inst_359_: *mut LeanObject,
    mut v_lift_360_: *mut LeanObject,
    mut v_00_u03b3_361_: *mut LeanObject,
    mut v_Pl_362_: *mut LeanObject,
    mut v_it_363_: *mut LeanObject,
    mut v_init_364_: *mut LeanObject,
    mut v___y_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_366_ = lean_ctor_get(v_inst_357_, 0);
    lean_inc_ref(v_toApplicative_366_);
    v_toBind_367_ = lean_ctor_get(v_inst_357_, 1);
    lean_inc(v_toBind_367_);
    lean_dec_ref(v_inst_357_);
    v_toPure_368_ = lean_ctor_get(v_toApplicative_366_, 1);
    lean_inc(v_toPure_368_);
    lean_dec_ref(v_toApplicative_366_);
    v___f_369_ = lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        10,
        6,
    );
    lean_closure_set(v___f_369_, 0, v_toPure_368_);
    lean_closure_set(v___f_369_, 1, v___y_365_);
    lean_closure_set(v___f_369_, 2, v_toBind_367_);
    lean_closure_set(v___f_369_, 3, v_inst_358_);
    lean_closure_set(v___f_369_, 4, v_inst_359_);
    lean_closure_set(v___f_369_, 5, v_lift_360_);
    v___x_370_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_369_, v_it_363_, v_init_364_, lean_box(0));
    return v___x_370_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg(
    mut v_inst_371_: *mut LeanObject,
    mut v_inst_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_374_: *mut LeanObject = core::ptr::null_mut();
    v___f_374_ = lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_374_, 0, v_inst_372_);
    lean_closure_set(v___f_374_, 1, v_inst_371_);
    lean_closure_set(v___f_374_, 2, v_inst_373_);
    return v___f_374_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop(
    mut v_00_u03b1_375_: *mut LeanObject,
    mut v_m_376_: *mut LeanObject,
    mut v_00_u03b2_377_: *mut LeanObject,
    mut v_n_378_: *mut LeanObject,
    mut v_inst_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_382_: *mut LeanObject = core::ptr::null_mut();
    v___f_382_ = lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_382_, 0, v_inst_380_);
    lean_closure_set(v___f_382_, 1, v_inst_379_);
    lean_closure_set(v___f_382_, 2, v_inst_381_);
    return v___f_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
}
