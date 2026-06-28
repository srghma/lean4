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
pub unsafe fn l_Std_IterM_take___redArg(
    mut v_n_192_: *mut crate::leanh::LeanObject,
    mut v_it_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_194_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_195_ = lean_nat_add(v_n_192_, v___x_194_);
    v___x_196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_196_, 0, v___x_195_);
    crate::leanh::lean_ctor_set(v___x_196_, 1, v_it_193_);
    return v___x_196_;
}
pub unsafe fn l_Std_IterM_take___redArg___boxed(
    mut v_n_197_: *mut crate::leanh::LeanObject,
    mut v_it_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l_Std_IterM_take___redArg(v_n_197_, v_it_198_);
    crate::leanh::lean_dec(v_n_197_);
    return v_res_199_;
}
pub unsafe fn l_Std_IterM_take(
    mut v_00_u03b1_200_: *mut crate::leanh::LeanObject,
    mut v_m_201_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_202_: *mut crate::leanh::LeanObject,
    mut v_inst_203_: *mut crate::leanh::LeanObject,
    mut v_n_204_: *mut crate::leanh::LeanObject,
    mut v_it_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_206_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_207_ = lean_nat_add(v_n_204_, v___x_206_);
    v___x_208_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_208_, 0, v___x_207_);
    crate::leanh::lean_ctor_set(v___x_208_, 1, v_it_205_);
    return v___x_208_;
}
pub unsafe fn l_Std_IterM_take___boxed(
    mut v_00_u03b1_209_: *mut crate::leanh::LeanObject,
    mut v_m_210_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_211_: *mut crate::leanh::LeanObject,
    mut v_inst_212_: *mut crate::leanh::LeanObject,
    mut v_n_213_: *mut crate::leanh::LeanObject,
    mut v_it_214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Std_IterM_take(
        v_00_u03b1_209_,
        v_m_210_,
        v_00_u03b2_211_,
        v_inst_212_,
        v_n_213_,
        v_it_214_,
    );
    crate::leanh::lean_dec(v_n_213_);
    crate::leanh::lean_dec(v_inst_212_);
    return v_res_215_;
}
pub unsafe fn l_Std_IterM_toTake___redArg(
    mut v_it_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_217_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_218_, 0, v___x_217_);
    crate::leanh::lean_ctor_set(v___x_218_, 1, v_it_216_);
    return v___x_218_;
}
pub unsafe fn l_Std_IterM_toTake(
    mut v_00_u03b1_219_: *mut crate::leanh::LeanObject,
    mut v_m_220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_221_: *mut crate::leanh::LeanObject,
    mut v_inst_222_: *mut crate::leanh::LeanObject,
    mut v_inst_223_: *mut crate::leanh::LeanObject,
    mut v_it_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_225_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_226_, 0, v___x_225_);
    crate::leanh::lean_ctor_set(v___x_226_, 1, v_it_224_);
    return v___x_226_;
}
pub unsafe fn l_Std_IterM_toTake___boxed(
    mut v_00_u03b1_227_: *mut crate::leanh::LeanObject,
    mut v_m_228_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_229_: *mut crate::leanh::LeanObject,
    mut v_inst_230_: *mut crate::leanh::LeanObject,
    mut v_inst_231_: *mut crate::leanh::LeanObject,
    mut v_it_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Std_IterM_toTake(
        v_00_u03b1_227_,
        v_m_228_,
        v_00_u03b2_229_,
        v_inst_230_,
        v_inst_231_,
        v_it_232_,
    );
    crate::leanh::lean_dec(v_inst_230_);
    return v_res_233_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(
    mut v_toApplicative_234_: *mut crate::leanh::LeanObject,
    mut v_countdown_235_: *mut crate::leanh::LeanObject,
    mut v___x_236_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_242_: u8 = 0;
    let mut v_toPure_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_250_: u8 = 0;
    let mut v_it_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_254_: u8 = 0;
    let mut v_toPure_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_261_: u8 = 0;
    let mut v_toPure_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_237_) {
                0 => {
                    v_it_238_ = crate::leanh::lean_ctor_get(v_____do__lift_237_, 0);
                    v_out_239_ = crate::leanh::lean_ctor_get(v_____do__lift_237_, 1);
                    v_isSharedCheck_250_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_250_ == 0 {
                        v___x_241_ = v_____do__lift_237_;
                        v_isShared_242_ = v_isSharedCheck_250_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_239_);
                        crate::leanh::lean_inc(v_it_238_);
                        crate::leanh::lean_dec(v_____do__lift_237_);
                        v___x_241_ = crate::leanh::lean_box(0);
                        v_isShared_242_ = v_isSharedCheck_250_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_251_ = crate::leanh::lean_ctor_get(v_____do__lift_237_, 0);
                    v_isSharedCheck_261_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_261_ == 0 {
                        v___x_253_ = v_____do__lift_237_;
                        v_isShared_254_ = v_isSharedCheck_261_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_251_);
                        crate::leanh::lean_dec(v_____do__lift_237_);
                        v___x_253_ = crate::leanh::lean_box(0);
                        v_isShared_254_ = v_isSharedCheck_261_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_countdown_235_);
                    v_toPure_262_ = crate::leanh::lean_ctor_get(v_toApplicative_234_, 1);
                    crate::leanh::lean_inc(v_toPure_262_);
                    crate::leanh::lean_dec_ref(v_toApplicative_234_);
                    v___x_263_ = crate::leanh::lean_box(2);
                    v___x_264_ = crate::leanh::lean_apply_2(
                        v_toPure_262_,
                        crate::leanh::lean_box(0),
                        v___x_263_,
                    );
                    return v___x_264_;
                }
            },
            1 => {
                v_toPure_243_ = crate::leanh::lean_ctor_get(v_toApplicative_234_, 1);
                crate::leanh::lean_inc(v_toPure_243_);
                crate::leanh::lean_dec_ref(v_toApplicative_234_);
                v___x_244_ = lean_nat_sub(v_countdown_235_, v___x_236_);
                crate::leanh::lean_dec(v_countdown_235_);
                v___x_245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_245_, 0, v___x_244_);
                crate::leanh::lean_ctor_set(v___x_245_, 1, v_it_238_);
                if v_isShared_242_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_241_, 0, v___x_245_);
                    v___x_247_ = v___x_241_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_249_, 1, v_out_239_);
                    v___x_247_ = v_reuseFailAlloc_249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_248_ = crate::leanh::lean_apply_2(
                    v_toPure_243_,
                    crate::leanh::lean_box(0),
                    v___x_247_,
                );
                return v___x_248_;
            }
            3 => {
                v_toPure_255_ = crate::leanh::lean_ctor_get(v_toApplicative_234_, 1);
                crate::leanh::lean_inc(v_toPure_255_);
                crate::leanh::lean_dec_ref(v_toApplicative_234_);
                v___x_256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_256_, 0, v_countdown_235_);
                crate::leanh::lean_ctor_set(v___x_256_, 1, v_it_251_);
                if v_isShared_254_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_253_, 0, v___x_256_);
                    v___x_258_ = v___x_253_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
                    v___x_258_ = v_reuseFailAlloc_260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_259_ = crate::leanh::lean_apply_2(
                    v_toPure_255_,
                    crate::leanh::lean_box(0),
                    v___x_258_,
                );
                return v___x_259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed(
    mut v_toApplicative_265_: *mut crate::leanh::LeanObject,
    mut v_countdown_266_: *mut crate::leanh::LeanObject,
    mut v___x_267_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(
        v_toApplicative_265_,
        v_countdown_266_,
        v___x_267_,
        v_____do__lift_268_,
    );
    crate::leanh::lean_dec(v___x_267_);
    return v_res_269_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg___lam__1(
    mut v_inst_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
    mut v_it_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_countdown_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: u8 = 0;
    v_countdown_273_ = crate::leanh::lean_ctor_get(v_it_272_, 0);
    crate::leanh::lean_inc(v_countdown_273_);
    v_inner_274_ = crate::leanh::lean_ctor_get(v_it_272_, 1);
    crate::leanh::lean_inc(v_inner_274_);
    crate::leanh::lean_dec_ref(v_it_272_);
    v___x_275_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_276_ = lean_nat_dec_eq(v_countdown_273_, v___x_275_);
    if v___x_276_ == 0 {
        let mut v_toApplicative_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_277_ = crate::leanh::lean_ctor_get(v_inst_270_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_277_);
        v_toBind_278_ = crate::leanh::lean_ctor_get(v_inst_270_, 1);
        crate::leanh::lean_inc(v_toBind_278_);
        crate::leanh::lean_dec_ref(v_inst_270_);
        v___f_279_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_279_, 0, v_toApplicative_277_);
        crate::leanh::lean_closure_set(v___f_279_, 1, v_countdown_273_);
        crate::leanh::lean_closure_set(v___f_279_, 2, v___x_275_);
        v___x_280_ = crate::leanh::lean_apply_1(v_inst_271_, v_inner_274_);
        v___x_281_ = crate::leanh::lean_apply_4(
            v_toBind_278_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_280_,
            v___f_279_,
        );
        return v___x_281_;
    } else {
        let mut v_toApplicative_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inner_274_);
        crate::leanh::lean_dec(v_countdown_273_);
        crate::leanh::lean_dec(v_inst_271_);
        v_toApplicative_282_ = crate::leanh::lean_ctor_get(v_inst_270_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_282_);
        crate::leanh::lean_dec_ref(v_inst_270_);
        v_toPure_283_ = crate::leanh::lean_ctor_get(v_toApplicative_282_, 1);
        crate::leanh::lean_inc(v_toPure_283_);
        crate::leanh::lean_dec_ref(v_toApplicative_282_);
        v___x_284_ = crate::leanh::lean_box(2);
        v___x_285_ =
            crate::leanh::lean_apply_2(v_toPure_283_, crate::leanh::lean_box(0), v___x_284_);
        return v___x_285_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator___redArg(
    mut v_inst_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_288_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_288_, 0, v_inst_286_);
    crate::leanh::lean_closure_set(v___f_288_, 1, v_inst_287_);
    return v___f_288_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIterator(
    mut v_00_u03b1_289_: *mut crate::leanh::LeanObject,
    mut v_m_290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_291_: *mut crate::leanh::LeanObject,
    mut v_inst_292_: *mut crate::leanh::LeanObject,
    mut v_inst_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_294_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_294_, 0, v_inst_292_);
    crate::leanh::lean_closure_set(v___f_294_, 1, v_inst_293_);
    return v___f_294_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(
    mut v_00_u03b1_295_: *mut crate::leanh::LeanObject,
    mut v_m_296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_297_: *mut crate::leanh::LeanObject,
    mut v_inst_298_: *mut crate::leanh::LeanObject,
    mut v_inst_299_: *mut crate::leanh::LeanObject,
    mut v_inst_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = crate::leanh::lean_box(0);
    return v___x_301_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___boxed(
    mut v_00_u03b1_302_: *mut crate::leanh::LeanObject,
    mut v_m_303_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_304_: *mut crate::leanh::LeanObject,
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_inst_306_: *mut crate::leanh::LeanObject,
    mut v_inst_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_308_ = l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(v_00_u03b1_302_, v_m_303_, v_00_u03b2_304_, v_inst_305_, v_inst_306_, v_inst_307_);
    crate::leanh::lean_dec(v_inst_306_);
    crate::leanh::lean_dec_ref(v_inst_305_);
    return v_res_308_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0(
    mut v_toPure_309_: *mut crate::leanh::LeanObject,
    mut v_recur_310_: *mut crate::leanh::LeanObject,
    mut v_it_311_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_312_) == 0 {
        let mut v_a_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_311_);
        crate::leanh::lean_dec(v_recur_310_);
        v_a_313_ = crate::leanh::lean_ctor_get(v_____do__lift_312_, 0);
        crate::leanh::lean_inc(v_a_313_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_312_, 1);
        v___x_314_ = crate::leanh::lean_apply_2(v_toPure_309_, crate::leanh::lean_box(0), v_a_313_);
        return v___x_314_;
    } else {
        let mut v_a_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_309_);
        v_a_315_ = crate::leanh::lean_ctor_get(v_____do__lift_312_, 0);
        crate::leanh::lean_inc(v_a_315_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_312_, 1);
        v___x_316_ = crate::leanh::lean_apply_4(
            v_recur_310_,
            v_it_311_,
            v_a_315_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_316_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1(
    mut v_toPure_317_: *mut crate::leanh::LeanObject,
    mut v_recur_318_: *mut crate::leanh::LeanObject,
    mut v___y_319_: *mut crate::leanh::LeanObject,
    mut v_acc_320_: *mut crate::leanh::LeanObject,
    mut v_toBind_321_: *mut crate::leanh::LeanObject,
    mut v_s_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_322_) {
        0 => {
            let mut v_it_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_323_ = crate::leanh::lean_ctor_get(v_s_322_, 0);
            crate::leanh::lean_inc(v_it_323_);
            v_out_324_ = crate::leanh::lean_ctor_get(v_s_322_, 1);
            crate::leanh::lean_inc(v_out_324_);
            crate::leanh::lean_dec_ref_known(v_s_322_, 2);
            v___f_325_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_325_, 0, v_toPure_317_);
            crate::leanh::lean_closure_set(v___f_325_, 1, v_recur_318_);
            crate::leanh::lean_closure_set(v___f_325_, 2, v_it_323_);
            v___x_326_ = crate::leanh::lean_apply_3(
                v___y_319_,
                v_out_324_,
                crate::leanh::lean_box(0),
                v_acc_320_,
            );
            v___x_327_ = crate::leanh::lean_apply_4(
                v_toBind_321_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_326_,
                v___f_325_,
            );
            return v___x_327_;
        }
        1 => {
            let mut v_it_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_321_);
            crate::leanh::lean_dec(v___y_319_);
            crate::leanh::lean_dec(v_toPure_317_);
            v_it_328_ = crate::leanh::lean_ctor_get(v_s_322_, 0);
            crate::leanh::lean_inc(v_it_328_);
            crate::leanh::lean_dec_ref_known(v_s_322_, 1);
            v___x_329_ = crate::leanh::lean_apply_4(
                v_recur_318_,
                v_it_328_,
                v_acc_320_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_329_;
        }
        _ => {
            let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_321_);
            crate::leanh::lean_dec(v___y_319_);
            crate::leanh::lean_dec(v_recur_318_);
            v___x_330_ =
                crate::leanh::lean_apply_2(v_toPure_317_, crate::leanh::lean_box(0), v_acc_320_);
            return v___x_330_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3(
    mut v_toPure_331_: *mut crate::leanh::LeanObject,
    mut v___y_332_: *mut crate::leanh::LeanObject,
    mut v_toBind_333_: *mut crate::leanh::LeanObject,
    mut v_inst_334_: *mut crate::leanh::LeanObject,
    mut v_inst_335_: *mut crate::leanh::LeanObject,
    mut v_lift_336_: *mut crate::leanh::LeanObject,
    mut v_it_337_: *mut crate::leanh::LeanObject,
    mut v_acc_338_: *mut crate::leanh::LeanObject,
    mut v_hP_339_: *mut crate::leanh::LeanObject,
    mut v_recur_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_countdown_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: u8 = 0;
    v_countdown_341_ = crate::leanh::lean_ctor_get(v_it_337_, 0);
    crate::leanh::lean_inc(v_countdown_341_);
    v_inner_342_ = crate::leanh::lean_ctor_get(v_it_337_, 1);
    crate::leanh::lean_inc(v_inner_342_);
    crate::leanh::lean_dec_ref(v_it_337_);
    v___f_343_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_343_, 0, v_toPure_331_);
    crate::leanh::lean_closure_set(v___f_343_, 1, v_recur_340_);
    crate::leanh::lean_closure_set(v___f_343_, 2, v___y_332_);
    crate::leanh::lean_closure_set(v___f_343_, 3, v_acc_338_);
    crate::leanh::lean_closure_set(v___f_343_, 4, v_toBind_333_);
    v___x_344_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_345_ = lean_nat_dec_eq(v_countdown_341_, v___x_344_);
    if v___x_345_ == 0 {
        let mut v_toApplicative_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_346_ = crate::leanh::lean_ctor_get(v_inst_334_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_346_);
        v_toBind_347_ = crate::leanh::lean_ctor_get(v_inst_334_, 1);
        crate::leanh::lean_inc(v_toBind_347_);
        crate::leanh::lean_dec_ref(v_inst_334_);
        v___f_348_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_348_, 0, v_toApplicative_346_);
        crate::leanh::lean_closure_set(v___f_348_, 1, v_countdown_341_);
        crate::leanh::lean_closure_set(v___f_348_, 2, v___x_344_);
        v___x_349_ = crate::leanh::lean_apply_1(v_inst_335_, v_inner_342_);
        v___x_350_ = crate::leanh::lean_apply_4(
            v_toBind_347_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_349_,
            v___f_348_,
        );
        v___x_351_ = crate::leanh::lean_apply_4(
            v_lift_336_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_343_,
            v___x_350_,
        );
        return v___x_351_;
    } else {
        let mut v_toApplicative_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inner_342_);
        crate::leanh::lean_dec(v_countdown_341_);
        crate::leanh::lean_dec(v_inst_335_);
        v_toApplicative_352_ = crate::leanh::lean_ctor_get(v_inst_334_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_352_);
        crate::leanh::lean_dec_ref(v_inst_334_);
        v_toPure_353_ = crate::leanh::lean_ctor_get(v_toApplicative_352_, 1);
        crate::leanh::lean_inc(v_toPure_353_);
        crate::leanh::lean_dec_ref(v_toApplicative_352_);
        v___x_354_ = crate::leanh::lean_box(2);
        v___x_355_ =
            crate::leanh::lean_apply_2(v_toPure_353_, crate::leanh::lean_box(0), v___x_354_);
        v___x_356_ = crate::leanh::lean_apply_4(
            v_lift_336_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_343_,
            v___x_355_,
        );
        return v___x_356_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2(
    mut v_inst_357_: *mut crate::leanh::LeanObject,
    mut v_inst_358_: *mut crate::leanh::LeanObject,
    mut v_inst_359_: *mut crate::leanh::LeanObject,
    mut v_lift_360_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_361_: *mut crate::leanh::LeanObject,
    mut v_Pl_362_: *mut crate::leanh::LeanObject,
    mut v_it_363_: *mut crate::leanh::LeanObject,
    mut v_init_364_: *mut crate::leanh::LeanObject,
    mut v___y_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_366_ = crate::leanh::lean_ctor_get(v_inst_357_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_366_);
    v_toBind_367_ = crate::leanh::lean_ctor_get(v_inst_357_, 1);
    crate::leanh::lean_inc(v_toBind_367_);
    crate::leanh::lean_dec_ref(v_inst_357_);
    v_toPure_368_ = crate::leanh::lean_ctor_get(v_toApplicative_366_, 1);
    crate::leanh::lean_inc(v_toPure_368_);
    crate::leanh::lean_dec_ref(v_toApplicative_366_);
    v___f_369_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___f_369_, 0, v_toPure_368_);
    crate::leanh::lean_closure_set(v___f_369_, 1, v___y_365_);
    crate::leanh::lean_closure_set(v___f_369_, 2, v_toBind_367_);
    crate::leanh::lean_closure_set(v___f_369_, 3, v_inst_358_);
    crate::leanh::lean_closure_set(v___f_369_, 4, v_inst_359_);
    crate::leanh::lean_closure_set(v___f_369_, 5, v_lift_360_);
    v___x_370_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_369_,
        v_it_363_,
        v_init_364_,
        crate::leanh::lean_box(0),
    );
    return v___x_370_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop___redArg(
    mut v_inst_371_: *mut crate::leanh::LeanObject,
    mut v_inst_372_: *mut crate::leanh::LeanObject,
    mut v_inst_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_374_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_374_, 0, v_inst_372_);
    crate::leanh::lean_closure_set(v___f_374_, 1, v_inst_371_);
    crate::leanh::lean_closure_set(v___f_374_, 2, v_inst_373_);
    return v___f_374_;
}
pub unsafe fn l_Std_Iterators_Types_Take_instIteratorLoop(
    mut v_00_u03b1_375_: *mut crate::leanh::LeanObject,
    mut v_m_376_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_377_: *mut crate::leanh::LeanObject,
    mut v_n_378_: *mut crate::leanh::LeanObject,
    mut v_inst_379_: *mut crate::leanh::LeanObject,
    mut v_inst_380_: *mut crate::leanh::LeanObject,
    mut v_inst_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_382_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_382_, 0, v_inst_380_);
    crate::leanh::lean_closure_set(v___f_382_, 1, v_inst_379_);
    crate::leanh::lean_closure_set(v___f_382_, 2, v_inst_381_);
    return v___f_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
}
