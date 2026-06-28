// Lean compiler output
// Module: Init.Data.List.MinMaxIdx
// Imports: Init.Data.List.MinMaxOn Init.Data.List.Nat.TakeDrop Init.ByCases Init.Data.Bool Init.Data.List.Sublist Init.Data.Nat.Lemmas Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::MinMaxOn::{
    initialize_Init_Data_List_MinMaxOn, runtime_initialize_Init_Data_List_MinMaxOn,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_List_get___redArg, l_List_lengthTR___redArg};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
    mut v_inst_205_: *mut LeanObject,
    mut v_f_206_: *mut LeanObject,
    mut v_x_207_: *mut LeanObject,
    mut v_i_208_: *mut LeanObject,
    mut v_j_209_: *mut LeanObject,
    mut v_xs_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: u8 = 0;
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_xs_210_) == 0 {
                    lean_dec(v_j_209_);
                    lean_dec(v_x_207_);
                    lean_dec(v_f_206_);
                    lean_dec_ref(v_inst_205_);
                    return v_i_208_;
                } else {
                    v_head_211_ = lean_ctor_get(v_xs_210_, 0);
                    lean_inc_n(v_head_211_, 2);
                    v_tail_212_ = lean_ctor_get(v_xs_210_, 1);
                    lean_inc(v_tail_212_);
                    lean_dec_ref_known(v_xs_210_, 2);
                    lean_inc_n(v_f_206_, 2);
                    lean_inc(v_x_207_);
                    v___x_213_ = lean_apply_1(v_f_206_, v_x_207_);
                    v___x_214_ = lean_apply_1(v_f_206_, v_head_211_);
                    lean_inc_ref(v_inst_205_);
                    v___x_215_ = lean_apply_2(v_inst_205_, v___x_213_, v___x_214_);
                    v___x_216_ = (lean_unbox(v___x_215_) as u8);
                    if v___x_216_ == 0 {
                        lean_dec(v_i_208_);
                        lean_dec(v_x_207_);
                        v___x_217_ = lean_unsigned_to_nat(1);
                        v___x_218_ = lean_nat_add(v_j_209_, v___x_217_);
                        v_x_207_ = v_head_211_;
                        v_i_208_ = v_j_209_;
                        v_j_209_ = v___x_218_;
                        v_xs_210_ = v_tail_212_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_head_211_);
                        v___x_220_ = lean_unsigned_to_nat(1);
                        v___x_221_ = lean_nat_add(v_j_209_, v___x_220_);
                        lean_dec(v_j_209_);
                        v_j_209_ = v___x_221_;
                        v_xs_210_ = v_tail_212_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go(
    mut v_00_u03b2_223_: *mut LeanObject,
    mut v_00_u03b1_224_: *mut LeanObject,
    mut v_inst_225_: *mut LeanObject,
    mut v_inst_226_: *mut LeanObject,
    mut v_f_227_: *mut LeanObject,
    mut v_x_228_: *mut LeanObject,
    mut v_i_229_: *mut LeanObject,
    mut v_j_230_: *mut LeanObject,
    mut v_xs_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v___x_232_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
        v_inst_226_,
        v_f_227_,
        v_x_228_,
        v_i_229_,
        v_j_230_,
        v_xs_231_,
    );
    return v___x_232_;
}
pub unsafe fn l_List_minIdxOn___redArg(
    mut v_inst_233_: *mut LeanObject,
    mut v_f_234_: *mut LeanObject,
    mut v_xs_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    v_head_236_ = lean_ctor_get(v_xs_235_, 0);
    lean_inc(v_head_236_);
    v_tail_237_ = lean_ctor_get(v_xs_235_, 1);
    lean_inc(v_tail_237_);
    lean_dec(v_xs_235_);
    v___x_238_ = lean_unsigned_to_nat(0);
    v___x_239_ = lean_unsigned_to_nat(1);
    v___x_240_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
        v_inst_233_,
        v_f_234_,
        v_head_236_,
        v___x_238_,
        v___x_239_,
        v_tail_237_,
    );
    return v___x_240_;
}
pub unsafe fn l_List_minIdxOn(
    mut v_00_u03b2_241_: *mut LeanObject,
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_inst_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_f_245_: *mut LeanObject,
    mut v_xs_246_: *mut LeanObject,
    mut v_h_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v_head_248_ = lean_ctor_get(v_xs_246_, 0);
    lean_inc(v_head_248_);
    v_tail_249_ = lean_ctor_get(v_xs_246_, 1);
    lean_inc(v_tail_249_);
    lean_dec(v_xs_246_);
    v___x_250_ = lean_unsigned_to_nat(0);
    v___x_251_ = lean_unsigned_to_nat(1);
    v___x_252_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
        v_inst_244_,
        v_f_245_,
        v_head_248_,
        v___x_250_,
        v___x_251_,
        v_tail_249_,
    );
    return v___x_252_;
}
pub unsafe fn l_List_minIdxOn_x3f___redArg(
    mut v_inst_253_: *mut LeanObject,
    mut v_f_254_: *mut LeanObject,
    mut v_xs_255_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_255_) == 0 {
        let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_254_);
        lean_dec_ref(v_inst_253_);
        v___x_256_ = lean_box(0);
        return v___x_256_;
    } else {
        let mut v_head_257_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        v_head_257_ = lean_ctor_get(v_xs_255_, 0);
        lean_inc(v_head_257_);
        v_tail_258_ = lean_ctor_get(v_xs_255_, 1);
        lean_inc(v_tail_258_);
        lean_dec_ref_known(v_xs_255_, 2);
        v___x_259_ = lean_unsigned_to_nat(0);
        v___x_260_ = lean_unsigned_to_nat(1);
        v___x_261_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v_inst_253_,
            v_f_254_,
            v_head_257_,
            v___x_259_,
            v___x_260_,
            v_tail_258_,
        );
        v___x_262_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_262_, 0, v___x_261_);
        return v___x_262_;
    }
}
pub unsafe fn l_List_minIdxOn_x3f(
    mut v_00_u03b2_263_: *mut LeanObject,
    mut v_00_u03b1_264_: *mut LeanObject,
    mut v_inst_265_: *mut LeanObject,
    mut v_inst_266_: *mut LeanObject,
    mut v_f_267_: *mut LeanObject,
    mut v_xs_268_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_268_) == 0 {
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_267_);
        lean_dec_ref(v_inst_266_);
        v___x_269_ = lean_box(0);
        return v___x_269_;
    } else {
        let mut v_head_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        v_head_270_ = lean_ctor_get(v_xs_268_, 0);
        lean_inc(v_head_270_);
        v_tail_271_ = lean_ctor_get(v_xs_268_, 1);
        lean_inc(v_tail_271_);
        lean_dec_ref_known(v_xs_268_, 2);
        v___x_272_ = lean_unsigned_to_nat(0);
        v___x_273_ = lean_unsigned_to_nat(1);
        v___x_274_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v_inst_266_,
            v_f_267_,
            v_head_270_,
            v___x_272_,
            v___x_273_,
            v_tail_271_,
        );
        v___x_275_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_275_, 0, v___x_274_);
        return v___x_275_;
    }
}
pub unsafe fn l_List_maxIdxOn___redArg___lam__0(
    mut v_inst_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
    mut v_b_278_: *mut LeanObject,
) -> u8 {
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    v___x_279_ = lean_apply_2(v_inst_276_, v_b_278_, v_a_277_);
    v___x_280_ = (lean_unbox(v___x_279_) as u8);
    return v___x_280_;
}
pub unsafe fn l_List_maxIdxOn___redArg___lam__0___boxed(
    mut v_inst_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v_b_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_284_: u8 = 0;
    let mut v_r_285_: *mut LeanObject = core::ptr::null_mut();
    v_res_284_ = l_List_maxIdxOn___redArg___lam__0(v_inst_281_, v_a_282_, v_b_283_);
    v_r_285_ = lean_box((v_res_284_) as usize);
    return v_r_285_;
}
pub unsafe fn l_List_maxIdxOn___redArg(
    mut v_inst_286_: *mut LeanObject,
    mut v_f_287_: *mut LeanObject,
    mut v_xs_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v_head_289_ = lean_ctor_get(v_xs_288_, 0);
    lean_inc(v_head_289_);
    v_tail_290_ = lean_ctor_get(v_xs_288_, 1);
    lean_inc(v_tail_290_);
    lean_dec(v_xs_288_);
    v___f_291_ = lean_alloc_closure(
        l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_291_, 0, v_inst_286_);
    v___x_292_ = lean_unsigned_to_nat(0);
    v___x_293_ = lean_unsigned_to_nat(1);
    v___x_294_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
        v___f_291_,
        v_f_287_,
        v_head_289_,
        v___x_292_,
        v___x_293_,
        v_tail_290_,
    );
    return v___x_294_;
}
pub unsafe fn l_List_maxIdxOn(
    mut v_00_u03b2_295_: *mut LeanObject,
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_inst_297_: *mut LeanObject,
    mut v_inst_298_: *mut LeanObject,
    mut v_f_299_: *mut LeanObject,
    mut v_xs_300_: *mut LeanObject,
    mut v_h_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v_head_302_ = lean_ctor_get(v_xs_300_, 0);
    lean_inc(v_head_302_);
    v_tail_303_ = lean_ctor_get(v_xs_300_, 1);
    lean_inc(v_tail_303_);
    lean_dec(v_xs_300_);
    v___f_304_ = lean_alloc_closure(
        l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_304_, 0, v_inst_298_);
    v___x_305_ = lean_unsigned_to_nat(0);
    v___x_306_ = lean_unsigned_to_nat(1);
    v___x_307_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
        v___f_304_,
        v_f_299_,
        v_head_302_,
        v___x_305_,
        v___x_306_,
        v_tail_303_,
    );
    return v___x_307_;
}
pub unsafe fn l_List_maxIdxOn_x3f___redArg(
    mut v_inst_308_: *mut LeanObject,
    mut v_f_309_: *mut LeanObject,
    mut v_xs_310_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_310_) == 0 {
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_309_);
        lean_dec_ref(v_inst_308_);
        v___x_311_ = lean_box(0);
        return v___x_311_;
    } else {
        let mut v_head_312_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        v_head_312_ = lean_ctor_get(v_xs_310_, 0);
        lean_inc(v_head_312_);
        v_tail_313_ = lean_ctor_get(v_xs_310_, 1);
        lean_inc(v_tail_313_);
        lean_dec_ref_known(v_xs_310_, 2);
        v___f_314_ = lean_alloc_closure(
            l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_314_, 0, v_inst_308_);
        v___x_315_ = lean_unsigned_to_nat(0);
        v___x_316_ = lean_unsigned_to_nat(1);
        v___x_317_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v___f_314_,
            v_f_309_,
            v_head_312_,
            v___x_315_,
            v___x_316_,
            v_tail_313_,
        );
        v___x_318_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_318_, 0, v___x_317_);
        return v___x_318_;
    }
}
pub unsafe fn l_List_maxIdxOn_x3f(
    mut v_00_u03b2_319_: *mut LeanObject,
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_inst_321_: *mut LeanObject,
    mut v_inst_322_: *mut LeanObject,
    mut v_f_323_: *mut LeanObject,
    mut v_xs_324_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_324_) == 0 {
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_323_);
        lean_dec_ref(v_inst_322_);
        v___x_325_ = lean_box(0);
        return v___x_325_;
    } else {
        let mut v_head_326_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
        v_head_326_ = lean_ctor_get(v_xs_324_, 0);
        lean_inc(v_head_326_);
        v_tail_327_ = lean_ctor_get(v_xs_324_, 1);
        lean_inc(v_tail_327_);
        lean_dec_ref_known(v_xs_324_, 2);
        v___f_328_ = lean_alloc_closure(
            l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_328_, 0, v_inst_322_);
        v___x_329_ = lean_unsigned_to_nat(0);
        v___x_330_ = lean_unsigned_to_nat(1);
        v___x_331_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v___f_328_,
            v_f_323_,
            v_head_326_,
            v___x_329_,
            v___x_330_,
            v_tail_327_,
        );
        v___x_332_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_332_, 0, v___x_331_);
        return v___x_332_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter___redArg(
    mut v_xs_333_: *mut LeanObject,
    mut v_h__1_334_: *mut LeanObject,
    mut v_h__2_335_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_333_) == 0 {
        let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_335_);
        v___x_336_ = lean_box(0);
        v___x_337_ = lean_apply_1(v_h__1_334_, v___x_336_);
        return v___x_337_;
    } else {
        let mut v_head_338_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_334_);
        v_head_338_ = lean_ctor_get(v_xs_333_, 0);
        lean_inc(v_head_338_);
        v_tail_339_ = lean_ctor_get(v_xs_333_, 1);
        lean_inc(v_tail_339_);
        lean_dec_ref_known(v_xs_333_, 2);
        v___x_340_ = lean_apply_2(v_h__2_335_, v_head_338_, v_tail_339_);
        return v___x_340_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter(
    mut v_00_u03b1_341_: *mut LeanObject,
    mut v_motive_342_: *mut LeanObject,
    mut v_xs_343_: *mut LeanObject,
    mut v_h__1_344_: *mut LeanObject,
    mut v_h__2_345_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_343_) == 0 {
        let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_345_);
        v___x_346_ = lean_box(0);
        v___x_347_ = lean_apply_1(v_h__1_344_, v___x_346_);
        return v___x_347_;
    } else {
        let mut v_head_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_344_);
        v_head_348_ = lean_ctor_get(v_xs_343_, 0);
        lean_inc(v_head_348_);
        v_tail_349_ = lean_ctor_get(v_xs_343_, 1);
        lean_inc(v_tail_349_);
        lean_dec_ref_known(v_xs_343_, 2);
        v___x_350_ = lean_apply_2(v_h__2_345_, v_head_348_, v_tail_349_);
        return v___x_350_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter___redArg(
    mut v_xs_351_: *mut LeanObject,
    mut v_h__1_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v_head_353_ = lean_ctor_get(v_xs_351_, 0);
    lean_inc(v_head_353_);
    v_tail_354_ = lean_ctor_get(v_xs_351_, 1);
    lean_inc(v_tail_354_);
    lean_dec(v_xs_351_);
    v___x_355_ = lean_apply_3(v_h__1_352_, v_head_353_, v_tail_354_, lean_box(0));
    return v___x_355_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter(
    mut v_00_u03b1_356_: *mut LeanObject,
    mut v_motive_357_: *mut LeanObject,
    mut v_xs_358_: *mut LeanObject,
    mut v_h_359_: *mut LeanObject,
    mut v_h__1_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    v_head_361_ = lean_ctor_get(v_xs_358_, 0);
    lean_inc(v_head_361_);
    v_tail_362_ = lean_ctor_get(v_xs_358_, 1);
    lean_inc(v_tail_362_);
    lean_dec(v_xs_358_);
    v___x_363_ = lean_apply_3(v_h__1_360_, v_head_361_, v_tail_362_, lean_box(0));
    return v___x_363_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(
    mut v_inst_364_: *mut LeanObject,
    mut v_f_365_: *mut LeanObject,
    mut v_xs_366_: *mut LeanObject,
    mut v_ys_367_: *mut LeanObject,
    mut v_i_368_: *mut LeanObject,
    mut v_j_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: u8 = 0;
    lean_inc(v_i_368_);
    v___x_370_ = l_List_get___redArg(v_xs_366_, v_i_368_);
    lean_inc(v_f_365_);
    v___x_371_ = lean_apply_1(v_f_365_, v___x_370_);
    lean_inc(v_j_369_);
    v___x_372_ = l_List_get___redArg(v_ys_367_, v_j_369_);
    v___x_373_ = lean_apply_1(v_f_365_, v___x_372_);
    v___x_374_ = lean_apply_2(v_inst_364_, v___x_371_, v___x_373_);
    v___x_375_ = (lean_unbox(v___x_374_) as u8);
    if v___x_375_ == 0 {
        let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_368_);
        v___x_376_ = l_List_lengthTR___redArg(v_xs_366_);
        v___x_377_ = lean_nat_add(v___x_376_, v_j_369_);
        lean_dec(v_j_369_);
        lean_dec(v___x_376_);
        return v___x_377_;
    } else {
        lean_dec(v_j_369_);
        return v_i_368_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(
    mut v_inst_378_: *mut LeanObject,
    mut v_f_379_: *mut LeanObject,
    mut v_xs_380_: *mut LeanObject,
    mut v_ys_381_: *mut LeanObject,
    mut v_i_382_: *mut LeanObject,
    mut v_j_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
    v_res_384_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(
        v_inst_378_,
        v_f_379_,
        v_xs_380_,
        v_ys_381_,
        v_i_382_,
        v_j_383_,
    );
    lean_dec(v_ys_381_);
    lean_dec(v_xs_380_);
    return v_res_384_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(
    mut v_00_u03b2_385_: *mut LeanObject,
    mut v_00_u03b1_386_: *mut LeanObject,
    mut v_inst_387_: *mut LeanObject,
    mut v_inst_388_: *mut LeanObject,
    mut v_f_389_: *mut LeanObject,
    mut v_xs_390_: *mut LeanObject,
    mut v_ys_391_: *mut LeanObject,
    mut v_i_392_: *mut LeanObject,
    mut v_j_393_: *mut LeanObject,
    mut v_hi_394_: *mut LeanObject,
    mut v_hj_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    v___x_396_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(
        v_inst_388_,
        v_f_389_,
        v_xs_390_,
        v_ys_391_,
        v_i_392_,
        v_j_393_,
    );
    return v___x_396_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___boxed(
    mut v_00_u03b2_397_: *mut LeanObject,
    mut v_00_u03b1_398_: *mut LeanObject,
    mut v_inst_399_: *mut LeanObject,
    mut v_inst_400_: *mut LeanObject,
    mut v_f_401_: *mut LeanObject,
    mut v_xs_402_: *mut LeanObject,
    mut v_ys_403_: *mut LeanObject,
    mut v_i_404_: *mut LeanObject,
    mut v_j_405_: *mut LeanObject,
    mut v_hi_406_: *mut LeanObject,
    mut v_hj_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_408_: *mut LeanObject = core::ptr::null_mut();
    v_res_408_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(
        v_00_u03b2_397_,
        v_00_u03b1_398_,
        v_inst_399_,
        v_inst_400_,
        v_f_401_,
        v_xs_402_,
        v_ys_403_,
        v_i_404_,
        v_j_405_,
        v_hi_406_,
        v_hj_407_,
    );
    lean_dec(v_ys_403_);
    lean_dec(v_xs_402_);
    return v_res_408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_MinMaxIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_MinMaxOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_List_MinMaxIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_MinMaxIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_MinMaxOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMaxIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_MinMaxIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_MinMaxIdx(builtin);
}
