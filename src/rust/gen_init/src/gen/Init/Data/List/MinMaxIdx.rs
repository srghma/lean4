// Lean compiler output
// Module: Init.Data.List.MinMaxIdx
// Imports: Init.Data.List.MinMaxOn Init.Data.List.Nat.TakeDrop Init.ByCases Init.Data.Bool Init.Data.List.Sublist Init.Data.Nat.Lemmas Init.Omega
use crate::ffi::lean_nat_add;
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
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
    mut v_inst_205_: *mut leanh::LeanObject,
    mut v_f_206_: *mut leanh::LeanObject,
    mut v_x_207_: *mut leanh::LeanObject,
    mut v_i_208_: *mut leanh::LeanObject,
    mut v_j_209_: *mut leanh::LeanObject,
    mut v_xs_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: u8 = 0;
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_xs_210_) == 0 {
                    leanh::lean_dec(v_j_209_);
                    leanh::lean_dec(v_x_207_);
                    leanh::lean_dec(v_f_206_);
                    leanh::lean_dec_ref(v_inst_205_);
                    return v_i_208_;
                } else {
                    v_head_211_ = leanh::lean_ctor_get(v_xs_210_, 0);
                    leanh::lean_inc_n(v_head_211_, 2);
                    v_tail_212_ = leanh::lean_ctor_get(v_xs_210_, 1);
                    leanh::lean_inc(v_tail_212_);
                    leanh::lean_dec_ref_known(v_xs_210_, 2);
                    leanh::lean_inc_n(v_f_206_, 2);
                    leanh::lean_inc(v_x_207_);
                    v___x_213_ = leanh::lean_apply_1(v_f_206_, v_x_207_);
                    v___x_214_ = leanh::lean_apply_1(v_f_206_, v_head_211_);
                    leanh::lean_inc_ref(v_inst_205_);
                    v___x_215_ = leanh::lean_apply_2(v_inst_205_, v___x_213_, v___x_214_);
                    v___x_216_ = (leanh::lean_unbox(v___x_215_) as u8);
                    if v___x_216_ == 0 {
                        leanh::lean_dec(v_i_208_);
                        leanh::lean_dec(v_x_207_);
                        v___x_217_ = leanh::lean_unsigned_to_nat(1);
                        v___x_218_ = lean_nat_add(v_j_209_, v___x_217_);
                        v_x_207_ = v_head_211_;
                        v_i_208_ = v_j_209_;
                        v_j_209_ = v___x_218_;
                        v_xs_210_ = v_tail_212_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_211_);
                        v___x_220_ = leanh::lean_unsigned_to_nat(1);
                        v___x_221_ = lean_nat_add(v_j_209_, v___x_220_);
                        leanh::lean_dec(v_j_209_);
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
    mut v_00_u03b2_223_: *mut leanh::LeanObject,
    mut v_00_u03b1_224_: *mut leanh::LeanObject,
    mut v_inst_225_: *mut leanh::LeanObject,
    mut v_inst_226_: *mut leanh::LeanObject,
    mut v_f_227_: *mut leanh::LeanObject,
    mut v_x_228_: *mut leanh::LeanObject,
    mut v_i_229_: *mut leanh::LeanObject,
    mut v_j_230_: *mut leanh::LeanObject,
    mut v_xs_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_233_: *mut leanh::LeanObject,
    mut v_f_234_: *mut leanh::LeanObject,
    mut v_xs_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_236_ = leanh::lean_ctor_get(v_xs_235_, 0);
    leanh::lean_inc(v_head_236_);
    v_tail_237_ = leanh::lean_ctor_get(v_xs_235_, 1);
    leanh::lean_inc(v_tail_237_);
    leanh::lean_dec(v_xs_235_);
    v___x_238_ = leanh::lean_unsigned_to_nat(0);
    v___x_239_ = leanh::lean_unsigned_to_nat(1);
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
    mut v_00_u03b2_241_: *mut leanh::LeanObject,
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_inst_243_: *mut leanh::LeanObject,
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_f_245_: *mut leanh::LeanObject,
    mut v_xs_246_: *mut leanh::LeanObject,
    mut v_h_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_248_ = leanh::lean_ctor_get(v_xs_246_, 0);
    leanh::lean_inc(v_head_248_);
    v_tail_249_ = leanh::lean_ctor_get(v_xs_246_, 1);
    leanh::lean_inc(v_tail_249_);
    leanh::lean_dec(v_xs_246_);
    v___x_250_ = leanh::lean_unsigned_to_nat(0);
    v___x_251_ = leanh::lean_unsigned_to_nat(1);
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
    mut v_inst_253_: *mut leanh::LeanObject,
    mut v_f_254_: *mut leanh::LeanObject,
    mut v_xs_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_255_) == 0 {
        let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_254_);
        leanh::lean_dec_ref(v_inst_253_);
        v___x_256_ = leanh::lean_box(0);
        return v___x_256_;
    } else {
        let mut v_head_257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_257_ = leanh::lean_ctor_get(v_xs_255_, 0);
        leanh::lean_inc(v_head_257_);
        v_tail_258_ = leanh::lean_ctor_get(v_xs_255_, 1);
        leanh::lean_inc(v_tail_258_);
        leanh::lean_dec_ref_known(v_xs_255_, 2);
        v___x_259_ = leanh::lean_unsigned_to_nat(0);
        v___x_260_ = leanh::lean_unsigned_to_nat(1);
        v___x_261_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v_inst_253_,
            v_f_254_,
            v_head_257_,
            v___x_259_,
            v___x_260_,
            v_tail_258_,
        );
        v___x_262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_262_, 0, v___x_261_);
        return v___x_262_;
    }
}
pub unsafe fn l_List_minIdxOn_x3f(
    mut v_00_u03b2_263_: *mut leanh::LeanObject,
    mut v_00_u03b1_264_: *mut leanh::LeanObject,
    mut v_inst_265_: *mut leanh::LeanObject,
    mut v_inst_266_: *mut leanh::LeanObject,
    mut v_f_267_: *mut leanh::LeanObject,
    mut v_xs_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_268_) == 0 {
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_267_);
        leanh::lean_dec_ref(v_inst_266_);
        v___x_269_ = leanh::lean_box(0);
        return v___x_269_;
    } else {
        let mut v_head_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_270_ = leanh::lean_ctor_get(v_xs_268_, 0);
        leanh::lean_inc(v_head_270_);
        v_tail_271_ = leanh::lean_ctor_get(v_xs_268_, 1);
        leanh::lean_inc(v_tail_271_);
        leanh::lean_dec_ref_known(v_xs_268_, 2);
        v___x_272_ = leanh::lean_unsigned_to_nat(0);
        v___x_273_ = leanh::lean_unsigned_to_nat(1);
        v___x_274_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v_inst_266_,
            v_f_267_,
            v_head_270_,
            v___x_272_,
            v___x_273_,
            v_tail_271_,
        );
        v___x_275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_275_, 0, v___x_274_);
        return v___x_275_;
    }
}
pub unsafe fn l_List_maxIdxOn___redArg___lam__0(
    mut v_inst_276_: *mut leanh::LeanObject,
    mut v_a_277_: *mut leanh::LeanObject,
    mut v_b_278_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    v___x_279_ = leanh::lean_apply_2(v_inst_276_, v_b_278_, v_a_277_);
    v___x_280_ = (leanh::lean_unbox(v___x_279_) as u8);
    return v___x_280_;
}
pub unsafe fn l_List_maxIdxOn___redArg___lam__0___boxed(
    mut v_inst_281_: *mut leanh::LeanObject,
    mut v_a_282_: *mut leanh::LeanObject,
    mut v_b_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_284_: u8 = 0;
    let mut v_r_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_284_ = l_List_maxIdxOn___redArg___lam__0(v_inst_281_, v_a_282_, v_b_283_);
    v_r_285_ = leanh::lean_box((v_res_284_) as usize);
    return v_r_285_;
}
pub unsafe fn l_List_maxIdxOn___redArg(
    mut v_inst_286_: *mut leanh::LeanObject,
    mut v_f_287_: *mut leanh::LeanObject,
    mut v_xs_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_289_ = leanh::lean_ctor_get(v_xs_288_, 0);
    leanh::lean_inc(v_head_289_);
    v_tail_290_ = leanh::lean_ctor_get(v_xs_288_, 1);
    leanh::lean_inc(v_tail_290_);
    leanh::lean_dec(v_xs_288_);
    v___f_291_ = leanh::lean_alloc_closure(
        l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_291_, 0, v_inst_286_);
    v___x_292_ = leanh::lean_unsigned_to_nat(0);
    v___x_293_ = leanh::lean_unsigned_to_nat(1);
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
    mut v_00_u03b2_295_: *mut leanh::LeanObject,
    mut v_00_u03b1_296_: *mut leanh::LeanObject,
    mut v_inst_297_: *mut leanh::LeanObject,
    mut v_inst_298_: *mut leanh::LeanObject,
    mut v_f_299_: *mut leanh::LeanObject,
    mut v_xs_300_: *mut leanh::LeanObject,
    mut v_h_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_302_ = leanh::lean_ctor_get(v_xs_300_, 0);
    leanh::lean_inc(v_head_302_);
    v_tail_303_ = leanh::lean_ctor_get(v_xs_300_, 1);
    leanh::lean_inc(v_tail_303_);
    leanh::lean_dec(v_xs_300_);
    v___f_304_ = leanh::lean_alloc_closure(
        l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_304_, 0, v_inst_298_);
    v___x_305_ = leanh::lean_unsigned_to_nat(0);
    v___x_306_ = leanh::lean_unsigned_to_nat(1);
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
    mut v_inst_308_: *mut leanh::LeanObject,
    mut v_f_309_: *mut leanh::LeanObject,
    mut v_xs_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_310_) == 0 {
        let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_309_);
        leanh::lean_dec_ref(v_inst_308_);
        v___x_311_ = leanh::lean_box(0);
        return v___x_311_;
    } else {
        let mut v_head_312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_312_ = leanh::lean_ctor_get(v_xs_310_, 0);
        leanh::lean_inc(v_head_312_);
        v_tail_313_ = leanh::lean_ctor_get(v_xs_310_, 1);
        leanh::lean_inc(v_tail_313_);
        leanh::lean_dec_ref_known(v_xs_310_, 2);
        v___f_314_ = leanh::lean_alloc_closure(
            l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_314_, 0, v_inst_308_);
        v___x_315_ = leanh::lean_unsigned_to_nat(0);
        v___x_316_ = leanh::lean_unsigned_to_nat(1);
        v___x_317_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v___f_314_,
            v_f_309_,
            v_head_312_,
            v___x_315_,
            v___x_316_,
            v_tail_313_,
        );
        v___x_318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
        return v___x_318_;
    }
}
pub unsafe fn l_List_maxIdxOn_x3f(
    mut v_00_u03b2_319_: *mut leanh::LeanObject,
    mut v_00_u03b1_320_: *mut leanh::LeanObject,
    mut v_inst_321_: *mut leanh::LeanObject,
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_f_323_: *mut leanh::LeanObject,
    mut v_xs_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_324_) == 0 {
        let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_323_);
        leanh::lean_dec_ref(v_inst_322_);
        v___x_325_ = leanh::lean_box(0);
        return v___x_325_;
    } else {
        let mut v_head_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_326_ = leanh::lean_ctor_get(v_xs_324_, 0);
        leanh::lean_inc(v_head_326_);
        v_tail_327_ = leanh::lean_ctor_get(v_xs_324_, 1);
        leanh::lean_inc(v_tail_327_);
        leanh::lean_dec_ref_known(v_xs_324_, 2);
        v___f_328_ = leanh::lean_alloc_closure(
            l_List_maxIdxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_328_, 0, v_inst_322_);
        v___x_329_ = leanh::lean_unsigned_to_nat(0);
        v___x_330_ = leanh::lean_unsigned_to_nat(1);
        v___x_331_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(
            v___f_328_,
            v_f_323_,
            v_head_326_,
            v___x_329_,
            v___x_330_,
            v_tail_327_,
        );
        v___x_332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_332_, 0, v___x_331_);
        return v___x_332_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter___redArg(
    mut v_xs_333_: *mut leanh::LeanObject,
    mut v_h__1_334_: *mut leanh::LeanObject,
    mut v_h__2_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_333_) == 0 {
        let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_335_);
        v___x_336_ = leanh::lean_box(0);
        v___x_337_ = leanh::lean_apply_1(v_h__1_334_, v___x_336_);
        return v___x_337_;
    } else {
        let mut v_head_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_334_);
        v_head_338_ = leanh::lean_ctor_get(v_xs_333_, 0);
        leanh::lean_inc(v_head_338_);
        v_tail_339_ = leanh::lean_ctor_get(v_xs_333_, 1);
        leanh::lean_inc(v_tail_339_);
        leanh::lean_dec_ref_known(v_xs_333_, 2);
        v___x_340_ = leanh::lean_apply_2(v_h__2_335_, v_head_338_, v_tail_339_);
        return v___x_340_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter(
    mut v_00_u03b1_341_: *mut leanh::LeanObject,
    mut v_motive_342_: *mut leanh::LeanObject,
    mut v_xs_343_: *mut leanh::LeanObject,
    mut v_h__1_344_: *mut leanh::LeanObject,
    mut v_h__2_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_343_) == 0 {
        let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_345_);
        v___x_346_ = leanh::lean_box(0);
        v___x_347_ = leanh::lean_apply_1(v_h__1_344_, v___x_346_);
        return v___x_347_;
    } else {
        let mut v_head_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_344_);
        v_head_348_ = leanh::lean_ctor_get(v_xs_343_, 0);
        leanh::lean_inc(v_head_348_);
        v_tail_349_ = leanh::lean_ctor_get(v_xs_343_, 1);
        leanh::lean_inc(v_tail_349_);
        leanh::lean_dec_ref_known(v_xs_343_, 2);
        v___x_350_ = leanh::lean_apply_2(v_h__2_345_, v_head_348_, v_tail_349_);
        return v___x_350_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter___redArg(
    mut v_xs_351_: *mut leanh::LeanObject,
    mut v_h__1_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_353_ = leanh::lean_ctor_get(v_xs_351_, 0);
    leanh::lean_inc(v_head_353_);
    v_tail_354_ = leanh::lean_ctor_get(v_xs_351_, 1);
    leanh::lean_inc(v_tail_354_);
    leanh::lean_dec(v_xs_351_);
    v___x_355_ = leanh::lean_apply_3(
        v_h__1_352_,
        v_head_353_,
        v_tail_354_,
        leanh::lean_box(0),
    );
    return v___x_355_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter(
    mut v_00_u03b1_356_: *mut leanh::LeanObject,
    mut v_motive_357_: *mut leanh::LeanObject,
    mut v_xs_358_: *mut leanh::LeanObject,
    mut v_h_359_: *mut leanh::LeanObject,
    mut v_h__1_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_361_ = leanh::lean_ctor_get(v_xs_358_, 0);
    leanh::lean_inc(v_head_361_);
    v_tail_362_ = leanh::lean_ctor_get(v_xs_358_, 1);
    leanh::lean_inc(v_tail_362_);
    leanh::lean_dec(v_xs_358_);
    v___x_363_ = leanh::lean_apply_3(
        v_h__1_360_,
        v_head_361_,
        v_tail_362_,
        leanh::lean_box(0),
    );
    return v___x_363_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(
    mut v_inst_364_: *mut leanh::LeanObject,
    mut v_f_365_: *mut leanh::LeanObject,
    mut v_xs_366_: *mut leanh::LeanObject,
    mut v_ys_367_: *mut leanh::LeanObject,
    mut v_i_368_: *mut leanh::LeanObject,
    mut v_j_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: u8 = 0;
    leanh::lean_inc(v_i_368_);
    v___x_370_ = l_List_get___redArg(v_xs_366_, v_i_368_);
    leanh::lean_inc(v_f_365_);
    v___x_371_ = leanh::lean_apply_1(v_f_365_, v___x_370_);
    leanh::lean_inc(v_j_369_);
    v___x_372_ = l_List_get___redArg(v_ys_367_, v_j_369_);
    v___x_373_ = leanh::lean_apply_1(v_f_365_, v___x_372_);
    v___x_374_ = leanh::lean_apply_2(v_inst_364_, v___x_371_, v___x_373_);
    v___x_375_ = (leanh::lean_unbox(v___x_374_) as u8);
    if v___x_375_ == 0 {
        let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_368_);
        v___x_376_ = l_List_lengthTR___redArg(v_xs_366_);
        v___x_377_ = lean_nat_add(v___x_376_, v_j_369_);
        leanh::lean_dec(v_j_369_);
        leanh::lean_dec(v___x_376_);
        return v___x_377_;
    } else {
        leanh::lean_dec(v_j_369_);
        return v_i_368_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(
    mut v_inst_378_: *mut leanh::LeanObject,
    mut v_f_379_: *mut leanh::LeanObject,
    mut v_xs_380_: *mut leanh::LeanObject,
    mut v_ys_381_: *mut leanh::LeanObject,
    mut v_i_382_: *mut leanh::LeanObject,
    mut v_j_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(
        v_inst_378_,
        v_f_379_,
        v_xs_380_,
        v_ys_381_,
        v_i_382_,
        v_j_383_,
    );
    leanh::lean_dec(v_ys_381_);
    leanh::lean_dec(v_xs_380_);
    return v_res_384_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(
    mut v_00_u03b2_385_: *mut leanh::LeanObject,
    mut v_00_u03b1_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_inst_388_: *mut leanh::LeanObject,
    mut v_f_389_: *mut leanh::LeanObject,
    mut v_xs_390_: *mut leanh::LeanObject,
    mut v_ys_391_: *mut leanh::LeanObject,
    mut v_i_392_: *mut leanh::LeanObject,
    mut v_j_393_: *mut leanh::LeanObject,
    mut v_hi_394_: *mut leanh::LeanObject,
    mut v_hj_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b2_397_: *mut leanh::LeanObject,
    mut v_00_u03b1_398_: *mut leanh::LeanObject,
    mut v_inst_399_: *mut leanh::LeanObject,
    mut v_inst_400_: *mut leanh::LeanObject,
    mut v_f_401_: *mut leanh::LeanObject,
    mut v_xs_402_: *mut leanh::LeanObject,
    mut v_ys_403_: *mut leanh::LeanObject,
    mut v_i_404_: *mut leanh::LeanObject,
    mut v_j_405_: *mut leanh::LeanObject,
    mut v_hi_406_: *mut leanh::LeanObject,
    mut v_hj_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_408_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_ys_403_);
    leanh::lean_dec(v_xs_402_);
    return v_res_408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_MinMaxIdx(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_MinMaxOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_MinMaxIdx(
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
pub unsafe fn initialize_Init_Data_List_MinMaxIdx(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_MinMaxOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMaxIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_MinMaxIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_MinMaxIdx(builtin);
}