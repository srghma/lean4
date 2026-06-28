// Lean compiler output
// Module: Init.Data.List.MinMaxOn
// Imports: Init.Data.Order.MinMaxOn Init.Data.List.Lemmas Init.Data.List.TakeDrop Init.Data.Order.Lemmas Init.Data.List.Sublist Init.Data.List.MinMax Init.Data.Option.Lemmas Init.ByCases Init.Data.Bool
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Order::MinMaxOn::{
    initialize_Init_Data_Order_MinMaxOn, l_minOn, runtime_initialize_Init_Data_Order_MinMaxOn,
};
use crate::r#gen::Init::Prelude::l_List_foldl___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag, lean_unbox,
};
pub unsafe fn l_List_minOn___redArg(
    mut v_inst_180_: *mut LeanObject,
    mut v_inst_181_: *mut LeanObject,
    mut v_f_182_: *mut LeanObject,
    mut v_l_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    v_head_184_ = lean_ctor_get(v_l_183_, 0);
    lean_inc(v_head_184_);
    v_tail_185_ = lean_ctor_get(v_l_183_, 1);
    lean_inc(v_tail_185_);
    lean_dec(v_l_183_);
    v___x_186_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    lean_closure_set(v___x_186_, 0, lean_box(0));
    lean_closure_set(v___x_186_, 1, lean_box(0));
    lean_closure_set(v___x_186_, 2, v_inst_180_);
    lean_closure_set(v___x_186_, 3, v_inst_181_);
    lean_closure_set(v___x_186_, 4, v_f_182_);
    v___x_187_ = l_List_foldl___redArg(v___x_186_, v_head_184_, v_tail_185_);
    return v___x_187_;
}
pub unsafe fn l_List_minOn(
    mut v_00_u03b2_188_: *mut LeanObject,
    mut v_00_u03b1_189_: *mut LeanObject,
    mut v_inst_190_: *mut LeanObject,
    mut v_inst_191_: *mut LeanObject,
    mut v_f_192_: *mut LeanObject,
    mut v_l_193_: *mut LeanObject,
    mut v_h_194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    v_head_195_ = lean_ctor_get(v_l_193_, 0);
    lean_inc(v_head_195_);
    v_tail_196_ = lean_ctor_get(v_l_193_, 1);
    lean_inc(v_tail_196_);
    lean_dec(v_l_193_);
    v___x_197_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    lean_closure_set(v___x_197_, 0, lean_box(0));
    lean_closure_set(v___x_197_, 1, lean_box(0));
    lean_closure_set(v___x_197_, 2, v_inst_190_);
    lean_closure_set(v___x_197_, 3, v_inst_191_);
    lean_closure_set(v___x_197_, 4, v_f_192_);
    v___x_198_ = l_List_foldl___redArg(v___x_197_, v_head_195_, v_tail_196_);
    return v___x_198_;
}
pub unsafe fn l_List_maxOn___redArg___lam__0(
    mut v_inst_199_: *mut LeanObject,
    mut v_a_200_: *mut LeanObject,
    mut v_b_201_: *mut LeanObject,
) -> u8 {
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: u8 = 0;
    v___x_202_ = lean_apply_2(v_inst_199_, v_b_201_, v_a_200_);
    v___x_203_ = (lean_unbox(v___x_202_) as u8);
    return v___x_203_;
}
pub unsafe fn l_List_maxOn___redArg___lam__0___boxed(
    mut v_inst_204_: *mut LeanObject,
    mut v_a_205_: *mut LeanObject,
    mut v_b_206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_207_: u8 = 0;
    let mut v_r_208_: *mut LeanObject = core::ptr::null_mut();
    v_res_207_ = l_List_maxOn___redArg___lam__0(v_inst_204_, v_a_205_, v_b_206_);
    v_r_208_ = lean_box((v_res_207_) as usize);
    return v_r_208_;
}
pub unsafe fn l_List_maxOn___redArg(
    mut v_inst_209_: *mut LeanObject,
    mut v_f_210_: *mut LeanObject,
    mut v_l_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    v___x_212_ = lean_box(0);
    v_head_213_ = lean_ctor_get(v_l_211_, 0);
    lean_inc(v_head_213_);
    v_tail_214_ = lean_ctor_get(v_l_211_, 1);
    lean_inc(v_tail_214_);
    lean_dec(v_l_211_);
    v___f_215_ = lean_alloc_closure(
        l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_215_, 0, v_inst_209_);
    v___x_216_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    lean_closure_set(v___x_216_, 0, lean_box(0));
    lean_closure_set(v___x_216_, 1, lean_box(0));
    lean_closure_set(v___x_216_, 2, v___x_212_);
    lean_closure_set(v___x_216_, 3, v___f_215_);
    lean_closure_set(v___x_216_, 4, v_f_210_);
    v___x_217_ = l_List_foldl___redArg(v___x_216_, v_head_213_, v_tail_214_);
    return v___x_217_;
}
pub unsafe fn l_List_maxOn(
    mut v_00_u03b2_218_: *mut LeanObject,
    mut v_00_u03b1_219_: *mut LeanObject,
    mut v_i_220_: *mut LeanObject,
    mut v_inst_221_: *mut LeanObject,
    mut v_f_222_: *mut LeanObject,
    mut v_l_223_: *mut LeanObject,
    mut v_h_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    v___x_225_ = lean_box(0);
    v_head_226_ = lean_ctor_get(v_l_223_, 0);
    lean_inc(v_head_226_);
    v_tail_227_ = lean_ctor_get(v_l_223_, 1);
    lean_inc(v_tail_227_);
    lean_dec(v_l_223_);
    v___f_228_ = lean_alloc_closure(
        l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_228_, 0, v_inst_221_);
    v___x_229_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    lean_closure_set(v___x_229_, 0, lean_box(0));
    lean_closure_set(v___x_229_, 1, lean_box(0));
    lean_closure_set(v___x_229_, 2, v___x_225_);
    lean_closure_set(v___x_229_, 3, v___f_228_);
    lean_closure_set(v___x_229_, 4, v_f_222_);
    v___x_230_ = l_List_foldl___redArg(v___x_229_, v_head_226_, v_tail_227_);
    return v___x_230_;
}
pub unsafe fn l_List_minOn_x3f___redArg(
    mut v_inst_231_: *mut LeanObject,
    mut v_inst_232_: *mut LeanObject,
    mut v_f_233_: *mut LeanObject,
    mut v_l_234_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_234_) == 0 {
        let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_233_);
        lean_dec_ref(v_inst_232_);
        v___x_235_ = lean_box(0);
        return v___x_235_;
    } else {
        let mut v_head_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        v_head_236_ = lean_ctor_get(v_l_234_, 0);
        lean_inc(v_head_236_);
        v_tail_237_ = lean_ctor_get(v_l_234_, 1);
        lean_inc(v_tail_237_);
        lean_dec_ref_known(v_l_234_, 2);
        v___x_238_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        lean_closure_set(v___x_238_, 0, lean_box(0));
        lean_closure_set(v___x_238_, 1, lean_box(0));
        lean_closure_set(v___x_238_, 2, v_inst_231_);
        lean_closure_set(v___x_238_, 3, v_inst_232_);
        lean_closure_set(v___x_238_, 4, v_f_233_);
        v___x_239_ = l_List_foldl___redArg(v___x_238_, v_head_236_, v_tail_237_);
        v___x_240_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_240_, 0, v___x_239_);
        return v___x_240_;
    }
}
pub unsafe fn l_List_minOn_x3f(
    mut v_00_u03b2_241_: *mut LeanObject,
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_inst_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_f_245_: *mut LeanObject,
    mut v_l_246_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_246_) == 0 {
        let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_245_);
        lean_dec_ref(v_inst_244_);
        v___x_247_ = lean_box(0);
        return v___x_247_;
    } else {
        let mut v_head_248_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
        v_head_248_ = lean_ctor_get(v_l_246_, 0);
        lean_inc(v_head_248_);
        v_tail_249_ = lean_ctor_get(v_l_246_, 1);
        lean_inc(v_tail_249_);
        lean_dec_ref_known(v_l_246_, 2);
        v___x_250_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        lean_closure_set(v___x_250_, 0, lean_box(0));
        lean_closure_set(v___x_250_, 1, lean_box(0));
        lean_closure_set(v___x_250_, 2, v_inst_243_);
        lean_closure_set(v___x_250_, 3, v_inst_244_);
        lean_closure_set(v___x_250_, 4, v_f_245_);
        v___x_251_ = l_List_foldl___redArg(v___x_250_, v_head_248_, v_tail_249_);
        v___x_252_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_252_, 0, v___x_251_);
        return v___x_252_;
    }
}
pub unsafe fn l_List_maxOn_x3f___redArg(
    mut v_inst_253_: *mut LeanObject,
    mut v_f_254_: *mut LeanObject,
    mut v_l_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v___x_256_ = lean_box(0);
    if lean_obj_tag(v_l_255_) == 0 {
        let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_254_);
        lean_dec_ref(v_inst_253_);
        v___x_257_ = lean_box(0);
        return v___x_257_;
    } else {
        let mut v_head_258_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        v_head_258_ = lean_ctor_get(v_l_255_, 0);
        lean_inc(v_head_258_);
        v_tail_259_ = lean_ctor_get(v_l_255_, 1);
        lean_inc(v_tail_259_);
        lean_dec_ref_known(v_l_255_, 2);
        v___f_260_ = lean_alloc_closure(
            l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_260_, 0, v_inst_253_);
        v___x_261_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        lean_closure_set(v___x_261_, 0, lean_box(0));
        lean_closure_set(v___x_261_, 1, lean_box(0));
        lean_closure_set(v___x_261_, 2, v___x_256_);
        lean_closure_set(v___x_261_, 3, v___f_260_);
        lean_closure_set(v___x_261_, 4, v_f_254_);
        v___x_262_ = l_List_foldl___redArg(v___x_261_, v_head_258_, v_tail_259_);
        v___x_263_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_263_, 0, v___x_262_);
        return v___x_263_;
    }
}
pub unsafe fn l_List_maxOn_x3f(
    mut v_00_u03b2_264_: *mut LeanObject,
    mut v_00_u03b1_265_: *mut LeanObject,
    mut v_i_266_: *mut LeanObject,
    mut v_inst_267_: *mut LeanObject,
    mut v_f_268_: *mut LeanObject,
    mut v_l_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = lean_box(0);
    if lean_obj_tag(v_l_269_) == 0 {
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_268_);
        lean_dec_ref(v_inst_267_);
        v___x_271_ = lean_box(0);
        return v___x_271_;
    } else {
        let mut v_head_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        v_head_272_ = lean_ctor_get(v_l_269_, 0);
        lean_inc(v_head_272_);
        v_tail_273_ = lean_ctor_get(v_l_269_, 1);
        lean_inc(v_tail_273_);
        lean_dec_ref_known(v_l_269_, 2);
        v___f_274_ = lean_alloc_closure(
            l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_274_, 0, v_inst_267_);
        v___x_275_ = lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        lean_closure_set(v___x_275_, 0, lean_box(0));
        lean_closure_set(v___x_275_, 1, lean_box(0));
        lean_closure_set(v___x_275_, 2, v___x_270_);
        lean_closure_set(v___x_275_, 3, v___f_274_);
        lean_closure_set(v___x_275_, 4, v_f_268_);
        v___x_276_ = l_List_foldl___redArg(v___x_275_, v_head_272_, v_tail_273_);
        v___x_277_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_277_, 0, v___x_276_);
        return v___x_277_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter___redArg(
    mut v_l_278_: *mut LeanObject,
    mut v_h__1_279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    v_head_280_ = lean_ctor_get(v_l_278_, 0);
    lean_inc(v_head_280_);
    v_tail_281_ = lean_ctor_get(v_l_278_, 1);
    lean_inc(v_tail_281_);
    lean_dec(v_l_278_);
    v___x_282_ = lean_apply_3(v_h__1_279_, v_head_280_, v_tail_281_, lean_box(0));
    return v___x_282_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter(
    mut v_00_u03b1_283_: *mut LeanObject,
    mut v_motive_284_: *mut LeanObject,
    mut v_l_285_: *mut LeanObject,
    mut v_h_286_: *mut LeanObject,
    mut v_h__1_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v_head_288_ = lean_ctor_get(v_l_285_, 0);
    lean_inc(v_head_288_);
    v_tail_289_ = lean_ctor_get(v_l_285_, 1);
    lean_inc(v_tail_289_);
    lean_dec(v_l_285_);
    v___x_290_ = lean_apply_3(v_h__1_287_, v_head_288_, v_tail_289_, lean_box(0));
    return v___x_290_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter___redArg(
    mut v_x_291_: *mut LeanObject,
    mut v_h__1_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    v_head_293_ = lean_ctor_get(v_x_291_, 0);
    lean_inc(v_head_293_);
    v_tail_294_ = lean_ctor_get(v_x_291_, 1);
    lean_inc(v_tail_294_);
    lean_dec(v_x_291_);
    v___x_295_ = lean_apply_3(v_h__1_292_, v_head_293_, v_tail_294_, lean_box(0));
    return v___x_295_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter(
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_motive_297_: *mut LeanObject,
    mut v_x_298_: *mut LeanObject,
    mut v_x_299_: *mut LeanObject,
    mut v_h__1_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v_head_301_ = lean_ctor_get(v_x_298_, 0);
    lean_inc(v_head_301_);
    v_tail_302_ = lean_ctor_get(v_x_298_, 1);
    lean_inc(v_tail_302_);
    lean_dec(v_x_298_);
    v___x_303_ = lean_apply_3(v_h__1_300_, v_head_301_, v_tail_302_, lean_box(0));
    return v___x_303_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter___redArg(
    mut v_x_304_: *mut LeanObject,
    mut v_x_305_: *mut LeanObject,
    mut v_h__1_306_: *mut LeanObject,
    mut v_h__2_307_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_305_) == 0 {
        let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_307_);
        v___x_308_ = lean_apply_1(v_h__1_306_, v_x_304_);
        return v___x_308_;
    } else {
        let mut v_head_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_306_);
        v_head_309_ = lean_ctor_get(v_x_305_, 0);
        lean_inc(v_head_309_);
        v_tail_310_ = lean_ctor_get(v_x_305_, 1);
        lean_inc(v_tail_310_);
        lean_dec_ref_known(v_x_305_, 2);
        v___x_311_ = lean_apply_3(v_h__2_307_, v_x_304_, v_head_309_, v_tail_310_);
        return v___x_311_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter(
    mut v_00_u03b1_312_: *mut LeanObject,
    mut v_00_u03b2_313_: *mut LeanObject,
    mut v_motive_314_: *mut LeanObject,
    mut v_x_315_: *mut LeanObject,
    mut v_x_316_: *mut LeanObject,
    mut v_h__1_317_: *mut LeanObject,
    mut v_h__2_318_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_316_) == 0 {
        let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_318_);
        v___x_319_ = lean_apply_1(v_h__1_317_, v_x_315_);
        return v___x_319_;
    } else {
        let mut v_head_320_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_317_);
        v_head_320_ = lean_ctor_get(v_x_316_, 0);
        lean_inc(v_head_320_);
        v_tail_321_ = lean_ctor_get(v_x_316_, 1);
        lean_inc(v_tail_321_);
        lean_dec_ref_known(v_x_316_, 2);
        v___x_322_ = lean_apply_3(v_h__2_318_, v_x_315_, v_head_320_, v_tail_321_);
        return v___x_322_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_323_: *mut LeanObject,
    mut v_h__1_324_: *mut LeanObject,
    mut v_h__2_325_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_323_) == 0 {
        let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_325_);
        v___x_326_ = lean_box(0);
        v___x_327_ = lean_apply_1(v_h__1_324_, v___x_326_);
        return v___x_327_;
    } else {
        let mut v_head_328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_324_);
        v_head_328_ = lean_ctor_get(v_x_323_, 0);
        lean_inc(v_head_328_);
        v_tail_329_ = lean_ctor_get(v_x_323_, 1);
        lean_inc(v_tail_329_);
        lean_dec_ref_known(v_x_323_, 2);
        v___x_330_ = lean_apply_2(v_h__2_325_, v_head_328_, v_tail_329_);
        return v___x_330_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_331_: *mut LeanObject,
    mut v_motive_332_: *mut LeanObject,
    mut v_x_333_: *mut LeanObject,
    mut v_h__1_334_: *mut LeanObject,
    mut v_h__2_335_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_333_) == 0 {
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
        v_head_338_ = lean_ctor_get(v_x_333_, 0);
        lean_inc(v_head_338_);
        v_tail_339_ = lean_ctor_get(v_x_333_, 1);
        lean_inc(v_tail_339_);
        lean_dec_ref_known(v_x_333_, 2);
        v___x_340_ = lean_apply_2(v_h__2_335_, v_head_338_, v_tail_339_);
        return v___x_340_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter___redArg(
    mut v_l_341_: *mut LeanObject,
    mut v_h__1_342_: *mut LeanObject,
    mut v_h__2_343_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_341_) == 0 {
        let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_343_);
        v___x_344_ = lean_box(0);
        v___x_345_ = lean_apply_1(v_h__1_342_, v___x_344_);
        return v___x_345_;
    } else {
        let mut v_head_346_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_342_);
        v_head_346_ = lean_ctor_get(v_l_341_, 0);
        lean_inc(v_head_346_);
        v_tail_347_ = lean_ctor_get(v_l_341_, 1);
        lean_inc(v_tail_347_);
        lean_dec_ref_known(v_l_341_, 2);
        v___x_348_ = lean_apply_2(v_h__2_343_, v_head_346_, v_tail_347_);
        return v___x_348_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter(
    mut v_00_u03b1_349_: *mut LeanObject,
    mut v_motive_350_: *mut LeanObject,
    mut v_l_351_: *mut LeanObject,
    mut v_h__1_352_: *mut LeanObject,
    mut v_h__2_353_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_351_) == 0 {
        let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_353_);
        v___x_354_ = lean_box(0);
        v___x_355_ = lean_apply_1(v_h__1_352_, v___x_354_);
        return v___x_355_;
    } else {
        let mut v_head_356_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_352_);
        v_head_356_ = lean_ctor_get(v_l_351_, 0);
        lean_inc(v_head_356_);
        v_tail_357_ = lean_ctor_get(v_l_351_, 1);
        lean_inc(v_tail_357_);
        lean_dec_ref_known(v_l_351_, 2);
        v___x_358_ = lean_apply_2(v_h__2_353_, v_head_356_, v_tail_357_);
        return v___x_358_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_MinMaxOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_MinMaxOn(builtin);
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
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
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
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_MinMaxOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_MinMaxOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_MinMaxOn(builtin);
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
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
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
    res = runtime_initialize_Init_Data_List_MinMaxOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_MinMaxOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_MinMaxOn(builtin);
}
