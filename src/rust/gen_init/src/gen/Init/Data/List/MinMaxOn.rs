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
pub unsafe fn l_List_minOn___redArg(
    mut v_inst_180_: *mut leanh::LeanObject,
    mut v_inst_181_: *mut leanh::LeanObject,
    mut v_f_182_: *mut leanh::LeanObject,
    mut v_l_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_184_ = leanh::lean_ctor_get(v_l_183_, 0);
    leanh::lean_inc(v_head_184_);
    v_tail_185_ = leanh::lean_ctor_get(v_l_183_, 1);
    leanh::lean_inc(v_tail_185_);
    leanh::lean_dec(v_l_183_);
    v___x_186_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_186_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_186_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_186_, 2, v_inst_180_);
    leanh::lean_closure_set(v___x_186_, 3, v_inst_181_);
    leanh::lean_closure_set(v___x_186_, 4, v_f_182_);
    v___x_187_ = l_List_foldl___redArg(v___x_186_, v_head_184_, v_tail_185_);
    return v___x_187_;
}
pub unsafe fn l_List_minOn(
    mut v_00_u03b2_188_: *mut leanh::LeanObject,
    mut v_00_u03b1_189_: *mut leanh::LeanObject,
    mut v_inst_190_: *mut leanh::LeanObject,
    mut v_inst_191_: *mut leanh::LeanObject,
    mut v_f_192_: *mut leanh::LeanObject,
    mut v_l_193_: *mut leanh::LeanObject,
    mut v_h_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_195_ = leanh::lean_ctor_get(v_l_193_, 0);
    leanh::lean_inc(v_head_195_);
    v_tail_196_ = leanh::lean_ctor_get(v_l_193_, 1);
    leanh::lean_inc(v_tail_196_);
    leanh::lean_dec(v_l_193_);
    v___x_197_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_197_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_197_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_197_, 2, v_inst_190_);
    leanh::lean_closure_set(v___x_197_, 3, v_inst_191_);
    leanh::lean_closure_set(v___x_197_, 4, v_f_192_);
    v___x_198_ = l_List_foldl___redArg(v___x_197_, v_head_195_, v_tail_196_);
    return v___x_198_;
}
pub unsafe fn l_List_maxOn___redArg___lam__0(
    mut v_inst_199_: *mut leanh::LeanObject,
    mut v_a_200_: *mut leanh::LeanObject,
    mut v_b_201_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: u8 = 0;
    v___x_202_ = leanh::lean_apply_2(v_inst_199_, v_b_201_, v_a_200_);
    v___x_203_ = (leanh::lean_unbox(v___x_202_) as u8);
    return v___x_203_;
}
pub unsafe fn l_List_maxOn___redArg___lam__0___boxed(
    mut v_inst_204_: *mut leanh::LeanObject,
    mut v_a_205_: *mut leanh::LeanObject,
    mut v_b_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_207_: u8 = 0;
    let mut v_r_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_207_ = l_List_maxOn___redArg___lam__0(v_inst_204_, v_a_205_, v_b_206_);
    v_r_208_ = leanh::lean_box((v_res_207_) as usize);
    return v_r_208_;
}
pub unsafe fn l_List_maxOn___redArg(
    mut v_inst_209_: *mut leanh::LeanObject,
    mut v_f_210_: *mut leanh::LeanObject,
    mut v_l_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_212_ = leanh::lean_box(0);
    v_head_213_ = leanh::lean_ctor_get(v_l_211_, 0);
    leanh::lean_inc(v_head_213_);
    v_tail_214_ = leanh::lean_ctor_get(v_l_211_, 1);
    leanh::lean_inc(v_tail_214_);
    leanh::lean_dec(v_l_211_);
    v___f_215_ = leanh::lean_alloc_closure(
        l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_215_, 0, v_inst_209_);
    v___x_216_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_216_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_216_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_216_, 2, v___x_212_);
    leanh::lean_closure_set(v___x_216_, 3, v___f_215_);
    leanh::lean_closure_set(v___x_216_, 4, v_f_210_);
    v___x_217_ = l_List_foldl___redArg(v___x_216_, v_head_213_, v_tail_214_);
    return v___x_217_;
}
pub unsafe fn l_List_maxOn(
    mut v_00_u03b2_218_: *mut leanh::LeanObject,
    mut v_00_u03b1_219_: *mut leanh::LeanObject,
    mut v_i_220_: *mut leanh::LeanObject,
    mut v_inst_221_: *mut leanh::LeanObject,
    mut v_f_222_: *mut leanh::LeanObject,
    mut v_l_223_: *mut leanh::LeanObject,
    mut v_h_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_225_ = leanh::lean_box(0);
    v_head_226_ = leanh::lean_ctor_get(v_l_223_, 0);
    leanh::lean_inc(v_head_226_);
    v_tail_227_ = leanh::lean_ctor_get(v_l_223_, 1);
    leanh::lean_inc(v_tail_227_);
    leanh::lean_dec(v_l_223_);
    v___f_228_ = leanh::lean_alloc_closure(
        l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_228_, 0, v_inst_221_);
    v___x_229_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_229_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_229_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_229_, 2, v___x_225_);
    leanh::lean_closure_set(v___x_229_, 3, v___f_228_);
    leanh::lean_closure_set(v___x_229_, 4, v_f_222_);
    v___x_230_ = l_List_foldl___redArg(v___x_229_, v_head_226_, v_tail_227_);
    return v___x_230_;
}
pub unsafe fn l_List_minOn_x3f___redArg(
    mut v_inst_231_: *mut leanh::LeanObject,
    mut v_inst_232_: *mut leanh::LeanObject,
    mut v_f_233_: *mut leanh::LeanObject,
    mut v_l_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_234_) == 0 {
        let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_233_);
        leanh::lean_dec_ref(v_inst_232_);
        v___x_235_ = leanh::lean_box(0);
        return v___x_235_;
    } else {
        let mut v_head_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_236_ = leanh::lean_ctor_get(v_l_234_, 0);
        leanh::lean_inc(v_head_236_);
        v_tail_237_ = leanh::lean_ctor_get(v_l_234_, 1);
        leanh::lean_inc(v_tail_237_);
        leanh::lean_dec_ref_known(v_l_234_, 2);
        v___x_238_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        leanh::lean_closure_set(v___x_238_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_238_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_238_, 2, v_inst_231_);
        leanh::lean_closure_set(v___x_238_, 3, v_inst_232_);
        leanh::lean_closure_set(v___x_238_, 4, v_f_233_);
        v___x_239_ = l_List_foldl___redArg(v___x_238_, v_head_236_, v_tail_237_);
        v___x_240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_240_, 0, v___x_239_);
        return v___x_240_;
    }
}
pub unsafe fn l_List_minOn_x3f(
    mut v_00_u03b2_241_: *mut leanh::LeanObject,
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_inst_243_: *mut leanh::LeanObject,
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_f_245_: *mut leanh::LeanObject,
    mut v_l_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_246_) == 0 {
        let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_245_);
        leanh::lean_dec_ref(v_inst_244_);
        v___x_247_ = leanh::lean_box(0);
        return v___x_247_;
    } else {
        let mut v_head_248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_248_ = leanh::lean_ctor_get(v_l_246_, 0);
        leanh::lean_inc(v_head_248_);
        v_tail_249_ = leanh::lean_ctor_get(v_l_246_, 1);
        leanh::lean_inc(v_tail_249_);
        leanh::lean_dec_ref_known(v_l_246_, 2);
        v___x_250_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        leanh::lean_closure_set(v___x_250_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_250_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_250_, 2, v_inst_243_);
        leanh::lean_closure_set(v___x_250_, 3, v_inst_244_);
        leanh::lean_closure_set(v___x_250_, 4, v_f_245_);
        v___x_251_ = l_List_foldl___redArg(v___x_250_, v_head_248_, v_tail_249_);
        v___x_252_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_252_, 0, v___x_251_);
        return v___x_252_;
    }
}
pub unsafe fn l_List_maxOn_x3f___redArg(
    mut v_inst_253_: *mut leanh::LeanObject,
    mut v_f_254_: *mut leanh::LeanObject,
    mut v_l_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_256_ = leanh::lean_box(0);
    if leanh::lean_obj_tag(v_l_255_) == 0 {
        let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_254_);
        leanh::lean_dec_ref(v_inst_253_);
        v___x_257_ = leanh::lean_box(0);
        return v___x_257_;
    } else {
        let mut v_head_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_258_ = leanh::lean_ctor_get(v_l_255_, 0);
        leanh::lean_inc(v_head_258_);
        v_tail_259_ = leanh::lean_ctor_get(v_l_255_, 1);
        leanh::lean_inc(v_tail_259_);
        leanh::lean_dec_ref_known(v_l_255_, 2);
        v___f_260_ = leanh::lean_alloc_closure(
            l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_260_, 0, v_inst_253_);
        v___x_261_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        leanh::lean_closure_set(v___x_261_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_261_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_261_, 2, v___x_256_);
        leanh::lean_closure_set(v___x_261_, 3, v___f_260_);
        leanh::lean_closure_set(v___x_261_, 4, v_f_254_);
        v___x_262_ = l_List_foldl___redArg(v___x_261_, v_head_258_, v_tail_259_);
        v___x_263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_263_, 0, v___x_262_);
        return v___x_263_;
    }
}
pub unsafe fn l_List_maxOn_x3f(
    mut v_00_u03b2_264_: *mut leanh::LeanObject,
    mut v_00_u03b1_265_: *mut leanh::LeanObject,
    mut v_i_266_: *mut leanh::LeanObject,
    mut v_inst_267_: *mut leanh::LeanObject,
    mut v_f_268_: *mut leanh::LeanObject,
    mut v_l_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = leanh::lean_box(0);
    if leanh::lean_obj_tag(v_l_269_) == 0 {
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_268_);
        leanh::lean_dec_ref(v_inst_267_);
        v___x_271_ = leanh::lean_box(0);
        return v___x_271_;
    } else {
        let mut v_head_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_272_ = leanh::lean_ctor_get(v_l_269_, 0);
        leanh::lean_inc(v_head_272_);
        v_tail_273_ = leanh::lean_ctor_get(v_l_269_, 1);
        leanh::lean_inc(v_tail_273_);
        leanh::lean_dec_ref_known(v_l_269_, 2);
        v___f_274_ = leanh::lean_alloc_closure(
            l_List_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_274_, 0, v_inst_267_);
        v___x_275_ = leanh::lean_alloc_closure(l_minOn as *mut core::ffi::c_void, 7, 5);
        leanh::lean_closure_set(v___x_275_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_275_, 1, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_275_, 2, v___x_270_);
        leanh::lean_closure_set(v___x_275_, 3, v___f_274_);
        leanh::lean_closure_set(v___x_275_, 4, v_f_268_);
        v___x_276_ = l_List_foldl___redArg(v___x_275_, v_head_272_, v_tail_273_);
        v___x_277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_277_, 0, v___x_276_);
        return v___x_277_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter___redArg(
    mut v_l_278_: *mut leanh::LeanObject,
    mut v_h__1_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_280_ = leanh::lean_ctor_get(v_l_278_, 0);
    leanh::lean_inc(v_head_280_);
    v_tail_281_ = leanh::lean_ctor_get(v_l_278_, 1);
    leanh::lean_inc(v_tail_281_);
    leanh::lean_dec(v_l_278_);
    v___x_282_ = leanh::lean_apply_3(
        v_h__1_279_,
        v_head_280_,
        v_tail_281_,
        leanh::lean_box(0),
    );
    return v___x_282_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter(
    mut v_00_u03b1_283_: *mut leanh::LeanObject,
    mut v_motive_284_: *mut leanh::LeanObject,
    mut v_l_285_: *mut leanh::LeanObject,
    mut v_h_286_: *mut leanh::LeanObject,
    mut v_h__1_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_288_ = leanh::lean_ctor_get(v_l_285_, 0);
    leanh::lean_inc(v_head_288_);
    v_tail_289_ = leanh::lean_ctor_get(v_l_285_, 1);
    leanh::lean_inc(v_tail_289_);
    leanh::lean_dec(v_l_285_);
    v___x_290_ = leanh::lean_apply_3(
        v_h__1_287_,
        v_head_288_,
        v_tail_289_,
        leanh::lean_box(0),
    );
    return v___x_290_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter___redArg(
    mut v_x_291_: *mut leanh::LeanObject,
    mut v_h__1_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_293_ = leanh::lean_ctor_get(v_x_291_, 0);
    leanh::lean_inc(v_head_293_);
    v_tail_294_ = leanh::lean_ctor_get(v_x_291_, 1);
    leanh::lean_inc(v_tail_294_);
    leanh::lean_dec(v_x_291_);
    v___x_295_ = leanh::lean_apply_3(
        v_h__1_292_,
        v_head_293_,
        v_tail_294_,
        leanh::lean_box(0),
    );
    return v___x_295_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter(
    mut v_00_u03b1_296_: *mut leanh::LeanObject,
    mut v_motive_297_: *mut leanh::LeanObject,
    mut v_x_298_: *mut leanh::LeanObject,
    mut v_x_299_: *mut leanh::LeanObject,
    mut v_h__1_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_301_ = leanh::lean_ctor_get(v_x_298_, 0);
    leanh::lean_inc(v_head_301_);
    v_tail_302_ = leanh::lean_ctor_get(v_x_298_, 1);
    leanh::lean_inc(v_tail_302_);
    leanh::lean_dec(v_x_298_);
    v___x_303_ = leanh::lean_apply_3(
        v_h__1_300_,
        v_head_301_,
        v_tail_302_,
        leanh::lean_box(0),
    );
    return v___x_303_;
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter___redArg(
    mut v_x_304_: *mut leanh::LeanObject,
    mut v_x_305_: *mut leanh::LeanObject,
    mut v_h__1_306_: *mut leanh::LeanObject,
    mut v_h__2_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_305_) == 0 {
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_307_);
        v___x_308_ = leanh::lean_apply_1(v_h__1_306_, v_x_304_);
        return v___x_308_;
    } else {
        let mut v_head_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_306_);
        v_head_309_ = leanh::lean_ctor_get(v_x_305_, 0);
        leanh::lean_inc(v_head_309_);
        v_tail_310_ = leanh::lean_ctor_get(v_x_305_, 1);
        leanh::lean_inc(v_tail_310_);
        leanh::lean_dec_ref_known(v_x_305_, 2);
        v___x_311_ = leanh::lean_apply_3(v_h__2_307_, v_x_304_, v_head_309_, v_tail_310_);
        return v___x_311_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter(
    mut v_00_u03b1_312_: *mut leanh::LeanObject,
    mut v_00_u03b2_313_: *mut leanh::LeanObject,
    mut v_motive_314_: *mut leanh::LeanObject,
    mut v_x_315_: *mut leanh::LeanObject,
    mut v_x_316_: *mut leanh::LeanObject,
    mut v_h__1_317_: *mut leanh::LeanObject,
    mut v_h__2_318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_316_) == 0 {
        let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_318_);
        v___x_319_ = leanh::lean_apply_1(v_h__1_317_, v_x_315_);
        return v___x_319_;
    } else {
        let mut v_head_320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_317_);
        v_head_320_ = leanh::lean_ctor_get(v_x_316_, 0);
        leanh::lean_inc(v_head_320_);
        v_tail_321_ = leanh::lean_ctor_get(v_x_316_, 1);
        leanh::lean_inc(v_tail_321_);
        leanh::lean_dec_ref_known(v_x_316_, 2);
        v___x_322_ = leanh::lean_apply_3(v_h__2_318_, v_x_315_, v_head_320_, v_tail_321_);
        return v___x_322_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_323_: *mut leanh::LeanObject,
    mut v_h__1_324_: *mut leanh::LeanObject,
    mut v_h__2_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_323_) == 0 {
        let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_325_);
        v___x_326_ = leanh::lean_box(0);
        v___x_327_ = leanh::lean_apply_1(v_h__1_324_, v___x_326_);
        return v___x_327_;
    } else {
        let mut v_head_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_324_);
        v_head_328_ = leanh::lean_ctor_get(v_x_323_, 0);
        leanh::lean_inc(v_head_328_);
        v_tail_329_ = leanh::lean_ctor_get(v_x_323_, 1);
        leanh::lean_inc(v_tail_329_);
        leanh::lean_dec_ref_known(v_x_323_, 2);
        v___x_330_ = leanh::lean_apply_2(v_h__2_325_, v_head_328_, v_tail_329_);
        return v___x_330_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_331_: *mut leanh::LeanObject,
    mut v_motive_332_: *mut leanh::LeanObject,
    mut v_x_333_: *mut leanh::LeanObject,
    mut v_h__1_334_: *mut leanh::LeanObject,
    mut v_h__2_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_333_) == 0 {
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
        v_head_338_ = leanh::lean_ctor_get(v_x_333_, 0);
        leanh::lean_inc(v_head_338_);
        v_tail_339_ = leanh::lean_ctor_get(v_x_333_, 1);
        leanh::lean_inc(v_tail_339_);
        leanh::lean_dec_ref_known(v_x_333_, 2);
        v___x_340_ = leanh::lean_apply_2(v_h__2_335_, v_head_338_, v_tail_339_);
        return v___x_340_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter___redArg(
    mut v_l_341_: *mut leanh::LeanObject,
    mut v_h__1_342_: *mut leanh::LeanObject,
    mut v_h__2_343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_341_) == 0 {
        let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_343_);
        v___x_344_ = leanh::lean_box(0);
        v___x_345_ = leanh::lean_apply_1(v_h__1_342_, v___x_344_);
        return v___x_345_;
    } else {
        let mut v_head_346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_342_);
        v_head_346_ = leanh::lean_ctor_get(v_l_341_, 0);
        leanh::lean_inc(v_head_346_);
        v_tail_347_ = leanh::lean_ctor_get(v_l_341_, 1);
        leanh::lean_inc(v_tail_347_);
        leanh::lean_dec_ref_known(v_l_341_, 2);
        v___x_348_ = leanh::lean_apply_2(v_h__2_343_, v_head_346_, v_tail_347_);
        return v___x_348_;
    }
}
pub unsafe fn l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter(
    mut v_00_u03b1_349_: *mut leanh::LeanObject,
    mut v_motive_350_: *mut leanh::LeanObject,
    mut v_l_351_: *mut leanh::LeanObject,
    mut v_h__1_352_: *mut leanh::LeanObject,
    mut v_h__2_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_351_) == 0 {
        let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_353_);
        v___x_354_ = leanh::lean_box(0);
        v___x_355_ = leanh::lean_apply_1(v_h__1_352_, v___x_354_);
        return v___x_355_;
    } else {
        let mut v_head_356_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_352_);
        v_head_356_ = leanh::lean_ctor_get(v_l_351_, 0);
        leanh::lean_inc(v_head_356_);
        v_tail_357_ = leanh::lean_ctor_get(v_l_351_, 1);
        leanh::lean_inc(v_tail_357_);
        leanh::lean_dec_ref_known(v_l_351_, 2);
        v___x_358_ = leanh::lean_apply_2(v_h__2_353_, v_head_356_, v_tail_357_);
        return v___x_358_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_MinMaxOn(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_MinMaxOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_MinMaxOn(
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
pub unsafe fn initialize_Init_Data_List_MinMaxOn(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_MinMaxOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
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
    res = runtime_initialize_Init_Data_List_MinMaxOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_MinMaxOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_MinMaxOn(builtin);
}