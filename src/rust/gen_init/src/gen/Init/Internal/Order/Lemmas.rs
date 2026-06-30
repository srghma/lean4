// Lean compiler output
// Module: Init.Internal.Order.Lemmas
// Imports: Init.Data.List.Control Init.Data.Option.Basic Init.Data.Array.Basic Init.Internal.Order.Basic Init.Data.List.Monadic Init.Data.Array.Bootstrap
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Monadic::{
    initialize_Init_Data_List_Monadic, runtime_initialize_Init_Data_List_Monadic,
};
use crate::r#gen::Init::Data::Option::Basic::{
    initialize_Init_Data_Option_Basic, runtime_initialize_Init_Data_Option_Basic,
};
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_151_: *mut leanh::LeanObject,
    mut v_h__1_152_: *mut leanh::LeanObject,
    mut v_h__2_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_155_: u8 = 0;
    v_zero_154_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_155_ = lean_nat_dec_eq(v_i_151_, v_zero_154_);
    if v_isZero_155_ == 1 {
        let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_153_);
        v___x_156_ = leanh::lean_apply_1(v_h__1_152_, leanh::lean_box(0));
        return v___x_156_;
    } else {
        let mut v_one_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_152_);
        v_one_157_ = leanh::lean_unsigned_to_nat(1);
        v_n_158_ = lean_nat_sub(v_i_151_, v_one_157_);
        v___x_159_ = leanh::lean_apply_2(v_h__2_153_, v_n_158_, leanh::lean_box(0));
        return v___x_159_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_160_: *mut leanh::LeanObject,
    mut v_h__1_161_: *mut leanh::LeanObject,
    mut v_h__2_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_160_,
            v_h__1_161_,
            v_h__2_162_,
        );
    leanh::lean_dec(v_i_160_);
    return v_res_163_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_164_: *mut leanh::LeanObject,
    mut v_as_165_: *mut leanh::LeanObject,
    mut v_motive_166_: *mut leanh::LeanObject,
    mut v_i_167_: *mut leanh::LeanObject,
    mut v_h_168_: *mut leanh::LeanObject,
    mut v_h__1_169_: *mut leanh::LeanObject,
    mut v_h__2_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_172_: u8 = 0;
    v_zero_171_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_172_ = lean_nat_dec_eq(v_i_167_, v_zero_171_);
    if v_isZero_172_ == 1 {
        let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_170_);
        v___x_173_ = leanh::lean_apply_1(v_h__1_169_, leanh::lean_box(0));
        return v___x_173_;
    } else {
        let mut v_one_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_169_);
        v_one_174_ = leanh::lean_unsigned_to_nat(1);
        v_n_175_ = lean_nat_sub(v_i_167_, v_one_174_);
        v___x_176_ = leanh::lean_apply_2(v_h__2_170_, v_n_175_, leanh::lean_box(0));
        return v___x_176_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_177_: *mut leanh::LeanObject,
    mut v_as_178_: *mut leanh::LeanObject,
    mut v_motive_179_: *mut leanh::LeanObject,
    mut v_i_180_: *mut leanh::LeanObject,
    mut v_h_181_: *mut leanh::LeanObject,
    mut v_h__1_182_: *mut leanh::LeanObject,
    mut v_h__2_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_184_ = l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_177_,
        v_as_178_,
        v_motive_179_,
        v_i_180_,
        v_h_181_,
        v_h__1_182_,
        v_h__2_183_,
    );
    leanh::lean_dec(v_i_180_);
    leanh::lean_dec_ref(v_as_178_);
    return v_res_184_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(
    mut v_i_185_: *mut leanh::LeanObject,
    mut v_h__1_186_: *mut leanh::LeanObject,
    mut v_h__2_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_189_: u8 = 0;
    v_zero_188_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_189_ = lean_nat_dec_eq(v_i_185_, v_zero_188_);
    if v_isZero_189_ == 1 {
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_187_);
        v___x_190_ = leanh::lean_box(0);
        v___x_191_ = leanh::lean_apply_1(v_h__1_186_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_one_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_186_);
        v_one_192_ = leanh::lean_unsigned_to_nat(1);
        v_n_193_ = lean_nat_sub(v_i_185_, v_one_192_);
        v___x_194_ = leanh::lean_apply_1(v_h__2_187_, v_n_193_);
        return v___x_194_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(
    mut v_i_195_: *mut leanh::LeanObject,
    mut v_h__1_196_: *mut leanh::LeanObject,
    mut v_h__2_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_198_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(
            v_i_195_,
            v_h__1_196_,
            v_h__2_197_,
        );
    leanh::lean_dec(v_i_195_);
    return v_res_198_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(
    mut v_motive_199_: *mut leanh::LeanObject,
    mut v_i_200_: *mut leanh::LeanObject,
    mut v_h__1_201_: *mut leanh::LeanObject,
    mut v_h__2_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_204_: u8 = 0;
    v_zero_203_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_204_ = lean_nat_dec_eq(v_i_200_, v_zero_203_);
    if v_isZero_204_ == 1 {
        let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_202_);
        v___x_205_ = leanh::lean_box(0);
        v___x_206_ = leanh::lean_apply_1(v_h__1_201_, v___x_205_);
        return v___x_206_;
    } else {
        let mut v_one_207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_201_);
        v_one_207_ = leanh::lean_unsigned_to_nat(1);
        v_n_208_ = lean_nat_sub(v_i_200_, v_one_207_);
        v___x_209_ = leanh::lean_apply_1(v_h__2_202_, v_n_208_);
        return v___x_209_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(
    mut v_motive_210_: *mut leanh::LeanObject,
    mut v_i_211_: *mut leanh::LeanObject,
    mut v_h__1_212_: *mut leanh::LeanObject,
    mut v_h__2_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(
        v_motive_210_,
        v_i_211_,
        v_h__1_212_,
        v_h__2_213_,
    );
    leanh::lean_dec(v_i_211_);
    return v_res_214_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
    mut v_i_215_: *mut leanh::LeanObject,
    mut v_h__1_216_: *mut leanh::LeanObject,
    mut v_h__2_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_219_: u8 = 0;
    v_zero_218_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_219_ = lean_nat_dec_eq(v_i_215_, v_zero_218_);
    if v_isZero_219_ == 1 {
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_217_);
        v___x_220_ = leanh::lean_apply_1(v_h__1_216_, leanh::lean_box(0));
        return v___x_220_;
    } else {
        let mut v_one_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_216_);
        v_one_221_ = leanh::lean_unsigned_to_nat(1);
        v_n_222_ = lean_nat_sub(v_i_215_, v_one_221_);
        v___x_223_ = leanh::lean_apply_2(v_h__2_217_, v_n_222_, leanh::lean_box(0));
        return v___x_223_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(
    mut v_i_224_: *mut leanh::LeanObject,
    mut v_h__1_225_: *mut leanh::LeanObject,
    mut v_h__2_226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_227_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
            v_i_224_,
            v_h__1_225_,
            v_h__2_226_,
        );
    leanh::lean_dec(v_i_224_);
    return v_res_227_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(
    mut v_00_u03b1_228_: *mut leanh::LeanObject,
    mut v_as_229_: *mut leanh::LeanObject,
    mut v_j_230_: *mut leanh::LeanObject,
    mut v_motive_231_: *mut leanh::LeanObject,
    mut v_i_232_: *mut leanh::LeanObject,
    mut v_inv_233_: *mut leanh::LeanObject,
    mut v_h__1_234_: *mut leanh::LeanObject,
    mut v_h__2_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_237_: u8 = 0;
    v_zero_236_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_237_ = lean_nat_dec_eq(v_i_232_, v_zero_236_);
    if v_isZero_237_ == 1 {
        let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_235_);
        v___x_238_ = leanh::lean_apply_1(v_h__1_234_, leanh::lean_box(0));
        return v___x_238_;
    } else {
        let mut v_one_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_234_);
        v_one_239_ = leanh::lean_unsigned_to_nat(1);
        v_n_240_ = lean_nat_sub(v_i_232_, v_one_239_);
        v___x_241_ = leanh::lean_apply_2(v_h__2_235_, v_n_240_, leanh::lean_box(0));
        return v___x_241_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___boxed(
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_as_243_: *mut leanh::LeanObject,
    mut v_j_244_: *mut leanh::LeanObject,
    mut v_motive_245_: *mut leanh::LeanObject,
    mut v_i_246_: *mut leanh::LeanObject,
    mut v_inv_247_: *mut leanh::LeanObject,
    mut v_h__1_248_: *mut leanh::LeanObject,
    mut v_h__2_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_250_ = l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(
        v_00_u03b1_242_,
        v_as_243_,
        v_j_244_,
        v_motive_245_,
        v_i_246_,
        v_inv_247_,
        v_h__1_248_,
        v_h__2_249_,
    );
    leanh::lean_dec(v_i_246_);
    leanh::lean_dec(v_j_244_);
    leanh::lean_dec_ref(v_as_243_);
    return v_res_250_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_251_: *mut leanh::LeanObject,
    mut v_h__1_252_: *mut leanh::LeanObject,
    mut v_h__2_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_255_: u8 = 0;
    v_zero_254_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_255_ = lean_nat_dec_eq(v_x_251_, v_zero_254_);
    if v_isZero_255_ == 1 {
        let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_253_);
        v___x_256_ = leanh::lean_apply_1(v_h__1_252_, leanh::lean_box(0));
        return v___x_256_;
    } else {
        let mut v_one_257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_252_);
        v_one_257_ = leanh::lean_unsigned_to_nat(1);
        v_n_258_ = lean_nat_sub(v_x_251_, v_one_257_);
        v___x_259_ = leanh::lean_apply_2(v_h__2_253_, v_n_258_, leanh::lean_box(0));
        return v___x_259_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_260_: *mut leanh::LeanObject,
    mut v_h__1_261_: *mut leanh::LeanObject,
    mut v_h__2_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_263_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(
            v_x_260_,
            v_h__1_261_,
            v_h__2_262_,
        );
    leanh::lean_dec(v_x_260_);
    return v_res_263_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_264_: *mut leanh::LeanObject,
    mut v_xs_265_: *mut leanh::LeanObject,
    mut v_motive_266_: *mut leanh::LeanObject,
    mut v_x_267_: *mut leanh::LeanObject,
    mut v_x_268_: *mut leanh::LeanObject,
    mut v_h__1_269_: *mut leanh::LeanObject,
    mut v_h__2_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_272_: u8 = 0;
    v_zero_271_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_272_ = lean_nat_dec_eq(v_x_267_, v_zero_271_);
    if v_isZero_272_ == 1 {
        let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_270_);
        v___x_273_ = leanh::lean_apply_1(v_h__1_269_, leanh::lean_box(0));
        return v___x_273_;
    } else {
        let mut v_one_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_269_);
        v_one_274_ = leanh::lean_unsigned_to_nat(1);
        v_n_275_ = lean_nat_sub(v_x_267_, v_one_274_);
        v___x_276_ = leanh::lean_apply_2(v_h__2_270_, v_n_275_, leanh::lean_box(0));
        return v___x_276_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_277_: *mut leanh::LeanObject,
    mut v_xs_278_: *mut leanh::LeanObject,
    mut v_motive_279_: *mut leanh::LeanObject,
    mut v_x_280_: *mut leanh::LeanObject,
    mut v_x_281_: *mut leanh::LeanObject,
    mut v_h__1_282_: *mut leanh::LeanObject,
    mut v_h__2_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_284_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_277_,
        v_xs_278_,
        v_motive_279_,
        v_x_280_,
        v_x_281_,
        v_h__1_282_,
        v_h__2_283_,
    );
    leanh::lean_dec(v_x_280_);
    leanh::lean_dec_ref(v_xs_278_);
    return v_res_284_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(
    mut v_r_285_: *mut leanh::LeanObject,
    mut v_h__1_286_: *mut leanh::LeanObject,
    mut v_h__2_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_285_) == 0 {
        let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_286_);
        v___x_288_ = leanh::lean_box(0);
        v___x_289_ = leanh::lean_apply_1(v_h__2_287_, v___x_288_);
        return v___x_289_;
    } else {
        let mut v_val_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_287_);
        v_val_290_ = leanh::lean_ctor_get(v_r_285_, 0);
        leanh::lean_inc(v_val_290_);
        leanh::lean_dec_ref_known(v_r_285_, 1);
        v___x_291_ = leanh::lean_apply_1(v_h__1_286_, v_val_290_);
        return v___x_291_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(
    mut v_00_u03b2_292_: *mut leanh::LeanObject,
    mut v_motive_293_: *mut leanh::LeanObject,
    mut v_r_294_: *mut leanh::LeanObject,
    mut v_h__1_295_: *mut leanh::LeanObject,
    mut v_h__2_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_294_) == 0 {
        let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_295_);
        v___x_297_ = leanh::lean_box(0);
        v___x_298_ = leanh::lean_apply_1(v_h__2_296_, v___x_297_);
        return v___x_298_;
    } else {
        let mut v_val_299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_296_);
        v_val_299_ = leanh::lean_ctor_get(v_r_294_, 0);
        leanh::lean_inc(v_val_299_);
        leanh::lean_dec_ref_known(v_r_294_, 1);
        v___x_300_ = leanh::lean_apply_1(v_h__1_295_, v_val_299_);
        return v___x_300_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
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
pub unsafe fn meta_initialize_Init_Internal_Order_Lemmas(
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
pub unsafe fn initialize_Init_Internal_Order_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Internal_Order_Lemmas(builtin);
}