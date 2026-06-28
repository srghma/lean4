// Lean compiler output
// Module: Init.Internal.Order.Lemmas
// Imports: Init.Data.List.Control Init.Data.Option.Basic Init.Data.Array.Basic Init.Internal.Order.Basic Init.Data.List.Monadic Init.Data.Array.Bootstrap
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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_151_: *mut LeanObject,
    mut v_h__1_152_: *mut LeanObject,
    mut v_h__2_153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_155_: u8 = 0;
    v_zero_154_ = lean_unsigned_to_nat(0);
    v_isZero_155_ = lean_nat_dec_eq(v_i_151_, v_zero_154_);
    if v_isZero_155_ == 1 {
        let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_153_);
        v___x_156_ = lean_apply_1(v_h__1_152_, lean_box(0));
        return v___x_156_;
    } else {
        let mut v_one_157_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_152_);
        v_one_157_ = lean_unsigned_to_nat(1);
        v_n_158_ = lean_nat_sub(v_i_151_, v_one_157_);
        v___x_159_ = lean_apply_2(v_h__2_153_, v_n_158_, lean_box(0));
        return v___x_159_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_160_: *mut LeanObject,
    mut v_h__1_161_: *mut LeanObject,
    mut v_h__2_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_163_: *mut LeanObject = core::ptr::null_mut();
    v_res_163_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_160_,
            v_h__1_161_,
            v_h__2_162_,
        );
    lean_dec(v_i_160_);
    return v_res_163_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_164_: *mut LeanObject,
    mut v_as_165_: *mut LeanObject,
    mut v_motive_166_: *mut LeanObject,
    mut v_i_167_: *mut LeanObject,
    mut v_h_168_: *mut LeanObject,
    mut v_h__1_169_: *mut LeanObject,
    mut v_h__2_170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_172_: u8 = 0;
    v_zero_171_ = lean_unsigned_to_nat(0);
    v_isZero_172_ = lean_nat_dec_eq(v_i_167_, v_zero_171_);
    if v_isZero_172_ == 1 {
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_170_);
        v___x_173_ = lean_apply_1(v_h__1_169_, lean_box(0));
        return v___x_173_;
    } else {
        let mut v_one_174_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_169_);
        v_one_174_ = lean_unsigned_to_nat(1);
        v_n_175_ = lean_nat_sub(v_i_167_, v_one_174_);
        v___x_176_ = lean_apply_2(v_h__2_170_, v_n_175_, lean_box(0));
        return v___x_176_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_177_: *mut LeanObject,
    mut v_as_178_: *mut LeanObject,
    mut v_motive_179_: *mut LeanObject,
    mut v_i_180_: *mut LeanObject,
    mut v_h_181_: *mut LeanObject,
    mut v_h__1_182_: *mut LeanObject,
    mut v_h__2_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_184_: *mut LeanObject = core::ptr::null_mut();
    v_res_184_ = l___private_Init_Internal_Order_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_177_,
        v_as_178_,
        v_motive_179_,
        v_i_180_,
        v_h_181_,
        v_h__1_182_,
        v_h__2_183_,
    );
    lean_dec(v_i_180_);
    lean_dec_ref(v_as_178_);
    return v_res_184_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(
    mut v_i_185_: *mut LeanObject,
    mut v_h__1_186_: *mut LeanObject,
    mut v_h__2_187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_189_: u8 = 0;
    v_zero_188_ = lean_unsigned_to_nat(0);
    v_isZero_189_ = lean_nat_dec_eq(v_i_185_, v_zero_188_);
    if v_isZero_189_ == 1 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_187_);
        v___x_190_ = lean_box(0);
        v___x_191_ = lean_apply_1(v_h__1_186_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_one_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_186_);
        v_one_192_ = lean_unsigned_to_nat(1);
        v_n_193_ = lean_nat_sub(v_i_185_, v_one_192_);
        v___x_194_ = lean_apply_1(v_h__2_187_, v_n_193_);
        return v___x_194_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(
    mut v_i_195_: *mut LeanObject,
    mut v_h__1_196_: *mut LeanObject,
    mut v_h__2_197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_198_: *mut LeanObject = core::ptr::null_mut();
    v_res_198_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(
            v_i_195_,
            v_h__1_196_,
            v_h__2_197_,
        );
    lean_dec(v_i_195_);
    return v_res_198_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(
    mut v_motive_199_: *mut LeanObject,
    mut v_i_200_: *mut LeanObject,
    mut v_h__1_201_: *mut LeanObject,
    mut v_h__2_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_204_: u8 = 0;
    v_zero_203_ = lean_unsigned_to_nat(0);
    v_isZero_204_ = lean_nat_dec_eq(v_i_200_, v_zero_203_);
    if v_isZero_204_ == 1 {
        let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_202_);
        v___x_205_ = lean_box(0);
        v___x_206_ = lean_apply_1(v_h__1_201_, v___x_205_);
        return v___x_206_;
    } else {
        let mut v_one_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_201_);
        v_one_207_ = lean_unsigned_to_nat(1);
        v_n_208_ = lean_nat_sub(v_i_200_, v_one_207_);
        v___x_209_ = lean_apply_1(v_h__2_202_, v_n_208_);
        return v___x_209_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(
    mut v_motive_210_: *mut LeanObject,
    mut v_i_211_: *mut LeanObject,
    mut v_h__1_212_: *mut LeanObject,
    mut v_h__2_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_214_: *mut LeanObject = core::ptr::null_mut();
    v_res_214_ = l___private_Init_Internal_Order_Lemmas_0__Array_foldlM_loop_match__1_splitter(
        v_motive_210_,
        v_i_211_,
        v_h__1_212_,
        v_h__2_213_,
    );
    lean_dec(v_i_211_);
    return v_res_214_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
    mut v_i_215_: *mut LeanObject,
    mut v_h__1_216_: *mut LeanObject,
    mut v_h__2_217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_219_: u8 = 0;
    v_zero_218_ = lean_unsigned_to_nat(0);
    v_isZero_219_ = lean_nat_dec_eq(v_i_215_, v_zero_218_);
    if v_isZero_219_ == 1 {
        let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_217_);
        v___x_220_ = lean_apply_1(v_h__1_216_, lean_box(0));
        return v___x_220_;
    } else {
        let mut v_one_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_216_);
        v_one_221_ = lean_unsigned_to_nat(1);
        v_n_222_ = lean_nat_sub(v_i_215_, v_one_221_);
        v___x_223_ = lean_apply_2(v_h__2_217_, v_n_222_, lean_box(0));
        return v___x_223_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(
    mut v_i_224_: *mut LeanObject,
    mut v_h__1_225_: *mut LeanObject,
    mut v_h__2_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_227_: *mut LeanObject = core::ptr::null_mut();
    v_res_227_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
            v_i_224_,
            v_h__1_225_,
            v_h__2_226_,
        );
    lean_dec(v_i_224_);
    return v_res_227_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter(
    mut v_00_u03b1_228_: *mut LeanObject,
    mut v_as_229_: *mut LeanObject,
    mut v_j_230_: *mut LeanObject,
    mut v_motive_231_: *mut LeanObject,
    mut v_i_232_: *mut LeanObject,
    mut v_inv_233_: *mut LeanObject,
    mut v_h__1_234_: *mut LeanObject,
    mut v_h__2_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_237_: u8 = 0;
    v_zero_236_ = lean_unsigned_to_nat(0);
    v_isZero_237_ = lean_nat_dec_eq(v_i_232_, v_zero_236_);
    if v_isZero_237_ == 1 {
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_235_);
        v___x_238_ = lean_apply_1(v_h__1_234_, lean_box(0));
        return v___x_238_;
    } else {
        let mut v_one_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_234_);
        v_one_239_ = lean_unsigned_to_nat(1);
        v_n_240_ = lean_nat_sub(v_i_232_, v_one_239_);
        v___x_241_ = lean_apply_2(v_h__2_235_, v_n_240_, lean_box(0));
        return v___x_241_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_mapFinIdxM_map_match__1_splitter___boxed(
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_as_243_: *mut LeanObject,
    mut v_j_244_: *mut LeanObject,
    mut v_motive_245_: *mut LeanObject,
    mut v_i_246_: *mut LeanObject,
    mut v_inv_247_: *mut LeanObject,
    mut v_h__1_248_: *mut LeanObject,
    mut v_h__2_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_250_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_i_246_);
    lean_dec(v_j_244_);
    lean_dec_ref(v_as_243_);
    return v_res_250_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_251_: *mut LeanObject,
    mut v_h__1_252_: *mut LeanObject,
    mut v_h__2_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_255_: u8 = 0;
    v_zero_254_ = lean_unsigned_to_nat(0);
    v_isZero_255_ = lean_nat_dec_eq(v_x_251_, v_zero_254_);
    if v_isZero_255_ == 1 {
        let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_253_);
        v___x_256_ = lean_apply_1(v_h__1_252_, lean_box(0));
        return v___x_256_;
    } else {
        let mut v_one_257_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_252_);
        v_one_257_ = lean_unsigned_to_nat(1);
        v_n_258_ = lean_nat_sub(v_x_251_, v_one_257_);
        v___x_259_ = lean_apply_2(v_h__2_253_, v_n_258_, lean_box(0));
        return v___x_259_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_260_: *mut LeanObject,
    mut v_h__1_261_: *mut LeanObject,
    mut v_h__2_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_263_: *mut LeanObject = core::ptr::null_mut();
    v_res_263_ =
        l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(
            v_x_260_,
            v_h__1_261_,
            v_h__2_262_,
        );
    lean_dec(v_x_260_);
    return v_res_263_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_264_: *mut LeanObject,
    mut v_xs_265_: *mut LeanObject,
    mut v_motive_266_: *mut LeanObject,
    mut v_x_267_: *mut LeanObject,
    mut v_x_268_: *mut LeanObject,
    mut v_h__1_269_: *mut LeanObject,
    mut v_h__2_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_272_: u8 = 0;
    v_zero_271_ = lean_unsigned_to_nat(0);
    v_isZero_272_ = lean_nat_dec_eq(v_x_267_, v_zero_271_);
    if v_isZero_272_ == 1 {
        let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_270_);
        v___x_273_ = lean_apply_1(v_h__1_269_, lean_box(0));
        return v___x_273_;
    } else {
        let mut v_one_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_269_);
        v_one_274_ = lean_unsigned_to_nat(1);
        v_n_275_ = lean_nat_sub(v_x_267_, v_one_274_);
        v___x_276_ = lean_apply_2(v_h__2_270_, v_n_275_, lean_box(0));
        return v___x_276_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_277_: *mut LeanObject,
    mut v_xs_278_: *mut LeanObject,
    mut v_motive_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
    mut v_h__1_282_: *mut LeanObject,
    mut v_h__2_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_284_: *mut LeanObject = core::ptr::null_mut();
    v_res_284_ = l___private_Init_Internal_Order_Lemmas_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_277_,
        v_xs_278_,
        v_motive_279_,
        v_x_280_,
        v_x_281_,
        v_h__1_282_,
        v_h__2_283_,
    );
    lean_dec(v_x_280_);
    lean_dec_ref(v_xs_278_);
    return v_res_284_;
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(
    mut v_r_285_: *mut LeanObject,
    mut v_h__1_286_: *mut LeanObject,
    mut v_h__2_287_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_285_) == 0 {
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_286_);
        v___x_288_ = lean_box(0);
        v___x_289_ = lean_apply_1(v_h__2_287_, v___x_288_);
        return v___x_289_;
    } else {
        let mut v_val_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_287_);
        v_val_290_ = lean_ctor_get(v_r_285_, 0);
        lean_inc(v_val_290_);
        lean_dec_ref_known(v_r_285_, 1);
        v___x_291_ = lean_apply_1(v_h__1_286_, v_val_290_);
        return v___x_291_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Lemmas_0__Array_findSomeRevM_x3f_find_match__1_splitter(
    mut v_00_u03b2_292_: *mut LeanObject,
    mut v_motive_293_: *mut LeanObject,
    mut v_r_294_: *mut LeanObject,
    mut v_h__1_295_: *mut LeanObject,
    mut v_h__2_296_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_294_) == 0 {
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_295_);
        v___x_297_ = lean_box(0);
        v___x_298_ = lean_apply_1(v_h__2_296_, v___x_297_);
        return v___x_298_;
    } else {
        let mut v_val_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_296_);
        v_val_299_ = lean_ctor_get(v_r_294_, 0);
        lean_inc(v_val_299_);
        lean_dec_ref_known(v_r_294_, 1);
        v___x_300_ = lean_apply_1(v_h__1_295_, v_val_299_);
        return v___x_300_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
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
pub unsafe fn meta_initialize_Init_Internal_Order_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Internal_Order_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Internal_Order_Lemmas(builtin);
}
