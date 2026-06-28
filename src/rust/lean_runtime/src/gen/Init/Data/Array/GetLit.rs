// Lean compiler output
// Module: Init.Data.Array.GetLit
// Imports: Init.GetElem Init.Data.Array.Basic
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_mk, lean_nat_dec_eq, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l_Array_getLit___redArg(
    mut v_xs_151_: *mut LeanObject,
    mut v_i_152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    v___x_153_ = lean_array_fget_borrowed(v_xs_151_, v_i_152_);
    lean_inc(v___x_153_);
    return v___x_153_;
}
pub unsafe fn l_Array_getLit___redArg___boxed(
    mut v_xs_154_: *mut LeanObject,
    mut v_i_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_156_: *mut LeanObject = core::ptr::null_mut();
    v_res_156_ = l_Array_getLit___redArg(v_xs_154_, v_i_155_);
    lean_dec(v_i_155_);
    lean_dec_ref(v_xs_154_);
    return v_res_156_;
}
pub unsafe fn l_Array_getLit(
    mut v_00_u03b1_157_: *mut LeanObject,
    mut v_n_158_: *mut LeanObject,
    mut v_xs_159_: *mut LeanObject,
    mut v_i_160_: *mut LeanObject,
    mut v_h_u2081_161_: *mut LeanObject,
    mut v_h_u2082_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    v___x_163_ = lean_array_fget_borrowed(v_xs_159_, v_i_160_);
    lean_inc(v___x_163_);
    return v___x_163_;
}
pub unsafe fn l_Array_getLit___boxed(
    mut v_00_u03b1_164_: *mut LeanObject,
    mut v_n_165_: *mut LeanObject,
    mut v_xs_166_: *mut LeanObject,
    mut v_i_167_: *mut LeanObject,
    mut v_h_u2081_168_: *mut LeanObject,
    mut v_h_u2082_169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_170_: *mut LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Array_getLit(
        v_00_u03b1_164_,
        v_n_165_,
        v_xs_166_,
        v_i_167_,
        v_h_u2081_168_,
        v_h_u2082_169_,
    );
    lean_dec(v_i_167_);
    lean_dec_ref(v_xs_166_);
    lean_dec(v_n_165_);
    return v_res_170_;
}
pub unsafe fn l_Array_toListLitAux___redArg(
    mut v_xs_171_: *mut LeanObject,
    mut v_x_172_: *mut LeanObject,
    mut v_x_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_175_: u8 = 0;
    let mut v_one_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_174_ = lean_unsigned_to_nat(0);
                v_isZero_175_ = lean_nat_dec_eq(v_x_172_, v_zero_174_);
                if v_isZero_175_ == 1 {
                    lean_dec(v_x_172_);
                    return v_x_173_;
                } else {
                    v_one_176_ = lean_unsigned_to_nat(1);
                    v_n_177_ = lean_nat_sub(v_x_172_, v_one_176_);
                    lean_dec(v_x_172_);
                    v___x_178_ = lean_array_fget_borrowed(v_xs_171_, v_n_177_);
                    lean_inc(v___x_178_);
                    v___x_179_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_179_, 0, v___x_178_);
                    lean_ctor_set(v___x_179_, 1, v_x_173_);
                    v_x_172_ = v_n_177_;
                    v_x_173_ = v___x_179_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_toListLitAux___redArg___boxed(
    mut v_xs_181_: *mut LeanObject,
    mut v_x_182_: *mut LeanObject,
    mut v_x_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_184_: *mut LeanObject = core::ptr::null_mut();
    v_res_184_ = l_Array_toListLitAux___redArg(v_xs_181_, v_x_182_, v_x_183_);
    lean_dec_ref(v_xs_181_);
    return v_res_184_;
}
pub unsafe fn l_Array_toListLitAux(
    mut v_00_u03b1_185_: *mut LeanObject,
    mut v_xs_186_: *mut LeanObject,
    mut v_n_187_: *mut LeanObject,
    mut v_hsz_188_: *mut LeanObject,
    mut v_x_189_: *mut LeanObject,
    mut v_x_190_: *mut LeanObject,
    mut v_x_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_192_ = l_Array_toListLitAux___redArg(v_xs_186_, v_x_189_, v_x_191_);
    return v___x_192_;
}
pub unsafe fn l_Array_toListLitAux___boxed(
    mut v_00_u03b1_193_: *mut LeanObject,
    mut v_xs_194_: *mut LeanObject,
    mut v_n_195_: *mut LeanObject,
    mut v_hsz_196_: *mut LeanObject,
    mut v_x_197_: *mut LeanObject,
    mut v_x_198_: *mut LeanObject,
    mut v_x_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_200_: *mut LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Array_toListLitAux(
        v_00_u03b1_193_,
        v_xs_194_,
        v_n_195_,
        v_hsz_196_,
        v_x_197_,
        v_x_198_,
        v_x_199_,
    );
    lean_dec(v_n_195_);
    lean_dec_ref(v_xs_194_);
    return v_res_200_;
}
pub unsafe fn l_Array_toArrayLit___redArg(
    mut v_xs_201_: *mut LeanObject,
    mut v_n_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v___x_203_ = lean_box(0);
    v___x_204_ = l_Array_toListLitAux___redArg(v_xs_201_, v_n_202_, v___x_203_);
    v___x_205_ = lean_array_mk(v___x_204_);
    return v___x_205_;
}
pub unsafe fn l_Array_toArrayLit___redArg___boxed(
    mut v_xs_206_: *mut LeanObject,
    mut v_n_207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_208_: *mut LeanObject = core::ptr::null_mut();
    v_res_208_ = l_Array_toArrayLit___redArg(v_xs_206_, v_n_207_);
    lean_dec_ref(v_xs_206_);
    return v_res_208_;
}
pub unsafe fn l_Array_toArrayLit(
    mut v_00_u03b1_209_: *mut LeanObject,
    mut v_xs_210_: *mut LeanObject,
    mut v_n_211_: *mut LeanObject,
    mut v_hsz_212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    v___x_213_ = l_Array_toArrayLit___redArg(v_xs_210_, v_n_211_);
    return v___x_213_;
}
pub unsafe fn l_Array_toArrayLit___boxed(
    mut v_00_u03b1_214_: *mut LeanObject,
    mut v_xs_215_: *mut LeanObject,
    mut v_n_216_: *mut LeanObject,
    mut v_hsz_217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_218_: *mut LeanObject = core::ptr::null_mut();
    v_res_218_ = l_Array_toArrayLit(v_00_u03b1_214_, v_xs_215_, v_n_216_, v_hsz_217_);
    lean_dec_ref(v_xs_215_);
    return v_res_218_;
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg(
    mut v_x_219_: *mut LeanObject,
    mut v_x_220_: *mut LeanObject,
    mut v_h__1_221_: *mut LeanObject,
    mut v_h__2_222_: *mut LeanObject,
    mut v_h__3_223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_225_: u8 = 0;
    v_zero_224_ = lean_unsigned_to_nat(0);
    v_isZero_225_ = lean_nat_dec_eq(v_x_219_, v_zero_224_);
    if v_isZero_225_ == 1 {
        let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_223_);
        lean_dec(v_h__2_222_);
        v___x_226_ = lean_apply_1(v_h__1_221_, v_x_220_);
        return v___x_226_;
    } else {
        let mut v_one_227_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_228_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_221_);
        v_one_227_ = lean_unsigned_to_nat(1);
        v_n_228_ = lean_nat_sub(v_x_219_, v_one_227_);
        if lean_obj_tag(v_x_220_) == 0 {
            let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_223_);
            v___x_229_ = lean_apply_1(v_h__2_222_, v_n_228_);
            return v___x_229_;
        } else {
            let mut v_head_230_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_222_);
            v_head_230_ = lean_ctor_get(v_x_220_, 0);
            lean_inc(v_head_230_);
            v_tail_231_ = lean_ctor_get(v_x_220_, 1);
            lean_inc(v_tail_231_);
            lean_dec_ref_known(v_x_220_, 2);
            v___x_232_ = lean_apply_3(v_h__3_223_, v_n_228_, v_head_230_, v_tail_231_);
            return v___x_232_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_233_: *mut LeanObject,
    mut v_x_234_: *mut LeanObject,
    mut v_h__1_235_: *mut LeanObject,
    mut v_h__2_236_: *mut LeanObject,
    mut v_h__3_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___redArg(
        v_x_233_,
        v_x_234_,
        v_h__1_235_,
        v_h__2_236_,
        v_h__3_237_,
    );
    lean_dec(v_x_233_);
    return v_res_238_;
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter(
    mut v_00_u03b1_239_: *mut LeanObject,
    mut v_motive_240_: *mut LeanObject,
    mut v_x_241_: *mut LeanObject,
    mut v_x_242_: *mut LeanObject,
    mut v_h__1_243_: *mut LeanObject,
    mut v_h__2_244_: *mut LeanObject,
    mut v_h__3_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_247_: u8 = 0;
    v_zero_246_ = lean_unsigned_to_nat(0);
    v_isZero_247_ = lean_nat_dec_eq(v_x_241_, v_zero_246_);
    if v_isZero_247_ == 1 {
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_245_);
        lean_dec(v_h__2_244_);
        v___x_248_ = lean_apply_1(v_h__1_243_, v_x_242_);
        return v___x_248_;
    } else {
        let mut v_one_249_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_250_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_243_);
        v_one_249_ = lean_unsigned_to_nat(1);
        v_n_250_ = lean_nat_sub(v_x_241_, v_one_249_);
        if lean_obj_tag(v_x_242_) == 0 {
            let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_245_);
            v___x_251_ = lean_apply_1(v_h__2_244_, v_n_250_);
            return v___x_251_;
        } else {
            let mut v_head_252_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_253_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_244_);
            v_head_252_ = lean_ctor_get(v_x_242_, 0);
            lean_inc(v_head_252_);
            v_tail_253_ = lean_ctor_get(v_x_242_, 1);
            lean_inc(v_tail_253_);
            lean_dec_ref_known(v_x_242_, 2);
            v___x_254_ = lean_apply_3(v_h__3_245_, v_n_250_, v_head_252_, v_tail_253_);
            return v___x_254_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_255_: *mut LeanObject,
    mut v_motive_256_: *mut LeanObject,
    mut v_x_257_: *mut LeanObject,
    mut v_x_258_: *mut LeanObject,
    mut v_h__1_259_: *mut LeanObject,
    mut v_h__2_260_: *mut LeanObject,
    mut v_h__3_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_262_: *mut LeanObject = core::ptr::null_mut();
    v_res_262_ = l___private_Init_Data_Array_GetLit_0__List_take_match__1_splitter(
        v_00_u03b1_255_,
        v_motive_256_,
        v_x_257_,
        v_x_258_,
        v_h__1_259_,
        v_h__2_260_,
        v_h__3_261_,
    );
    lean_dec(v_x_257_);
    return v_res_262_;
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg(
    mut v_x_263_: *mut LeanObject,
    mut v_x_264_: *mut LeanObject,
    mut v_h__1_265_: *mut LeanObject,
    mut v_h__2_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_268_: u8 = 0;
    v_zero_267_ = lean_unsigned_to_nat(0);
    v_isZero_268_ = lean_nat_dec_eq(v_x_263_, v_zero_267_);
    if v_isZero_268_ == 1 {
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_266_);
        v___x_269_ = lean_apply_2(v_h__1_265_, lean_box(0), v_x_264_);
        return v___x_269_;
    } else {
        let mut v_one_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_265_);
        v_one_270_ = lean_unsigned_to_nat(1);
        v_n_271_ = lean_nat_sub(v_x_263_, v_one_270_);
        v___x_272_ = lean_apply_3(v_h__2_266_, v_n_271_, lean_box(0), v_x_264_);
        return v___x_272_;
    }
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg___boxed(
    mut v_x_273_: *mut LeanObject,
    mut v_x_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_277_: *mut LeanObject = core::ptr::null_mut();
    v_res_277_ =
        l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___redArg(
            v_x_273_,
            v_x_274_,
            v_h__1_275_,
            v_h__2_276_,
        );
    lean_dec(v_x_273_);
    return v_res_277_;
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter(
    mut v_00_u03b1_278_: *mut LeanObject,
    mut v_xs_279_: *mut LeanObject,
    mut v_motive_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
    mut v_x_282_: *mut LeanObject,
    mut v_x_283_: *mut LeanObject,
    mut v_h__1_284_: *mut LeanObject,
    mut v_h__2_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_287_: u8 = 0;
    v_zero_286_ = lean_unsigned_to_nat(0);
    v_isZero_287_ = lean_nat_dec_eq(v_x_281_, v_zero_286_);
    if v_isZero_287_ == 1 {
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_285_);
        v___x_288_ = lean_apply_2(v_h__1_284_, lean_box(0), v_x_283_);
        return v___x_288_;
    } else {
        let mut v_one_289_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_284_);
        v_one_289_ = lean_unsigned_to_nat(1);
        v_n_290_ = lean_nat_sub(v_x_281_, v_one_289_);
        v___x_291_ = lean_apply_3(v_h__2_285_, v_n_290_, lean_box(0), v_x_283_);
        return v___x_291_;
    }
}
pub unsafe fn l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter___boxed(
    mut v_00_u03b1_292_: *mut LeanObject,
    mut v_xs_293_: *mut LeanObject,
    mut v_motive_294_: *mut LeanObject,
    mut v_x_295_: *mut LeanObject,
    mut v_x_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
    mut v_h__1_298_: *mut LeanObject,
    mut v_h__2_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_300_: *mut LeanObject = core::ptr::null_mut();
    v_res_300_ = l___private_Init_Data_Array_GetLit_0__Array_toListLitAux_match__1_splitter(
        v_00_u03b1_292_,
        v_xs_293_,
        v_motive_294_,
        v_x_295_,
        v_x_296_,
        v_x_297_,
        v_h__1_298_,
        v_h__2_299_,
    );
    lean_dec(v_x_295_);
    lean_dec_ref(v_xs_293_);
    return v_res_300_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_GetLit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_GetLit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_GetLit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_GetLit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_GetLit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_GetLit(builtin);
}
