// Lean compiler output
// Module: Init.Data.Option.Instances
// Imports: Init.Data.Option.Basic
use crate::r#gen::Init::Data::Option::Basic::{
    initialize_Init_Data_Option_Basic, l_Option_instDecidableEq___redArg,
    runtime_initialize_Init_Data_Option_Basic,
};
pub unsafe fn l_Option_instMembership(
    mut v_00_u03b1_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_191_ = crate::leanh::lean_box(0);
    return v___x_191_;
}
pub unsafe fn l_Option_instDecidableMemOfDecidableEq___redArg(
    mut v_inst_192_: *mut crate::leanh::LeanObject,
    mut v_j_193_: *mut crate::leanh::LeanObject,
    mut v_o_194_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    v___x_195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_195_, 0, v_j_193_);
    v___x_196_ = l_Option_instDecidableEq___redArg(v_inst_192_, v_o_194_, v___x_195_);
    return v___x_196_;
}
pub unsafe fn l_Option_instDecidableMemOfDecidableEq___redArg___boxed(
    mut v_inst_197_: *mut crate::leanh::LeanObject,
    mut v_j_198_: *mut crate::leanh::LeanObject,
    mut v_o_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_200_: u8 = 0;
    let mut v_r_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_197_, v_j_198_, v_o_199_);
    v_r_201_ = crate::leanh::lean_box((v_res_200_) as usize);
    return v_r_201_;
}
pub unsafe fn l_Option_instDecidableMemOfDecidableEq(
    mut v_00_u03b1_202_: *mut crate::leanh::LeanObject,
    mut v_inst_203_: *mut crate::leanh::LeanObject,
    mut v_j_204_: *mut crate::leanh::LeanObject,
    mut v_o_205_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_206_: u8 = 0;
    v___x_206_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_203_, v_j_204_, v_o_205_);
    return v___x_206_;
}
pub unsafe fn l_Option_instDecidableMemOfDecidableEq___boxed(
    mut v_00_u03b1_207_: *mut crate::leanh::LeanObject,
    mut v_inst_208_: *mut crate::leanh::LeanObject,
    mut v_j_209_: *mut crate::leanh::LeanObject,
    mut v_o_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_211_: u8 = 0;
    let mut v_r_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ =
        l_Option_instDecidableMemOfDecidableEq(v_00_u03b1_207_, v_inst_208_, v_j_209_, v_o_210_);
    v_r_212_ = crate::leanh::lean_box((v_res_211_) as usize);
    return v_r_212_;
}
pub unsafe fn l_Option_decidableForallMem___redArg(
    mut v_inst_213_: *mut crate::leanh::LeanObject,
    mut v_x_214_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_214_) == 0 {
        let mut v___x_215_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_213_);
        v___x_215_ = 1;
        return v___x_215_;
    } else {
        let mut v_val_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: u8 = 0;
        v_val_216_ = crate::leanh::lean_ctor_get(v_x_214_, 0);
        crate::leanh::lean_inc(v_val_216_);
        crate::leanh::lean_dec_ref_known(v_x_214_, 1);
        v___x_217_ = crate::leanh::lean_apply_1(v_inst_213_, v_val_216_);
        v___x_218_ = (crate::leanh::lean_unbox(v___x_217_) as u8);
        return v___x_218_;
    }
}
pub unsafe fn l_Option_decidableForallMem___redArg___boxed(
    mut v_inst_219_: *mut crate::leanh::LeanObject,
    mut v_x_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_221_: u8 = 0;
    let mut v_r_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_221_ = l_Option_decidableForallMem___redArg(v_inst_219_, v_x_220_);
    v_r_222_ = crate::leanh::lean_box((v_res_221_) as usize);
    return v_r_222_;
}
pub unsafe fn l_Option_decidableForallMem(
    mut v_00_u03b1_223_: *mut crate::leanh::LeanObject,
    mut v_p_224_: *mut crate::leanh::LeanObject,
    mut v_inst_225_: *mut crate::leanh::LeanObject,
    mut v_x_226_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_227_: u8 = 0;
    v___x_227_ = l_Option_decidableForallMem___redArg(v_inst_225_, v_x_226_);
    return v___x_227_;
}
pub unsafe fn l_Option_decidableForallMem___boxed(
    mut v_00_u03b1_228_: *mut crate::leanh::LeanObject,
    mut v_p_229_: *mut crate::leanh::LeanObject,
    mut v_inst_230_: *mut crate::leanh::LeanObject,
    mut v_x_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_232_: u8 = 0;
    let mut v_r_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_232_ = l_Option_decidableForallMem(v_00_u03b1_228_, v_p_229_, v_inst_230_, v_x_231_);
    v_r_233_ = crate::leanh::lean_box((v_res_232_) as usize);
    return v_r_233_;
}
pub unsafe fn l_Option_decidableExistsMem___redArg(
    mut v_inst_234_: *mut crate::leanh::LeanObject,
    mut v_x_235_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_235_) == 0 {
        let mut v___x_236_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_234_);
        v___x_236_ = 0;
        return v___x_236_;
    } else {
        let mut v_val_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: u8 = 0;
        v_val_237_ = crate::leanh::lean_ctor_get(v_x_235_, 0);
        crate::leanh::lean_inc(v_val_237_);
        crate::leanh::lean_dec_ref_known(v_x_235_, 1);
        v___x_238_ = crate::leanh::lean_apply_1(v_inst_234_, v_val_237_);
        v___x_239_ = (crate::leanh::lean_unbox(v___x_238_) as u8);
        return v___x_239_;
    }
}
pub unsafe fn l_Option_decidableExistsMem___redArg___boxed(
    mut v_inst_240_: *mut crate::leanh::LeanObject,
    mut v_x_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_242_: u8 = 0;
    let mut v_r_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Option_decidableExistsMem___redArg(v_inst_240_, v_x_241_);
    v_r_243_ = crate::leanh::lean_box((v_res_242_) as usize);
    return v_r_243_;
}
pub unsafe fn l_Option_decidableExistsMem(
    mut v_00_u03b1_244_: *mut crate::leanh::LeanObject,
    mut v_p_245_: *mut crate::leanh::LeanObject,
    mut v_inst_246_: *mut crate::leanh::LeanObject,
    mut v_x_247_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_248_: u8 = 0;
    v___x_248_ = l_Option_decidableExistsMem___redArg(v_inst_246_, v_x_247_);
    return v___x_248_;
}
pub unsafe fn l_Option_decidableExistsMem___boxed(
    mut v_00_u03b1_249_: *mut crate::leanh::LeanObject,
    mut v_p_250_: *mut crate::leanh::LeanObject,
    mut v_inst_251_: *mut crate::leanh::LeanObject,
    mut v_x_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_253_: u8 = 0;
    let mut v_r_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_253_ = l_Option_decidableExistsMem(v_00_u03b1_249_, v_p_250_, v_inst_251_, v_x_252_);
    v_r_254_ = crate::leanh::lean_box((v_res_253_) as usize);
    return v_r_254_;
}
pub unsafe fn l_Option_pbind___redArg(
    mut v_x_255_: *mut crate::leanh::LeanObject,
    mut v_x_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_255_) == 0 {
        let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_x_256_);
        v___x_257_ = crate::leanh::lean_box(0);
        return v___x_257_;
    } else {
        let mut v_val_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_258_ = crate::leanh::lean_ctor_get(v_x_255_, 0);
        crate::leanh::lean_inc(v_val_258_);
        crate::leanh::lean_dec_ref_known(v_x_255_, 1);
        v___x_259_ = crate::leanh::lean_apply_2(v_x_256_, v_val_258_, crate::leanh::lean_box(0));
        return v___x_259_;
    }
}
pub unsafe fn l_Option_pbind(
    mut v_00_u03b1_260_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_261_: *mut crate::leanh::LeanObject,
    mut v_x_262_: *mut crate::leanh::LeanObject,
    mut v_x_263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_262_) == 0 {
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_x_263_);
        v___x_264_ = crate::leanh::lean_box(0);
        return v___x_264_;
    } else {
        let mut v_val_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_265_ = crate::leanh::lean_ctor_get(v_x_262_, 0);
        crate::leanh::lean_inc(v_val_265_);
        crate::leanh::lean_dec_ref_known(v_x_262_, 1);
        v___x_266_ = crate::leanh::lean_apply_2(v_x_263_, v_val_265_, crate::leanh::lean_box(0));
        return v___x_266_;
    }
}
pub unsafe fn l_Option_pmap___redArg(
    mut v_f_267_: *mut crate::leanh::LeanObject,
    mut v_x_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_273_: u8 = 0;
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_268_) == 0 {
                    crate::leanh::lean_dec(v_f_267_);
                    v___x_269_ = crate::leanh::lean_box(0);
                    return v___x_269_;
                } else {
                    v_val_270_ = crate::leanh::lean_ctor_get(v_x_268_, 0);
                    v_isSharedCheck_278_ = (!crate::leanh::lean_is_exclusive(v_x_268_)) as u8;
                    if v_isSharedCheck_278_ == 0 {
                        v___x_272_ = v_x_268_;
                        v_isShared_273_ = v_isSharedCheck_278_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_270_);
                        crate::leanh::lean_dec(v_x_268_);
                        v___x_272_ = crate::leanh::lean_box(0);
                        v_isShared_273_ = v_isSharedCheck_278_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_274_ =
                    crate::leanh::lean_apply_2(v_f_267_, v_val_270_, crate::leanh::lean_box(0));
                if v_isShared_273_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_272_, 0, v___x_274_);
                    v___x_276_ = v___x_272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
                    v___x_276_ = v_reuseFailAlloc_277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_pmap(
    mut v_00_u03b1_279_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_280_: *mut crate::leanh::LeanObject,
    mut v_p_281_: *mut crate::leanh::LeanObject,
    mut v_f_282_: *mut crate::leanh::LeanObject,
    mut v_x_283_: *mut crate::leanh::LeanObject,
    mut v_x_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_289_: u8 = 0;
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_283_) == 0 {
                    crate::leanh::lean_dec(v_f_282_);
                    v___x_285_ = crate::leanh::lean_box(0);
                    return v___x_285_;
                } else {
                    v_val_286_ = crate::leanh::lean_ctor_get(v_x_283_, 0);
                    v_isSharedCheck_294_ = (!crate::leanh::lean_is_exclusive(v_x_283_)) as u8;
                    if v_isSharedCheck_294_ == 0 {
                        v___x_288_ = v_x_283_;
                        v_isShared_289_ = v_isSharedCheck_294_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_286_);
                        crate::leanh::lean_dec(v_x_283_);
                        v___x_288_ = crate::leanh::lean_box(0);
                        v_isShared_289_ = v_isSharedCheck_294_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_290_ =
                    crate::leanh::lean_apply_2(v_f_282_, v_val_286_, crate::leanh::lean_box(0));
                if v_isShared_289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_288_, 0, v___x_290_);
                    v___x_292_ = v___x_288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
                    v___x_292_ = v_reuseFailAlloc_293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_pelim___redArg(
    mut v_o_295_: *mut crate::leanh::LeanObject,
    mut v_b_296_: *mut crate::leanh::LeanObject,
    mut v_f_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_295_) == 0 {
        crate::leanh::lean_dec(v_f_297_);
        crate::leanh::lean_inc(v_b_296_);
        return v_b_296_;
    } else {
        let mut v_val_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_298_ = crate::leanh::lean_ctor_get(v_o_295_, 0);
        crate::leanh::lean_inc(v_val_298_);
        crate::leanh::lean_dec_ref_known(v_o_295_, 1);
        v___x_299_ = crate::leanh::lean_apply_2(v_f_297_, v_val_298_, crate::leanh::lean_box(0));
        return v___x_299_;
    }
}
pub unsafe fn l_Option_pelim___redArg___boxed(
    mut v_o_300_: *mut crate::leanh::LeanObject,
    mut v_b_301_: *mut crate::leanh::LeanObject,
    mut v_f_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Option_pelim___redArg(v_o_300_, v_b_301_, v_f_302_);
    crate::leanh::lean_dec(v_b_301_);
    return v_res_303_;
}
pub unsafe fn l_Option_pelim(
    mut v_00_u03b1_304_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_305_: *mut crate::leanh::LeanObject,
    mut v_o_306_: *mut crate::leanh::LeanObject,
    mut v_b_307_: *mut crate::leanh::LeanObject,
    mut v_f_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_306_) == 0 {
        crate::leanh::lean_dec(v_f_308_);
        crate::leanh::lean_inc(v_b_307_);
        return v_b_307_;
    } else {
        let mut v_val_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_309_ = crate::leanh::lean_ctor_get(v_o_306_, 0);
        crate::leanh::lean_inc(v_val_309_);
        crate::leanh::lean_dec_ref_known(v_o_306_, 1);
        v___x_310_ = crate::leanh::lean_apply_2(v_f_308_, v_val_309_, crate::leanh::lean_box(0));
        return v___x_310_;
    }
}
pub unsafe fn l_Option_pelim___boxed(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_312_: *mut crate::leanh::LeanObject,
    mut v_o_313_: *mut crate::leanh::LeanObject,
    mut v_b_314_: *mut crate::leanh::LeanObject,
    mut v_f_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Option_pelim(
        v_00_u03b1_311_,
        v_00_u03b2_312_,
        v_o_313_,
        v_b_314_,
        v_f_315_,
    );
    crate::leanh::lean_dec(v_b_314_);
    return v_res_316_;
}
pub unsafe fn l_Option_pfilter___redArg(
    mut v_o_317_: *mut crate::leanh::LeanObject,
    mut v_p_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_317_) == 0 {
        crate::leanh::lean_dec_ref(v_p_318_);
        return v_o_317_;
    } else {
        let mut v_val_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_321_: u8 = 0;
        v_val_319_ = crate::leanh::lean_ctor_get(v_o_317_, 0);
        crate::leanh::lean_inc(v_val_319_);
        v___x_320_ = crate::leanh::lean_apply_2(v_p_318_, v_val_319_, crate::leanh::lean_box(0));
        v___x_321_ = (crate::leanh::lean_unbox(v___x_320_) as u8);
        if v___x_321_ == 0 {
            let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_o_317_, 1);
            v___x_322_ = crate::leanh::lean_box(0);
            return v___x_322_;
        } else {
            return v_o_317_;
        }
    }
}
pub unsafe fn l_Option_pfilter(
    mut v_00_u03b1_323_: *mut crate::leanh::LeanObject,
    mut v_o_324_: *mut crate::leanh::LeanObject,
    mut v_p_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_324_) == 0 {
        crate::leanh::lean_dec_ref(v_p_325_);
        return v_o_324_;
    } else {
        let mut v_val_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: u8 = 0;
        v_val_326_ = crate::leanh::lean_ctor_get(v_o_324_, 0);
        crate::leanh::lean_inc(v_val_326_);
        v___x_327_ = crate::leanh::lean_apply_2(v_p_325_, v_val_326_, crate::leanh::lean_box(0));
        v___x_328_ = (crate::leanh::lean_unbox(v___x_327_) as u8);
        if v___x_328_ == 0 {
            let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_o_324_, 1);
            v___x_329_ = crate::leanh::lean_box(0);
            return v___x_329_;
        } else {
            return v_o_324_;
        }
    }
}
pub unsafe fn l_Option_forM___redArg(
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_x_331_: *mut crate::leanh::LeanObject,
    mut v_x_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_331_) == 0 {
        let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_332_);
        v___x_333_ = crate::leanh::lean_box(0);
        v___x_334_ = crate::leanh::lean_apply_2(v_inst_330_, crate::leanh::lean_box(0), v___x_333_);
        return v___x_334_;
    } else {
        let mut v_val_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_330_);
        v_val_335_ = crate::leanh::lean_ctor_get(v_x_331_, 0);
        crate::leanh::lean_inc(v_val_335_);
        crate::leanh::lean_dec_ref_known(v_x_331_, 1);
        v___x_336_ = crate::leanh::lean_apply_1(v_x_332_, v_val_335_);
        return v___x_336_;
    }
}
pub unsafe fn l_Option_forM(
    mut v_m_337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_x_340_: *mut crate::leanh::LeanObject,
    mut v_x_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_340_) == 0 {
        let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_341_);
        v___x_342_ = crate::leanh::lean_box(0);
        v___x_343_ = crate::leanh::lean_apply_2(v_inst_339_, crate::leanh::lean_box(0), v___x_342_);
        return v___x_343_;
    } else {
        let mut v_val_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_339_);
        v_val_344_ = crate::leanh::lean_ctor_get(v_x_340_, 0);
        crate::leanh::lean_inc(v_val_344_);
        crate::leanh::lean_dec_ref_known(v_x_340_, 1);
        v___x_345_ = crate::leanh::lean_apply_1(v_x_341_, v_val_344_);
        return v___x_345_;
    }
}
pub unsafe fn l_Option_instForMOfMonad___redArg(
    mut v_inst_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_347_ = crate::leanh::lean_ctor_get(v_inst_346_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_347_);
    crate::leanh::lean_dec_ref(v_inst_346_);
    v_toPure_348_ = crate::leanh::lean_ctor_get(v_toApplicative_347_, 1);
    crate::leanh::lean_inc(v_toPure_348_);
    crate::leanh::lean_dec_ref(v_toApplicative_347_);
    v___x_349_ = crate::leanh::lean_alloc_closure(l_Option_forM as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_349_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_349_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_349_, 2, v_toPure_348_);
    return v___x_349_;
}
pub unsafe fn l_Option_instForMOfMonad(
    mut v_m_350_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_351_: *mut crate::leanh::LeanObject,
    mut v_inst_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = l_Option_instForMOfMonad___redArg(v_inst_352_);
    return v___x_353_;
}
pub unsafe fn l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
    mut v_toPure_354_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_356_ = crate::leanh::lean_ctor_get(v_____do__lift_355_, 0);
    crate::leanh::lean_inc(v_a_356_);
    crate::leanh::lean_dec_ref(v_____do__lift_355_);
    v___x_357_ = crate::leanh::lean_apply_2(v_toPure_354_, crate::leanh::lean_box(0), v_a_356_);
    return v___x_357_;
}
pub unsafe fn l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(
    mut v_toPure_358_: *mut crate::leanh::LeanObject,
    mut v_toBind_359_: *mut crate::leanh::LeanObject,
    mut v___f_360_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_361_: *mut crate::leanh::LeanObject,
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v_init_363_: *mut crate::leanh::LeanObject,
    mut v_f_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_362_) == 0 {
        let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_364_);
        crate::leanh::lean_dec(v___f_360_);
        crate::leanh::lean_dec(v_toBind_359_);
        v___x_365_ =
            crate::leanh::lean_apply_2(v_toPure_358_, crate::leanh::lean_box(0), v_init_363_);
        return v___x_365_;
    } else {
        let mut v_val_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_358_);
        v_val_366_ = crate::leanh::lean_ctor_get(v_x_362_, 0);
        crate::leanh::lean_inc(v_val_366_);
        crate::leanh::lean_dec_ref_known(v_x_362_, 1);
        v___x_367_ = crate::leanh::lean_apply_3(
            v_f_364_,
            v_val_366_,
            crate::leanh::lean_box(0),
            v_init_363_,
        );
        v___x_368_ = crate::leanh::lean_apply_4(
            v_toBind_359_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_367_,
            v___f_360_,
        );
        return v___x_368_;
    }
}
pub unsafe fn l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(
    mut v_inst_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_370_ = crate::leanh::lean_ctor_get(v_inst_369_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_370_);
    v_toBind_371_ = crate::leanh::lean_ctor_get(v_inst_369_, 1);
    crate::leanh::lean_inc(v_toBind_371_);
    crate::leanh::lean_dec_ref(v_inst_369_);
    v_toPure_372_ = crate::leanh::lean_ctor_get(v_toApplicative_370_, 1);
    crate::leanh::lean_inc_n(v_toPure_372_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_370_);
    v___f_373_ = crate::leanh::lean_alloc_closure(
        l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_373_, 0, v_toPure_372_);
    v___f_374_ = crate::leanh::lean_alloc_closure(
        l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_374_, 0, v_toPure_372_);
    crate::leanh::lean_closure_set(v___f_374_, 1, v_toBind_371_);
    crate::leanh::lean_closure_set(v___f_374_, 2, v___f_373_);
    return v___f_374_;
}
pub unsafe fn l_Option_instForIn_x27InferInstanceMembershipOfMonad(
    mut v_m_375_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_376_: *mut crate::leanh::LeanObject,
    mut v_inst_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_378_ = l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(v_inst_377_);
    return v___x_378_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Instances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Instances(
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
pub unsafe fn initialize_Init_Data_Option_Instances(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Instances(builtin);
}
