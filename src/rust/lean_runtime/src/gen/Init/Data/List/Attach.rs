// Lean compiler output
// Module: Init.Data.List.Attach
// Imports: Init.Data.List.Lemmas Init.Data.List.Lemmas Init.Data.List.Count Init.Data.Subtype.Basic
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::Count::{
    initialize_Init_Data_List_Count, runtime_initialize_Init_Data_List_Count,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub unsafe fn l_List_pmap___redArg(
    mut v_f_159_: *mut LeanObject,
    mut v_x_160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_166_: u8 = 0;
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_160_) == 0 {
                    lean_dec(v_f_159_);
                    v___x_161_ = lean_box(0);
                    return v___x_161_;
                } else {
                    v_head_162_ = lean_ctor_get(v_x_160_, 0);
                    v_tail_163_ = lean_ctor_get(v_x_160_, 1);
                    v_isSharedCheck_172_ = (!lean_is_exclusive(v_x_160_)) as u8;
                    if v_isSharedCheck_172_ == 0 {
                        v___x_165_ = v_x_160_;
                        v_isShared_166_ = v_isSharedCheck_172_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_163_);
                        lean_inc(v_head_162_);
                        lean_dec(v_x_160_);
                        v___x_165_ = lean_box(0);
                        v_isShared_166_ = v_isSharedCheck_172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_f_159_);
                v___x_167_ = lean_apply_2(v_f_159_, v_head_162_, lean_box(0));
                v___x_168_ = l_List_pmap___redArg(v_f_159_, v_tail_163_);
                if v_isShared_166_ == 0 {
                    lean_ctor_set(v___x_165_, 1, v___x_168_);
                    lean_ctor_set(v___x_165_, 0, v___x_167_);
                    v___x_170_ = v___x_165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
                    lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
                    v___x_170_ = v_reuseFailAlloc_171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_pmap(
    mut v_00_u03b1_173_: *mut LeanObject,
    mut v_00_u03b2_174_: *mut LeanObject,
    mut v_P_175_: *mut LeanObject,
    mut v_f_176_: *mut LeanObject,
    mut v_x_177_: *mut LeanObject,
    mut v_x_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    v___x_179_ = l_List_pmap___redArg(v_f_176_, v_x_177_);
    return v___x_179_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(
    mut v_l_180_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_l_180_);
    return v_l_180_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg___boxed(
    mut v_l_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_182_: *mut LeanObject = core::ptr::null_mut();
    v_res_182_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(v_l_181_);
    lean_dec(v_l_181_);
    return v_res_182_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl(
    mut v_00_u03b1_183_: *mut LeanObject,
    mut v_l_184_: *mut LeanObject,
    mut v_P_185_: *mut LeanObject,
    mut v_x_186_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_l_184_);
    return v_l_184_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl___boxed(
    mut v_00_u03b1_187_: *mut LeanObject,
    mut v_l_188_: *mut LeanObject,
    mut v_P_189_: *mut LeanObject,
    mut v_x_190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_191_: *mut LeanObject = core::ptr::null_mut();
    v_res_191_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl(
        v_00_u03b1_187_,
        v_l_188_,
        v_P_189_,
        v_x_190_,
    );
    lean_dec(v_l_188_);
    return v_res_191_;
}
pub unsafe fn l_List_attach___redArg(mut v_l_192_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_l_192_);
    return v_l_192_;
}
pub unsafe fn l_List_attach___redArg___boxed(mut v_l_193_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_194_: *mut LeanObject = core::ptr::null_mut();
    v_res_194_ = l_List_attach___redArg(v_l_193_);
    lean_dec(v_l_193_);
    return v_res_194_;
}
pub unsafe fn l_List_attach(
    mut v_00_u03b1_195_: *mut LeanObject,
    mut v_l_196_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_l_196_);
    return v_l_196_;
}
pub unsafe fn l_List_attach___boxed(
    mut v_00_u03b1_197_: *mut LeanObject,
    mut v_l_198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_199_: *mut LeanObject = core::ptr::null_mut();
    v_res_199_ = l_List_attach(v_00_u03b1_197_, v_l_198_);
    lean_dec(v_l_198_);
    return v_res_199_;
}
pub unsafe fn l_List_pmapImpl___redArg___lam__0(
    mut v_f_200_: *mut LeanObject,
    mut v_x_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    v___x_202_ = lean_apply_2(v_f_200_, v_x_201_, lean_box(0));
    return v___x_202_;
}
pub unsafe fn l_List_pmapImpl___redArg(
    mut v_f_203_: *mut LeanObject,
    mut v_l_204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    v___f_205_ = lean_alloc_closure(
        l_List_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_205_, 0, v_f_203_);
    v___x_206_ = lean_box(0);
    v___x_207_ = l_List_mapTR_loop___redArg(v___f_205_, v_l_204_, v___x_206_);
    return v___x_207_;
}
pub unsafe fn l_List_pmapImpl(
    mut v_00_u03b1_208_: *mut LeanObject,
    mut v_00_u03b2_209_: *mut LeanObject,
    mut v_P_210_: *mut LeanObject,
    mut v_f_211_: *mut LeanObject,
    mut v_l_212_: *mut LeanObject,
    mut v_H_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    v___f_214_ = lean_alloc_closure(
        l_List_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_214_, 0, v_f_211_);
    v___x_215_ = lean_box(0);
    v___x_216_ = l_List_mapTR_loop___redArg(v___f_214_, v_l_212_, v___x_215_);
    return v___x_216_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___redArg(
    mut v_x_217_: *mut LeanObject,
    mut v_h__1_218_: *mut LeanObject,
    mut v_h__2_219_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_219_);
        v___x_220_ = lean_apply_1(v_h__1_218_, lean_box(0));
        return v___x_220_;
    } else {
        let mut v_head_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_218_);
        v_head_221_ = lean_ctor_get(v_x_217_, 0);
        lean_inc(v_head_221_);
        v_tail_222_ = lean_ctor_get(v_x_217_, 1);
        lean_inc(v_tail_222_);
        lean_dec_ref_known(v_x_217_, 2);
        v___x_223_ = lean_apply_3(v_h__2_219_, v_head_221_, v_tail_222_, lean_box(0));
        return v___x_223_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter(
    mut v_00_u03b1_224_: *mut LeanObject,
    mut v_P_225_: *mut LeanObject,
    mut v_motive_226_: *mut LeanObject,
    mut v_x_227_: *mut LeanObject,
    mut v_x_228_: *mut LeanObject,
    mut v_h__1_229_: *mut LeanObject,
    mut v_h__2_230_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_227_) == 0 {
        let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_230_);
        v___x_231_ = lean_apply_1(v_h__1_229_, lean_box(0));
        return v___x_231_;
    } else {
        let mut v_head_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_229_);
        v_head_232_ = lean_ctor_get(v_x_227_, 0);
        lean_inc(v_head_232_);
        v_tail_233_ = lean_ctor_get(v_x_227_, 1);
        lean_inc(v_tail_233_);
        lean_dec_ref_known(v_x_227_, 2);
        v___x_234_ = lean_apply_3(v_h__2_230_, v_head_232_, v_tail_233_, lean_box(0));
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_235_: *mut LeanObject,
    mut v_h__1_236_: *mut LeanObject,
    mut v_h__2_237_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_235_) == 0 {
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_237_);
        v___x_238_ = lean_box(0);
        v___x_239_ = lean_apply_1(v_h__1_236_, v___x_238_);
        return v___x_239_;
    } else {
        let mut v_val_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_236_);
        v_val_240_ = lean_ctor_get(v_x_235_, 0);
        lean_inc(v_val_240_);
        lean_dec_ref_known(v_x_235_, 1);
        v___x_241_ = lean_apply_1(v_h__2_237_, v_val_240_);
        return v___x_241_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_242_: *mut LeanObject,
    mut v_motive_243_: *mut LeanObject,
    mut v_x_244_: *mut LeanObject,
    mut v_h__1_245_: *mut LeanObject,
    mut v_h__2_246_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_244_) == 0 {
        let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_246_);
        v___x_247_ = lean_box(0);
        v___x_248_ = lean_apply_1(v_h__1_245_, v___x_247_);
        return v___x_248_;
    } else {
        let mut v_val_249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_245_);
        v_val_249_ = lean_ctor_get(v_x_244_, 0);
        lean_inc(v_val_249_);
        lean_dec_ref_known(v_x_244_, 1);
        v___x_250_ = lean_apply_1(v_h__2_246_, v_val_249_);
        return v___x_250_;
    }
}
pub unsafe fn l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(
    mut v_a_251_: *mut LeanObject,
    mut v_a_252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_251_) == 0 {
                    v___x_253_ = l_List_reverse___redArg(v_a_252_);
                    return v___x_253_;
                } else {
                    v_head_254_ = lean_ctor_get(v_a_251_, 0);
                    v_tail_255_ = lean_ctor_get(v_a_251_, 1);
                    v_isSharedCheck_263_ = (!lean_is_exclusive(v_a_251_)) as u8;
                    if v_isSharedCheck_263_ == 0 {
                        v___x_257_ = v_a_251_;
                        v_isShared_258_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_255_);
                        lean_inc(v_head_254_);
                        lean_dec(v_a_251_);
                        v___x_257_ = lean_box(0);
                        v_isShared_258_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_258_ == 0 {
                    lean_ctor_set(v___x_257_, 1, v_a_252_);
                    v___x_260_ = v___x_257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_262_, 0, v_head_254_);
                    lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_252_);
                    v___x_260_ = v_reuseFailAlloc_262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_251_ = v_tail_255_;
                v_a_252_ = v___x_260_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_unattach___redArg(mut v_l_264_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_265_ = lean_box(0);
    v___x_266_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_l_264_, v___x_265_);
    return v___x_266_;
}
pub unsafe fn l_List_unattach(
    mut v_00_u03b1_267_: *mut LeanObject,
    mut v_p_268_: *mut LeanObject,
    mut v_l_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = l_List_unattach___redArg(v_l_269_);
    return v___x_270_;
}
pub unsafe fn l_List_mapTR_loop___at___00List_unattach_spec__0(
    mut v_00_u03b1_271_: *mut LeanObject,
    mut v_a_272_: *mut LeanObject,
    mut v_a_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    v___x_274_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_a_272_, v_a_273_);
    return v___x_274_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_275_: *mut LeanObject,
    mut v_h__1_276_: *mut LeanObject,
    mut v_h__2_277_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_275_) == 0 {
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_276_);
        v___x_278_ = lean_box(0);
        v___x_279_ = lean_apply_1(v_h__2_277_, v___x_278_);
        return v___x_279_;
    } else {
        let mut v_val_280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_277_);
        v_val_280_ = lean_ctor_get(v_x_275_, 0);
        lean_inc(v_val_280_);
        lean_dec_ref_known(v_x_275_, 1);
        v___x_281_ = lean_apply_1(v_h__1_276_, v_val_280_);
        return v___x_281_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_282_: *mut LeanObject,
    mut v_motive_283_: *mut LeanObject,
    mut v_x_284_: *mut LeanObject,
    mut v_h__1_285_: *mut LeanObject,
    mut v_h__2_286_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_284_) == 0 {
        let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_285_);
        v___x_287_ = lean_box(0);
        v___x_288_ = lean_apply_1(v_h__2_286_, v___x_287_);
        return v___x_288_;
    } else {
        let mut v_val_289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_286_);
        v_val_289_ = lean_ctor_get(v_x_284_, 0);
        lean_inc(v_val_289_);
        lean_dec_ref_known(v_x_284_, 1);
        v___x_290_ = lean_apply_1(v_h__1_285_, v_val_289_);
        return v___x_290_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(
    mut v_x_291_: u8,
    mut v_h__1_292_: *mut LeanObject,
    mut v_h__2_293_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_291_ == 0 {
        let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_292_);
        v___x_294_ = lean_box(0);
        v___x_295_ = lean_apply_1(v_h__2_293_, v___x_294_);
        return v___x_295_;
    } else {
        let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_293_);
        v___x_296_ = lean_box(0);
        v___x_297_ = lean_apply_1(v_h__1_292_, v___x_296_);
        return v___x_297_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_298_: *mut LeanObject,
    mut v_h__1_299_: *mut LeanObject,
    mut v_h__2_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_301_: u8 = 0;
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_301_ = (lean_unbox(v_x_298_) as u8);
    v_res_302_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_301_,
        v_h__1_299_,
        v_h__2_300_,
    );
    return v_res_302_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(
    mut v_motive_303_: *mut LeanObject,
    mut v_x_304_: u8,
    mut v_h__1_305_: *mut LeanObject,
    mut v_h__2_306_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_304_ == 0 {
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_305_);
        v___x_307_ = lean_box(0);
        v___x_308_ = lean_apply_1(v_h__2_306_, v___x_307_);
        return v___x_308_;
    } else {
        let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_306_);
        v___x_309_ = lean_box(0);
        v___x_310_ = lean_apply_1(v_h__1_305_, v___x_309_);
        return v___x_310_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___boxed(
    mut v_motive_311_: *mut LeanObject,
    mut v_x_312_: *mut LeanObject,
    mut v_h__1_313_: *mut LeanObject,
    mut v_h__2_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_315_: u8 = 0;
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_315_ = (lean_unbox(v_x_312_) as u8);
    v_res_316_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(
        v_motive_311_,
        v_x_37__boxed_315_,
        v_h__1_313_,
        v_h__2_314_,
    );
    return v_res_316_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Attach(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Attach(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Attach(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Attach(builtin);
}
