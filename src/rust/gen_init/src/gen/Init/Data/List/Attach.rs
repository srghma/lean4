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
pub unsafe fn l_List_pmap___redArg(
    mut v_f_159_: *mut leanh::LeanObject,
    mut v_x_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_166_: u8 = 0;
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_160_) == 0 {
                    leanh::lean_dec(v_f_159_);
                    v___x_161_ = leanh::lean_box(0);
                    return v___x_161_;
                } else {
                    v_head_162_ = leanh::lean_ctor_get(v_x_160_, 0);
                    v_tail_163_ = leanh::lean_ctor_get(v_x_160_, 1);
                    v_isSharedCheck_172_ = (!leanh::lean_is_exclusive(v_x_160_)) as u8;
                    if v_isSharedCheck_172_ == 0 {
                        v___x_165_ = v_x_160_;
                        v_isShared_166_ = v_isSharedCheck_172_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_163_);
                        leanh::lean_inc(v_head_162_);
                        leanh::lean_dec(v_x_160_);
                        v___x_165_ = leanh::lean_box(0);
                        v_isShared_166_ = v_isSharedCheck_172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_f_159_);
                v___x_167_ =
                    leanh::lean_apply_2(v_f_159_, v_head_162_, leanh::lean_box(0));
                v___x_168_ = l_List_pmap___redArg(v_f_159_, v_tail_163_);
                if v_isShared_166_ == 0 {
                    leanh::lean_ctor_set(v___x_165_, 1, v___x_168_);
                    leanh::lean_ctor_set(v___x_165_, 0, v___x_167_);
                    v___x_170_ = v___x_165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_171_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
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
    mut v_00_u03b1_173_: *mut leanh::LeanObject,
    mut v_00_u03b2_174_: *mut leanh::LeanObject,
    mut v_P_175_: *mut leanh::LeanObject,
    mut v_f_176_: *mut leanh::LeanObject,
    mut v_x_177_: *mut leanh::LeanObject,
    mut v_x_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_179_ = l_List_pmap___redArg(v_f_176_, v_x_177_);
    return v___x_179_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(
    mut v_l_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_l_180_);
    return v_l_180_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg___boxed(
    mut v_l_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(v_l_181_);
    leanh::lean_dec(v_l_181_);
    return v_res_182_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl(
    mut v_00_u03b1_183_: *mut leanh::LeanObject,
    mut v_l_184_: *mut leanh::LeanObject,
    mut v_P_185_: *mut leanh::LeanObject,
    mut v_x_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_l_184_);
    return v_l_184_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_attachWithImpl___boxed(
    mut v_00_u03b1_187_: *mut leanh::LeanObject,
    mut v_l_188_: *mut leanh::LeanObject,
    mut v_P_189_: *mut leanh::LeanObject,
    mut v_x_190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_191_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl(
        v_00_u03b1_187_,
        v_l_188_,
        v_P_189_,
        v_x_190_,
    );
    leanh::lean_dec(v_l_188_);
    return v_res_191_;
}
pub unsafe fn l_List_attach___redArg(
    mut v_l_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_l_192_);
    return v_l_192_;
}
pub unsafe fn l_List_attach___redArg___boxed(
    mut v_l_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = l_List_attach___redArg(v_l_193_);
    leanh::lean_dec(v_l_193_);
    return v_res_194_;
}
pub unsafe fn l_List_attach(
    mut v_00_u03b1_195_: *mut leanh::LeanObject,
    mut v_l_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_l_196_);
    return v_l_196_;
}
pub unsafe fn l_List_attach___boxed(
    mut v_00_u03b1_197_: *mut leanh::LeanObject,
    mut v_l_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l_List_attach(v_00_u03b1_197_, v_l_198_);
    leanh::lean_dec(v_l_198_);
    return v_res_199_;
}
pub unsafe fn l_List_pmapImpl___redArg___lam__0(
    mut v_f_200_: *mut leanh::LeanObject,
    mut v_x_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_202_ = leanh::lean_apply_2(v_f_200_, v_x_201_, leanh::lean_box(0));
    return v___x_202_;
}
pub unsafe fn l_List_pmapImpl___redArg(
    mut v_f_203_: *mut leanh::LeanObject,
    mut v_l_204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_205_ = leanh::lean_alloc_closure(
        l_List_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_205_, 0, v_f_203_);
    v___x_206_ = leanh::lean_box(0);
    v___x_207_ = l_List_mapTR_loop___redArg(v___f_205_, v_l_204_, v___x_206_);
    return v___x_207_;
}
pub unsafe fn l_List_pmapImpl(
    mut v_00_u03b1_208_: *mut leanh::LeanObject,
    mut v_00_u03b2_209_: *mut leanh::LeanObject,
    mut v_P_210_: *mut leanh::LeanObject,
    mut v_f_211_: *mut leanh::LeanObject,
    mut v_l_212_: *mut leanh::LeanObject,
    mut v_H_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_214_ = leanh::lean_alloc_closure(
        l_List_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_214_, 0, v_f_211_);
    v___x_215_ = leanh::lean_box(0);
    v___x_216_ = l_List_mapTR_loop___redArg(v___f_214_, v_l_212_, v___x_215_);
    return v___x_216_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___redArg(
    mut v_x_217_: *mut leanh::LeanObject,
    mut v_h__1_218_: *mut leanh::LeanObject,
    mut v_h__2_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_219_);
        v___x_220_ = leanh::lean_apply_1(v_h__1_218_, leanh::lean_box(0));
        return v___x_220_;
    } else {
        let mut v_head_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_218_);
        v_head_221_ = leanh::lean_ctor_get(v_x_217_, 0);
        leanh::lean_inc(v_head_221_);
        v_tail_222_ = leanh::lean_ctor_get(v_x_217_, 1);
        leanh::lean_inc(v_tail_222_);
        leanh::lean_dec_ref_known(v_x_217_, 2);
        v___x_223_ = leanh::lean_apply_3(
            v_h__2_219_,
            v_head_221_,
            v_tail_222_,
            leanh::lean_box(0),
        );
        return v___x_223_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter(
    mut v_00_u03b1_224_: *mut leanh::LeanObject,
    mut v_P_225_: *mut leanh::LeanObject,
    mut v_motive_226_: *mut leanh::LeanObject,
    mut v_x_227_: *mut leanh::LeanObject,
    mut v_x_228_: *mut leanh::LeanObject,
    mut v_h__1_229_: *mut leanh::LeanObject,
    mut v_h__2_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_227_) == 0 {
        let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_230_);
        v___x_231_ = leanh::lean_apply_1(v_h__1_229_, leanh::lean_box(0));
        return v___x_231_;
    } else {
        let mut v_head_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_229_);
        v_head_232_ = leanh::lean_ctor_get(v_x_227_, 0);
        leanh::lean_inc(v_head_232_);
        v_tail_233_ = leanh::lean_ctor_get(v_x_227_, 1);
        leanh::lean_inc(v_tail_233_);
        leanh::lean_dec_ref_known(v_x_227_, 2);
        v___x_234_ = leanh::lean_apply_3(
            v_h__2_230_,
            v_head_232_,
            v_tail_233_,
            leanh::lean_box(0),
        );
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_235_: *mut leanh::LeanObject,
    mut v_h__1_236_: *mut leanh::LeanObject,
    mut v_h__2_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_235_) == 0 {
        let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_237_);
        v___x_238_ = leanh::lean_box(0);
        v___x_239_ = leanh::lean_apply_1(v_h__1_236_, v___x_238_);
        return v___x_239_;
    } else {
        let mut v_val_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_236_);
        v_val_240_ = leanh::lean_ctor_get(v_x_235_, 0);
        leanh::lean_inc(v_val_240_);
        leanh::lean_dec_ref_known(v_x_235_, 1);
        v___x_241_ = leanh::lean_apply_1(v_h__2_237_, v_val_240_);
        return v___x_241_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_242_: *mut leanh::LeanObject,
    mut v_motive_243_: *mut leanh::LeanObject,
    mut v_x_244_: *mut leanh::LeanObject,
    mut v_h__1_245_: *mut leanh::LeanObject,
    mut v_h__2_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_244_) == 0 {
        let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_246_);
        v___x_247_ = leanh::lean_box(0);
        v___x_248_ = leanh::lean_apply_1(v_h__1_245_, v___x_247_);
        return v___x_248_;
    } else {
        let mut v_val_249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_245_);
        v_val_249_ = leanh::lean_ctor_get(v_x_244_, 0);
        leanh::lean_inc(v_val_249_);
        leanh::lean_dec_ref_known(v_x_244_, 1);
        v___x_250_ = leanh::lean_apply_1(v_h__2_246_, v_val_249_);
        return v___x_250_;
    }
}
pub unsafe fn l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(
    mut v_a_251_: *mut leanh::LeanObject,
    mut v_a_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_251_) == 0 {
                    v___x_253_ = l_List_reverse___redArg(v_a_252_);
                    return v___x_253_;
                } else {
                    v_head_254_ = leanh::lean_ctor_get(v_a_251_, 0);
                    v_tail_255_ = leanh::lean_ctor_get(v_a_251_, 1);
                    v_isSharedCheck_263_ = (!leanh::lean_is_exclusive(v_a_251_)) as u8;
                    if v_isSharedCheck_263_ == 0 {
                        v___x_257_ = v_a_251_;
                        v_isShared_258_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_255_);
                        leanh::lean_inc(v_head_254_);
                        leanh::lean_dec(v_a_251_);
                        v___x_257_ = leanh::lean_box(0);
                        v_isShared_258_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_258_ == 0 {
                    leanh::lean_ctor_set(v___x_257_, 1, v_a_252_);
                    v___x_260_ = v___x_257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_262_, 0, v_head_254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_252_);
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
pub unsafe fn l_List_unattach___redArg(
    mut v_l_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_265_ = leanh::lean_box(0);
    v___x_266_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_l_264_, v___x_265_);
    return v___x_266_;
}
pub unsafe fn l_List_unattach(
    mut v_00_u03b1_267_: *mut leanh::LeanObject,
    mut v_p_268_: *mut leanh::LeanObject,
    mut v_l_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = l_List_unattach___redArg(v_l_269_);
    return v___x_270_;
}
pub unsafe fn l_List_mapTR_loop___at___00List_unattach_spec__0(
    mut v_00_u03b1_271_: *mut leanh::LeanObject,
    mut v_a_272_: *mut leanh::LeanObject,
    mut v_a_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_a_272_, v_a_273_);
    return v___x_274_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_275_: *mut leanh::LeanObject,
    mut v_h__1_276_: *mut leanh::LeanObject,
    mut v_h__2_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_275_) == 0 {
        let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_276_);
        v___x_278_ = leanh::lean_box(0);
        v___x_279_ = leanh::lean_apply_1(v_h__2_277_, v___x_278_);
        return v___x_279_;
    } else {
        let mut v_val_280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_277_);
        v_val_280_ = leanh::lean_ctor_get(v_x_275_, 0);
        leanh::lean_inc(v_val_280_);
        leanh::lean_dec_ref_known(v_x_275_, 1);
        v___x_281_ = leanh::lean_apply_1(v_h__1_276_, v_val_280_);
        return v___x_281_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_282_: *mut leanh::LeanObject,
    mut v_motive_283_: *mut leanh::LeanObject,
    mut v_x_284_: *mut leanh::LeanObject,
    mut v_h__1_285_: *mut leanh::LeanObject,
    mut v_h__2_286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_284_) == 0 {
        let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_285_);
        v___x_287_ = leanh::lean_box(0);
        v___x_288_ = leanh::lean_apply_1(v_h__2_286_, v___x_287_);
        return v___x_288_;
    } else {
        let mut v_val_289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_286_);
        v_val_289_ = leanh::lean_ctor_get(v_x_284_, 0);
        leanh::lean_inc(v_val_289_);
        leanh::lean_dec_ref_known(v_x_284_, 1);
        v___x_290_ = leanh::lean_apply_1(v_h__1_285_, v_val_289_);
        return v___x_290_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(
    mut v_x_291_: u8,
    mut v_h__1_292_: *mut leanh::LeanObject,
    mut v_h__2_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_291_ == 0 {
        let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_292_);
        v___x_294_ = leanh::lean_box(0);
        v___x_295_ = leanh::lean_apply_1(v_h__2_293_, v___x_294_);
        return v___x_295_;
    } else {
        let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_293_);
        v___x_296_ = leanh::lean_box(0);
        v___x_297_ = leanh::lean_apply_1(v_h__1_292_, v___x_296_);
        return v___x_297_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_298_: *mut leanh::LeanObject,
    mut v_h__1_299_: *mut leanh::LeanObject,
    mut v_h__2_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_301_: u8 = 0;
    let mut v_res_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_301_ = (leanh::lean_unbox(v_x_298_) as u8);
    v_res_302_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_301_,
        v_h__1_299_,
        v_h__2_300_,
    );
    return v_res_302_;
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(
    mut v_motive_303_: *mut leanh::LeanObject,
    mut v_x_304_: u8,
    mut v_h__1_305_: *mut leanh::LeanObject,
    mut v_h__2_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_304_ == 0 {
        let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_305_);
        v___x_307_ = leanh::lean_box(0);
        v___x_308_ = leanh::lean_apply_1(v_h__2_306_, v___x_307_);
        return v___x_308_;
    } else {
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_306_);
        v___x_309_ = leanh::lean_box(0);
        v___x_310_ = leanh::lean_apply_1(v_h__1_305_, v___x_309_);
        return v___x_310_;
    }
}
pub unsafe fn l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___boxed(
    mut v_motive_311_: *mut leanh::LeanObject,
    mut v_x_312_: *mut leanh::LeanObject,
    mut v_h__1_313_: *mut leanh::LeanObject,
    mut v_h__2_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_315_: u8 = 0;
    let mut v_res_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_315_ = (leanh::lean_unbox(v_x_312_) as u8);
    v_res_316_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(
        v_motive_311_,
        v_x_37__boxed_315_,
        v_h__1_313_,
        v_h__2_314_,
    );
    return v_res_316_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Attach(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Attach(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Attach(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Attach(builtin);
}