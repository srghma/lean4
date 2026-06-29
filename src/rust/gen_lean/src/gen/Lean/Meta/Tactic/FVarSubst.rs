// Lean compiler output
// Module: Lean.Meta.Tactic.FVarSubst
// Imports: Lean.Data.AssocList Lean.LocalContext Lean.Util.ReplaceExpr
use crate::ffi::lean_replace_expr;
use crate::r#gen::Lean::Data::AssocList::{
    initialize_Lean_Data_AssocList, l_Lean_AssocList_any___redArg,
    l_Lean_AssocList_isEmpty___redArg, l_Lean_AssocList_mapVal___redArg,
    runtime_initialize_Lean_Data_AssocList,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasFVar, l_Lean_Expr_replaceFVarId, l_Lean_instBEqFVarId_beq, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    initialize_Lean_LocalContext, runtime_initialize_Lean_LocalContext,
};
use crate::r#gen::Lean::Util::ReplaceExpr::{
    initialize_Lean_Util_ReplaceExpr, runtime_initialize_Lean_Util_ReplaceExpr,
};
pub static mut l_Lean_Meta_instInhabitedFVarSubst_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedFVarSubst: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_FVarSubst_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_instInhabitedFVarSubst_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_205_ = crate::leanh::lean_box(0);
    return v___x_205_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedFVarSubst() -> *mut crate::leanh::LeanObject {
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_206_ = crate::leanh::lean_box(0);
    return v___x_206_;
}
pub unsafe fn _init_l_Lean_Meta_FVarSubst_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_207_ = crate::leanh::lean_box(0);
    return v___x_207_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_isEmpty(mut v_s_208_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_209_: u8 = 0;
    v___x_209_ = l_Lean_AssocList_isEmpty___redArg(v_s_208_);
    return v___x_209_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_isEmpty___boxed(
    mut v_s_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_211_: u8 = 0;
    let mut v_r_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Lean_Meta_FVarSubst_isEmpty(v_s_210_);
    crate::leanh::lean_dec(v_s_210_);
    v_r_212_ = crate::leanh::lean_box((v_res_211_) as usize);
    return v_r_212_;
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
    mut v_a_213_: *mut crate::leanh::LeanObject,
    mut v_x_214_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_215_: u8 = 0;
    let mut v_key_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_214_) == 0 {
                    v___x_215_ = 0;
                    return v___x_215_;
                } else {
                    v_key_216_ = crate::leanh::lean_ctor_get(v_x_214_, 0);
                    v_tail_217_ = crate::leanh::lean_ctor_get(v_x_214_, 2);
                    v___x_218_ = l_Lean_instBEqFVarId_beq(v_key_216_, v_a_213_);
                    if v___x_218_ == 0 {
                        v_x_214_ = v_tail_217_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_218_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg___boxed(
    mut v_a_220_: *mut crate::leanh::LeanObject,
    mut v_x_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_222_: u8 = 0;
    let mut v_r_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_a_220_, v_x_221_,
    );
    crate::leanh::lean_dec(v_x_221_);
    crate::leanh::lean_dec(v_a_220_);
    v_r_223_ = crate::leanh::lean_box((v_res_222_) as usize);
    return v_r_223_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_contains(
    mut v_s_224_: *mut crate::leanh::LeanObject,
    mut v_fvarId_225_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_226_: u8 = 0;
    v___x_226_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_fvarId_225_,
        v_s_224_,
    );
    return v___x_226_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_contains___boxed(
    mut v_s_227_: *mut crate::leanh::LeanObject,
    mut v_fvarId_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Lean_Meta_FVarSubst_contains(v_s_227_, v_fvarId_228_);
    crate::leanh::lean_dec(v_fvarId_228_);
    crate::leanh::lean_dec(v_s_227_);
    v_r_230_ = crate::leanh::lean_box((v_res_229_) as usize);
    return v_r_230_;
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(
    mut v_00_u03b2_231_: *mut crate::leanh::LeanObject,
    mut v_a_232_: *mut crate::leanh::LeanObject,
    mut v_x_233_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_234_: u8 = 0;
    v___x_234_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_a_232_, v_x_233_,
    );
    return v___x_234_;
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___boxed(
    mut v_00_u03b2_235_: *mut crate::leanh::LeanObject,
    mut v_a_236_: *mut crate::leanh::LeanObject,
    mut v_x_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_238_: u8 = 0;
    let mut v_r_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_238_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(
        v_00_u03b2_235_,
        v_a_236_,
        v_x_237_,
    );
    crate::leanh::lean_dec(v_x_237_);
    crate::leanh::lean_dec(v_a_236_);
    v_r_239_ = crate::leanh::lean_box((v_res_238_) as usize);
    return v_r_239_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_insert___lam__0(
    mut v_fvarId_240_: *mut crate::leanh::LeanObject,
    mut v_v_241_: *mut crate::leanh::LeanObject,
    mut v_e_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = l_Lean_Expr_replaceFVarId(v_e_242_, v_fvarId_240_, v_v_241_);
    return v___x_243_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_insert___lam__0___boxed(
    mut v_fvarId_244_: *mut crate::leanh::LeanObject,
    mut v_v_245_: *mut crate::leanh::LeanObject,
    mut v_e_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Lean_Meta_FVarSubst_insert___lam__0(v_fvarId_244_, v_v_245_, v_e_246_);
    crate::leanh::lean_dec_ref(v_e_246_);
    crate::leanh::lean_dec_ref(v_v_245_);
    return v_res_247_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_insert(
    mut v_s_248_: *mut crate::leanh::LeanObject,
    mut v_fvarId_249_: *mut crate::leanh::LeanObject,
    mut v_v_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_251_: u8 = 0;
    v___x_251_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_fvarId_249_,
        v_s_248_,
    );
    if v___x_251_ == 0 {
        let mut v___f_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_v_250_);
        crate::leanh::lean_inc(v_fvarId_249_);
        v___f_252_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_FVarSubst_insert___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_252_, 0, v_fvarId_249_);
        crate::leanh::lean_closure_set(v___f_252_, 1, v_v_250_);
        v_map_253_ = l_Lean_AssocList_mapVal___redArg(v___f_252_, v_s_248_);
        v___x_254_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_254_, 0, v_fvarId_249_);
        crate::leanh::lean_ctor_set(v___x_254_, 1, v_v_250_);
        crate::leanh::lean_ctor_set(v___x_254_, 2, v_map_253_);
        return v___x_254_;
    } else {
        crate::leanh::lean_dec_ref(v_v_250_);
        crate::leanh::lean_dec(v_fvarId_249_);
        return v_s_248_;
    }
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
    mut v_a_255_: *mut crate::leanh::LeanObject,
    mut v_x_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_262_: u8 = 0;
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_256_) == 0 {
                    return v_x_256_;
                } else {
                    v_key_257_ = crate::leanh::lean_ctor_get(v_x_256_, 0);
                    v_value_258_ = crate::leanh::lean_ctor_get(v_x_256_, 1);
                    v_tail_259_ = crate::leanh::lean_ctor_get(v_x_256_, 2);
                    v_isSharedCheck_268_ = (!crate::leanh::lean_is_exclusive(v_x_256_)) as u8;
                    if v_isSharedCheck_268_ == 0 {
                        v___x_261_ = v_x_256_;
                        v_isShared_262_ = v_isSharedCheck_268_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_259_);
                        crate::leanh::lean_inc(v_value_258_);
                        crate::leanh::lean_inc(v_key_257_);
                        crate::leanh::lean_dec(v_x_256_);
                        v___x_261_ = crate::leanh::lean_box(0);
                        v_isShared_262_ = v_isSharedCheck_268_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_263_ = l_Lean_instBEqFVarId_beq(v_key_257_, v_a_255_);
                if v___x_263_ == 0 {
                    v___x_264_ =
                        l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
                            v_a_255_,
                            v_tail_259_,
                        );
                    if v_isShared_262_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_261_, 2, v___x_264_);
                        v___x_266_ = v___x_261_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_267_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_267_, 0, v_key_257_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_267_, 1, v_value_258_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_267_, 2, v___x_264_);
                        v___x_266_ = v_reuseFailAlloc_267_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_261_);
                    crate::leanh::lean_dec(v_value_258_);
                    crate::leanh::lean_dec(v_key_257_);
                    return v_tail_259_;
                }
            }
            2 => {
                return v___x_266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg___boxed(
    mut v_a_269_: *mut crate::leanh::LeanObject,
    mut v_x_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
        v_a_269_, v_x_270_,
    );
    crate::leanh::lean_dec(v_a_269_);
    return v_res_271_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_erase(
    mut v_s_272_: *mut crate::leanh::LeanObject,
    mut v_fvarId_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
        v_fvarId_273_,
        v_s_272_,
    );
    return v___x_274_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_erase___boxed(
    mut v_s_275_: *mut crate::leanh::LeanObject,
    mut v_fvarId_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Lean_Meta_FVarSubst_erase(v_s_275_, v_fvarId_276_);
    crate::leanh::lean_dec(v_fvarId_276_);
    return v_res_277_;
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(
    mut v_00_u03b2_278_: *mut crate::leanh::LeanObject,
    mut v_a_279_: *mut crate::leanh::LeanObject,
    mut v_x_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
        v_a_279_, v_x_280_,
    );
    return v___x_281_;
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___boxed(
    mut v_00_u03b2_282_: *mut crate::leanh::LeanObject,
    mut v_a_283_: *mut crate::leanh::LeanObject,
    mut v_x_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(
        v_00_u03b2_282_,
        v_a_283_,
        v_x_284_,
    );
    crate::leanh::lean_dec(v_a_283_);
    return v_res_285_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
    mut v_a_286_: *mut crate::leanh::LeanObject,
    mut v_x_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: u8 = 0;
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_287_) == 0 {
                    v___x_288_ = crate::leanh::lean_box(0);
                    return v___x_288_;
                } else {
                    v_key_289_ = crate::leanh::lean_ctor_get(v_x_287_, 0);
                    v_value_290_ = crate::leanh::lean_ctor_get(v_x_287_, 1);
                    v_tail_291_ = crate::leanh::lean_ctor_get(v_x_287_, 2);
                    v___x_292_ = l_Lean_instBEqFVarId_beq(v_key_289_, v_a_286_);
                    if v___x_292_ == 0 {
                        v_x_287_ = v_tail_291_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_290_);
                        v___x_294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_294_, 0, v_value_290_);
                        return v___x_294_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg___boxed(
    mut v_a_295_: *mut crate::leanh::LeanObject,
    mut v_x_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_297_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_a_295_, v_x_296_,
    );
    crate::leanh::lean_dec(v_x_296_);
    crate::leanh::lean_dec(v_a_295_);
    return v_res_297_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_find_x3f(
    mut v_s_298_: *mut crate::leanh::LeanObject,
    mut v_fvarId_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_fvarId_299_,
        v_s_298_,
    );
    return v___x_300_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_find_x3f___boxed(
    mut v_s_301_: *mut crate::leanh::LeanObject,
    mut v_fvarId_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_301_, v_fvarId_302_);
    crate::leanh::lean_dec(v_fvarId_302_);
    crate::leanh::lean_dec(v_s_301_);
    return v_res_303_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(
    mut v_00_u03b2_304_: *mut crate::leanh::LeanObject,
    mut v_a_305_: *mut crate::leanh::LeanObject,
    mut v_x_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_a_305_, v_x_306_,
    );
    return v___x_307_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___boxed(
    mut v_00_u03b2_308_: *mut crate::leanh::LeanObject,
    mut v_a_309_: *mut crate::leanh::LeanObject,
    mut v_x_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(
        v_00_u03b2_308_,
        v_a_309_,
        v_x_310_,
    );
    crate::leanh::lean_dec(v_x_310_);
    crate::leanh::lean_dec(v_a_309_);
    return v_res_311_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_get(
    mut v_s_312_: *mut crate::leanh::LeanObject,
    mut v_fvarId_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_314_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_fvarId_313_,
        v_s_312_,
    );
    if crate::leanh::lean_obj_tag(v___x_314_) == 0 {
        let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_315_ = l_Lean_mkFVar(v_fvarId_313_);
        return v___x_315_;
    } else {
        let mut v_val_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fvarId_313_);
        v_val_316_ = crate::leanh::lean_ctor_get(v___x_314_, 0);
        crate::leanh::lean_inc(v_val_316_);
        crate::leanh::lean_dec_ref_known(v___x_314_, 1);
        return v_val_316_;
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_get___boxed(
    mut v_s_317_: *mut crate::leanh::LeanObject,
    mut v_fvarId_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Lean_Meta_FVarSubst_get(v_s_317_, v_fvarId_318_);
    crate::leanh::lean_dec(v_s_317_);
    return v_res_319_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply___lam__0(
    mut v_s_320_: *mut crate::leanh::LeanObject,
    mut v_e_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_321_) == 1 {
        let mut v_fvarId_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_322_ = crate::leanh::lean_ctor_get(v_e_321_, 0);
        v___x_323_ =
            l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
                v_fvarId_322_,
                v_s_320_,
            );
        if crate::leanh::lean_obj_tag(v___x_323_) == 0 {
            let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_324_, 0, v_e_321_);
            return v___x_324_;
        } else {
            crate::leanh::lean_dec_ref_known(v_e_321_, 1);
            return v___x_323_;
        }
    } else {
        let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_321_);
        v___x_325_ = crate::leanh::lean_box(0);
        return v___x_325_;
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply___lam__0___boxed(
    mut v_s_326_: *mut crate::leanh::LeanObject,
    mut v_e_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_328_ = l_Lean_Meta_FVarSubst_apply___lam__0(v_s_326_, v_e_327_);
    crate::leanh::lean_dec(v_s_326_);
    return v_res_328_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply(
    mut v_s_329_: *mut crate::leanh::LeanObject,
    mut v_e_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_331_: u8 = 0;
    v___x_331_ = l_Lean_AssocList_isEmpty___redArg(v_s_329_);
    if v___x_331_ == 0 {
        let mut v___x_332_: u8 = 0;
        v___x_332_ = l_Lean_Expr_hasFVar(v_e_330_);
        if v___x_332_ == 0 {
            crate::leanh::lean_dec(v_s_329_);
            crate::leanh::lean_inc_ref(v_e_330_);
            return v_e_330_;
        } else {
            if v___x_331_ == 0 {
                let mut v___f_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_333_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_FVarSubst_apply___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_333_, 0, v_s_329_);
                v___x_334_ = lean_replace_expr(v___f_333_, v_e_330_);
                crate::leanh::lean_dec_ref(v___f_333_);
                return v___x_334_;
            } else {
                crate::leanh::lean_dec(v_s_329_);
                crate::leanh::lean_inc_ref(v_e_330_);
                return v_e_330_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_s_329_);
        crate::leanh::lean_inc_ref(v_e_330_);
        return v_e_330_;
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply___boxed(
    mut v_s_335_: *mut crate::leanh::LeanObject,
    mut v_e_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Lean_Meta_FVarSubst_apply(v_s_335_, v_e_336_);
    crate::leanh::lean_dec_ref(v_e_336_);
    return v_res_337_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(
    mut v_x_338_: *mut crate::leanh::LeanObject,
    mut v_x_339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_339_) == 0 {
                    return v_x_338_;
                } else {
                    v_key_340_ = crate::leanh::lean_ctor_get(v_x_339_, 0);
                    v_tail_341_ = crate::leanh::lean_ctor_get(v_x_339_, 2);
                    crate::leanh::lean_inc(v_key_340_);
                    v___x_342_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_342_, 0, v_key_340_);
                    crate::leanh::lean_ctor_set(v___x_342_, 1, v_x_338_);
                    v_x_338_ = v___x_342_;
                    v_x_339_ = v_tail_341_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0___boxed(
    mut v_x_344_: *mut crate::leanh::LeanObject,
    mut v_x_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ =
        l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v_x_344_, v_x_345_);
    crate::leanh::lean_dec(v_x_345_);
    return v_res_346_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_domain(
    mut v_s_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = crate::leanh::lean_box(0);
    v___x_349_ =
        l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v___x_348_, v_s_347_);
    return v___x_349_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_domain___boxed(
    mut v_s_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Lean_Meta_FVarSubst_domain(v_s_350_);
    crate::leanh::lean_dec(v_s_350_);
    return v_res_351_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_any(
    mut v_p_352_: *mut crate::leanh::LeanObject,
    mut v_s_353_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_354_: u8 = 0;
    v___x_354_ = l_Lean_AssocList_any___redArg(v_p_352_, v_s_353_);
    return v___x_354_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_any___boxed(
    mut v_p_355_: *mut crate::leanh::LeanObject,
    mut v_s_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: u8 = 0;
    let mut v_r_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lean_Meta_FVarSubst_any(v_p_355_, v_s_356_);
    v_r_358_ = crate::leanh::lean_box((v_res_357_) as usize);
    return v_r_358_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(
    mut v_t_359_: *mut crate::leanh::LeanObject,
    mut v_x_360_: *mut crate::leanh::LeanObject,
    mut v_x_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_361_) == 0 {
                    crate::leanh::lean_dec(v_t_359_);
                    return v_x_360_;
                } else {
                    v_key_362_ = crate::leanh::lean_ctor_get(v_x_361_, 0);
                    crate::leanh::lean_inc(v_key_362_);
                    v_value_363_ = crate::leanh::lean_ctor_get(v_x_361_, 1);
                    crate::leanh::lean_inc(v_value_363_);
                    v_tail_364_ = crate::leanh::lean_ctor_get(v_x_361_, 2);
                    crate::leanh::lean_inc(v_tail_364_);
                    crate::leanh::lean_dec_ref_known(v_x_361_, 3);
                    crate::leanh::lean_inc(v_t_359_);
                    v___x_365_ = l_Lean_Meta_FVarSubst_apply(v_t_359_, v_value_363_);
                    crate::leanh::lean_dec(v_value_363_);
                    v___x_366_ = l_Lean_Meta_FVarSubst_insert(v_x_360_, v_key_362_, v___x_365_);
                    v_x_360_ = v___x_366_;
                    v_x_361_ = v_tail_364_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_append(
    mut v_s_368_: *mut crate::leanh::LeanObject,
    mut v_t_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_t_369_);
    v___x_370_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(
        v_t_369_, v_t_369_, v_s_368_,
    );
    return v___x_370_;
}
pub unsafe fn l_Lean_LocalDecl_applyFVarSubst(
    mut v_s_371_: *mut crate::leanh::LeanObject,
    mut v_x_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_index_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_377_: u8 = 0;
    let mut v_kind_378_: u8 = 0;
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v_index_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_392_: u8 = 0;
    let mut v_kind_393_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_372_) == 0 {
                    v_index_373_ = crate::leanh::lean_ctor_get(v_x_372_, 0);
                    v_fvarId_374_ = crate::leanh::lean_ctor_get(v_x_372_, 1);
                    v_userName_375_ = crate::leanh::lean_ctor_get(v_x_372_, 2);
                    v_type_376_ = crate::leanh::lean_ctor_get(v_x_372_, 3);
                    v_bi_377_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_kind_378_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_386_ = (!crate::leanh::lean_is_exclusive(v_x_372_)) as u8;
                    if v_isSharedCheck_386_ == 0 {
                        v___x_380_ = v_x_372_;
                        v_isShared_381_ = v_isSharedCheck_386_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_376_);
                        crate::leanh::lean_inc(v_userName_375_);
                        crate::leanh::lean_inc(v_fvarId_374_);
                        crate::leanh::lean_inc(v_index_373_);
                        crate::leanh::lean_dec(v_x_372_);
                        v___x_380_ = crate::leanh::lean_box(0);
                        v_isShared_381_ = v_isSharedCheck_386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_index_387_ = crate::leanh::lean_ctor_get(v_x_372_, 0);
                    v_fvarId_388_ = crate::leanh::lean_ctor_get(v_x_372_, 1);
                    v_userName_389_ = crate::leanh::lean_ctor_get(v_x_372_, 2);
                    v_type_390_ = crate::leanh::lean_ctor_get(v_x_372_, 3);
                    v_value_391_ = crate::leanh::lean_ctor_get(v_x_372_, 4);
                    v_nondep_392_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    v_kind_393_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_402_ = (!crate::leanh::lean_is_exclusive(v_x_372_)) as u8;
                    if v_isSharedCheck_402_ == 0 {
                        v___x_395_ = v_x_372_;
                        v_isShared_396_ = v_isSharedCheck_402_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_391_);
                        crate::leanh::lean_inc(v_type_390_);
                        crate::leanh::lean_inc(v_userName_389_);
                        crate::leanh::lean_inc(v_fvarId_388_);
                        crate::leanh::lean_inc(v_index_387_);
                        crate::leanh::lean_dec(v_x_372_);
                        v___x_395_ = crate::leanh::lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_402_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_382_ = l_Lean_Meta_FVarSubst_apply(v_s_371_, v_type_376_);
                crate::leanh::lean_dec_ref(v_type_376_);
                if v_isShared_381_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_380_, 3, v___x_382_);
                    v___x_384_ = v___x_380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 0, v_index_373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 1, v_fvarId_374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 2, v_userName_375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 3, v___x_382_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_385_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_bi_377_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_385_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_kind_378_,
                    );
                    v___x_384_ = v_reuseFailAlloc_385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_384_;
            }
            3 => {
                crate::leanh::lean_inc(v_s_371_);
                v___x_397_ = l_Lean_Meta_FVarSubst_apply(v_s_371_, v_type_390_);
                crate::leanh::lean_dec_ref(v_type_390_);
                v___x_398_ = l_Lean_Meta_FVarSubst_apply(v_s_371_, v_value_391_);
                crate::leanh::lean_dec_ref(v_value_391_);
                if v_isShared_396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_395_, 4, v___x_398_);
                    crate::leanh::lean_ctor_set(v___x_395_, 3, v___x_397_);
                    v___x_400_ = v___x_395_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_401_ = crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v_index_387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 1, v_fvarId_388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 2, v_userName_389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 3, v___x_397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_398_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v_nondep_392_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                        v_kind_393_,
                    );
                    v___x_400_ = v_reuseFailAlloc_401_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_applyFVarSubst(
    mut v_s_403_: *mut crate::leanh::LeanObject,
    mut v_e_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Meta_FVarSubst_apply(v_s_403_, v_e_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Expr_applyFVarSubst___boxed(
    mut v_s_406_: *mut crate::leanh::LeanObject,
    mut v_e_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_408_ = l_Lean_Expr_applyFVarSubst(v_s_406_, v_e_407_);
    crate::leanh::lean_dec_ref(v_e_407_);
    return v_res_408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_FVarSubst(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LocalContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedFVarSubst_default = _init_l_Lean_Meta_instInhabitedFVarSubst_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst_default);
    l_Lean_Meta_instInhabitedFVarSubst = _init_l_Lean_Meta_instInhabitedFVarSubst();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst);
    l_Lean_Meta_FVarSubst_empty = _init_l_Lean_Meta_FVarSubst_empty();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_FVarSubst_empty);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_FVarSubst(
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
pub unsafe fn initialize_Lean_Meta_Tactic_FVarSubst(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_AssocList(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_LocalContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ReplaceExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_FVarSubst(builtin);
}
