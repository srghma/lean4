// Lean compiler output
// Module: Lean.Meta.Tactic.FVarSubst
// Imports: Lean.Data.AssocList Lean.LocalContext Lean.Util.ReplaceExpr
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
use crate::lean_imports_rs::Lean::Util::ReplaceExpr::lean_replace_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_tag,
};
pub static mut l_Lean_Meta_instInhabitedFVarSubst_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedFVarSubst: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_FVarSubst_empty: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_instInhabitedFVarSubst_default() -> *mut LeanObject {
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v___x_205_ = lean_box(0);
    return v___x_205_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedFVarSubst() -> *mut LeanObject {
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    v___x_206_ = lean_box(0);
    return v___x_206_;
}
pub unsafe fn _init_l_Lean_Meta_FVarSubst_empty() -> *mut LeanObject {
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    v___x_207_ = lean_box(0);
    return v___x_207_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_isEmpty(mut v_s_208_: *mut LeanObject) -> u8 {
    let mut v___x_209_: u8 = 0;
    v___x_209_ = l_Lean_AssocList_isEmpty___redArg(v_s_208_);
    return v___x_209_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_isEmpty___boxed(
    mut v_s_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_211_: u8 = 0;
    let mut v_r_212_: *mut LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Lean_Meta_FVarSubst_isEmpty(v_s_210_);
    lean_dec(v_s_210_);
    v_r_212_ = lean_box((v_res_211_) as usize);
    return v_r_212_;
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
    mut v_a_213_: *mut LeanObject,
    mut v_x_214_: *mut LeanObject,
) -> u8 {
    let mut v___x_215_: u8 = 0;
    let mut v_key_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_214_) == 0 {
                    v___x_215_ = 0;
                    return v___x_215_;
                } else {
                    v_key_216_ = lean_ctor_get(v_x_214_, 0);
                    v_tail_217_ = lean_ctor_get(v_x_214_, 2);
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
    mut v_a_220_: *mut LeanObject,
    mut v_x_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: u8 = 0;
    let mut v_r_223_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_a_220_, v_x_221_,
    );
    lean_dec(v_x_221_);
    lean_dec(v_a_220_);
    v_r_223_ = lean_box((v_res_222_) as usize);
    return v_r_223_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_contains(
    mut v_s_224_: *mut LeanObject,
    mut v_fvarId_225_: *mut LeanObject,
) -> u8 {
    let mut v___x_226_: u8 = 0;
    v___x_226_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_fvarId_225_,
        v_s_224_,
    );
    return v___x_226_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_contains___boxed(
    mut v_s_227_: *mut LeanObject,
    mut v_fvarId_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Lean_Meta_FVarSubst_contains(v_s_227_, v_fvarId_228_);
    lean_dec(v_fvarId_228_);
    lean_dec(v_s_227_);
    v_r_230_ = lean_box((v_res_229_) as usize);
    return v_r_230_;
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(
    mut v_00_u03b2_231_: *mut LeanObject,
    mut v_a_232_: *mut LeanObject,
    mut v_x_233_: *mut LeanObject,
) -> u8 {
    let mut v___x_234_: u8 = 0;
    v___x_234_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_a_232_, v_x_233_,
    );
    return v___x_234_;
}
pub unsafe fn l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___boxed(
    mut v_00_u03b2_235_: *mut LeanObject,
    mut v_a_236_: *mut LeanObject,
    mut v_x_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: u8 = 0;
    let mut v_r_239_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0(
        v_00_u03b2_235_,
        v_a_236_,
        v_x_237_,
    );
    lean_dec(v_x_237_);
    lean_dec(v_a_236_);
    v_r_239_ = lean_box((v_res_238_) as usize);
    return v_r_239_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_insert___lam__0(
    mut v_fvarId_240_: *mut LeanObject,
    mut v_v_241_: *mut LeanObject,
    mut v_e_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    v___x_243_ = l_Lean_Expr_replaceFVarId(v_e_242_, v_fvarId_240_, v_v_241_);
    return v___x_243_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_insert___lam__0___boxed(
    mut v_fvarId_244_: *mut LeanObject,
    mut v_v_245_: *mut LeanObject,
    mut v_e_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_247_: *mut LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Lean_Meta_FVarSubst_insert___lam__0(v_fvarId_244_, v_v_245_, v_e_246_);
    lean_dec_ref(v_e_246_);
    lean_dec_ref(v_v_245_);
    return v_res_247_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_insert(
    mut v_s_248_: *mut LeanObject,
    mut v_fvarId_249_: *mut LeanObject,
    mut v_v_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_251_: u8 = 0;
    v___x_251_ = l_Lean_AssocList_contains___at___00Lean_Meta_FVarSubst_contains_spec__0___redArg(
        v_fvarId_249_,
        v_s_248_,
    );
    if v___x_251_ == 0 {
        let mut v___f_252_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_v_250_);
        lean_inc(v_fvarId_249_);
        v___f_252_ = lean_alloc_closure(
            l_Lean_Meta_FVarSubst_insert___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_252_, 0, v_fvarId_249_);
        lean_closure_set(v___f_252_, 1, v_v_250_);
        v_map_253_ = l_Lean_AssocList_mapVal___redArg(v___f_252_, v_s_248_);
        v___x_254_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_254_, 0, v_fvarId_249_);
        lean_ctor_set(v___x_254_, 1, v_v_250_);
        lean_ctor_set(v___x_254_, 2, v_map_253_);
        return v___x_254_;
    } else {
        lean_dec_ref(v_v_250_);
        lean_dec(v_fvarId_249_);
        return v_s_248_;
    }
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
    mut v_a_255_: *mut LeanObject,
    mut v_x_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_262_: u8 = 0;
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_256_) == 0 {
                    return v_x_256_;
                } else {
                    v_key_257_ = lean_ctor_get(v_x_256_, 0);
                    v_value_258_ = lean_ctor_get(v_x_256_, 1);
                    v_tail_259_ = lean_ctor_get(v_x_256_, 2);
                    v_isSharedCheck_268_ = (!lean_is_exclusive(v_x_256_)) as u8;
                    if v_isSharedCheck_268_ == 0 {
                        v___x_261_ = v_x_256_;
                        v_isShared_262_ = v_isSharedCheck_268_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_259_);
                        lean_inc(v_value_258_);
                        lean_inc(v_key_257_);
                        lean_dec(v_x_256_);
                        v___x_261_ = lean_box(0);
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
                        lean_ctor_set(v___x_261_, 2, v___x_264_);
                        v___x_266_ = v___x_261_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_267_, 0, v_key_257_);
                        lean_ctor_set(v_reuseFailAlloc_267_, 1, v_value_258_);
                        lean_ctor_set(v_reuseFailAlloc_267_, 2, v___x_264_);
                        v___x_266_ = v_reuseFailAlloc_267_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_261_);
                    lean_dec(v_value_258_);
                    lean_dec(v_key_257_);
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
    mut v_a_269_: *mut LeanObject,
    mut v_x_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_271_: *mut LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
        v_a_269_, v_x_270_,
    );
    lean_dec(v_a_269_);
    return v_res_271_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_erase(
    mut v_s_272_: *mut LeanObject,
    mut v_fvarId_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    v___x_274_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
        v_fvarId_273_,
        v_s_272_,
    );
    return v___x_274_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_erase___boxed(
    mut v_s_275_: *mut LeanObject,
    mut v_fvarId_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_277_: *mut LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Lean_Meta_FVarSubst_erase(v_s_275_, v_fvarId_276_);
    lean_dec(v_fvarId_276_);
    return v_res_277_;
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(
    mut v_00_u03b2_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    v___x_281_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___redArg(
        v_a_279_, v_x_280_,
    );
    return v___x_281_;
}
pub unsafe fn l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0___boxed(
    mut v_00_u03b2_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
    mut v_x_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_285_: *mut LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Lean_AssocList_erase___at___00Lean_Meta_FVarSubst_erase_spec__0(
        v_00_u03b2_282_,
        v_a_283_,
        v_x_284_,
    );
    lean_dec(v_a_283_);
    return v_res_285_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
    mut v_a_286_: *mut LeanObject,
    mut v_x_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: u8 = 0;
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_287_) == 0 {
                    v___x_288_ = lean_box(0);
                    return v___x_288_;
                } else {
                    v_key_289_ = lean_ctor_get(v_x_287_, 0);
                    v_value_290_ = lean_ctor_get(v_x_287_, 1);
                    v_tail_291_ = lean_ctor_get(v_x_287_, 2);
                    v___x_292_ = l_Lean_instBEqFVarId_beq(v_key_289_, v_a_286_);
                    if v___x_292_ == 0 {
                        v_x_287_ = v_tail_291_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_290_);
                        v___x_294_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_294_, 0, v_value_290_);
                        return v___x_294_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg___boxed(
    mut v_a_295_: *mut LeanObject,
    mut v_x_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_297_: *mut LeanObject = core::ptr::null_mut();
    v_res_297_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_a_295_, v_x_296_,
    );
    lean_dec(v_x_296_);
    lean_dec(v_a_295_);
    return v_res_297_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_find_x3f(
    mut v_s_298_: *mut LeanObject,
    mut v_fvarId_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    v___x_300_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_fvarId_299_,
        v_s_298_,
    );
    return v___x_300_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_find_x3f___boxed(
    mut v_s_301_: *mut LeanObject,
    mut v_fvarId_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_303_: *mut LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_301_, v_fvarId_302_);
    lean_dec(v_fvarId_302_);
    lean_dec(v_s_301_);
    return v_res_303_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(
    mut v_00_u03b2_304_: *mut LeanObject,
    mut v_a_305_: *mut LeanObject,
    mut v_x_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_a_305_, v_x_306_,
    );
    return v___x_307_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___boxed(
    mut v_00_u03b2_308_: *mut LeanObject,
    mut v_a_309_: *mut LeanObject,
    mut v_x_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_311_: *mut LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0(
        v_00_u03b2_308_,
        v_a_309_,
        v_x_310_,
    );
    lean_dec(v_x_310_);
    lean_dec(v_a_309_);
    return v_res_311_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_get(
    mut v_s_312_: *mut LeanObject,
    mut v_fvarId_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_314_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
        v_fvarId_313_,
        v_s_312_,
    );
    if lean_obj_tag(v___x_314_) == 0 {
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        v___x_315_ = l_Lean_mkFVar(v_fvarId_313_);
        return v___x_315_;
    } else {
        let mut v_val_316_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fvarId_313_);
        v_val_316_ = lean_ctor_get(v___x_314_, 0);
        lean_inc(v_val_316_);
        lean_dec_ref_known(v___x_314_, 1);
        return v_val_316_;
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_get___boxed(
    mut v_s_317_: *mut LeanObject,
    mut v_fvarId_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_319_: *mut LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Lean_Meta_FVarSubst_get(v_s_317_, v_fvarId_318_);
    lean_dec(v_s_317_);
    return v_res_319_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply___lam__0(
    mut v_s_320_: *mut LeanObject,
    mut v_e_321_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_321_) == 1 {
        let mut v_fvarId_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_322_ = lean_ctor_get(v_e_321_, 0);
        v___x_323_ =
            l_Lean_AssocList_find_x3f___at___00Lean_Meta_FVarSubst_find_x3f_spec__0___redArg(
                v_fvarId_322_,
                v_s_320_,
            );
        if lean_obj_tag(v___x_323_) == 0 {
            let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
            v___x_324_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_324_, 0, v_e_321_);
            return v___x_324_;
        } else {
            lean_dec_ref_known(v_e_321_, 1);
            return v___x_323_;
        }
    } else {
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_321_);
        v___x_325_ = lean_box(0);
        return v___x_325_;
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply___lam__0___boxed(
    mut v_s_326_: *mut LeanObject,
    mut v_e_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_328_: *mut LeanObject = core::ptr::null_mut();
    v_res_328_ = l_Lean_Meta_FVarSubst_apply___lam__0(v_s_326_, v_e_327_);
    lean_dec(v_s_326_);
    return v_res_328_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply(
    mut v_s_329_: *mut LeanObject,
    mut v_e_330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_331_: u8 = 0;
    v___x_331_ = l_Lean_AssocList_isEmpty___redArg(v_s_329_);
    if v___x_331_ == 0 {
        let mut v___x_332_: u8 = 0;
        v___x_332_ = l_Lean_Expr_hasFVar(v_e_330_);
        if v___x_332_ == 0 {
            lean_dec(v_s_329_);
            lean_inc_ref(v_e_330_);
            return v_e_330_;
        } else {
            if v___x_331_ == 0 {
                let mut v___f_333_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
                v___f_333_ = lean_alloc_closure(
                    l_Lean_Meta_FVarSubst_apply___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_333_, 0, v_s_329_);
                v___x_334_ = lean_replace_expr(v___f_333_, v_e_330_);
                lean_dec_ref(v___f_333_);
                return v___x_334_;
            } else {
                lean_dec(v_s_329_);
                lean_inc_ref(v_e_330_);
                return v_e_330_;
            }
        }
    } else {
        lean_dec(v_s_329_);
        lean_inc_ref(v_e_330_);
        return v_e_330_;
    }
}
pub unsafe fn l_Lean_Meta_FVarSubst_apply___boxed(
    mut v_s_335_: *mut LeanObject,
    mut v_e_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Lean_Meta_FVarSubst_apply(v_s_335_, v_e_336_);
    lean_dec_ref(v_e_336_);
    return v_res_337_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(
    mut v_x_338_: *mut LeanObject,
    mut v_x_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_339_) == 0 {
                    return v_x_338_;
                } else {
                    v_key_340_ = lean_ctor_get(v_x_339_, 0);
                    v_tail_341_ = lean_ctor_get(v_x_339_, 2);
                    lean_inc(v_key_340_);
                    v___x_342_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_342_, 0, v_key_340_);
                    lean_ctor_set(v___x_342_, 1, v_x_338_);
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
    mut v_x_344_: *mut LeanObject,
    mut v_x_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ =
        l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v_x_344_, v_x_345_);
    lean_dec(v_x_345_);
    return v_res_346_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_domain(mut v_s_347_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = lean_box(0);
    v___x_349_ =
        l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_domain_spec__0(v___x_348_, v_s_347_);
    return v___x_349_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_domain___boxed(
    mut v_s_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Lean_Meta_FVarSubst_domain(v_s_350_);
    lean_dec(v_s_350_);
    return v_res_351_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_any(
    mut v_p_352_: *mut LeanObject,
    mut v_s_353_: *mut LeanObject,
) -> u8 {
    let mut v___x_354_: u8 = 0;
    v___x_354_ = l_Lean_AssocList_any___redArg(v_p_352_, v_s_353_);
    return v___x_354_;
}
pub unsafe fn l_Lean_Meta_FVarSubst_any___boxed(
    mut v_p_355_: *mut LeanObject,
    mut v_s_356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_357_: u8 = 0;
    let mut v_r_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lean_Meta_FVarSubst_any(v_p_355_, v_s_356_);
    v_r_358_ = lean_box((v_res_357_) as usize);
    return v_r_358_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(
    mut v_t_359_: *mut LeanObject,
    mut v_x_360_: *mut LeanObject,
    mut v_x_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_361_) == 0 {
                    lean_dec(v_t_359_);
                    return v_x_360_;
                } else {
                    v_key_362_ = lean_ctor_get(v_x_361_, 0);
                    lean_inc(v_key_362_);
                    v_value_363_ = lean_ctor_get(v_x_361_, 1);
                    lean_inc(v_value_363_);
                    v_tail_364_ = lean_ctor_get(v_x_361_, 2);
                    lean_inc(v_tail_364_);
                    lean_dec_ref_known(v_x_361_, 3);
                    lean_inc(v_t_359_);
                    v___x_365_ = l_Lean_Meta_FVarSubst_apply(v_t_359_, v_value_363_);
                    lean_dec(v_value_363_);
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
    mut v_s_368_: *mut LeanObject,
    mut v_t_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_t_369_);
    v___x_370_ = l_Lean_AssocList_foldlM___at___00Lean_Meta_FVarSubst_append_spec__0(
        v_t_369_, v_t_369_, v_s_368_,
    );
    return v___x_370_;
}
pub unsafe fn l_Lean_LocalDecl_applyFVarSubst(
    mut v_s_371_: *mut LeanObject,
    mut v_x_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_index_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bi_377_: u8 = 0;
    let mut v_kind_378_: u8 = 0;
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v_index_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_392_: u8 = 0;
    let mut v_kind_393_: u8 = 0;
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_372_) == 0 {
                    v_index_373_ = lean_ctor_get(v_x_372_, 0);
                    v_fvarId_374_ = lean_ctor_get(v_x_372_, 1);
                    v_userName_375_ = lean_ctor_get(v_x_372_, 2);
                    v_type_376_ = lean_ctor_get(v_x_372_, 3);
                    v_bi_377_ = lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    );
                    v_kind_378_ = lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_386_ = (!lean_is_exclusive(v_x_372_)) as u8;
                    if v_isSharedCheck_386_ == 0 {
                        v___x_380_ = v_x_372_;
                        v_isShared_381_ = v_isSharedCheck_386_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_type_376_);
                        lean_inc(v_userName_375_);
                        lean_inc(v_fvarId_374_);
                        lean_inc(v_index_373_);
                        lean_dec(v_x_372_);
                        v___x_380_ = lean_box(0);
                        v_isShared_381_ = v_isSharedCheck_386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_index_387_ = lean_ctor_get(v_x_372_, 0);
                    v_fvarId_388_ = lean_ctor_get(v_x_372_, 1);
                    v_userName_389_ = lean_ctor_get(v_x_372_, 2);
                    v_type_390_ = lean_ctor_get(v_x_372_, 3);
                    v_value_391_ = lean_ctor_get(v_x_372_, 4);
                    v_nondep_392_ = lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_kind_393_ = lean_ctor_get_uint8(
                        v_x_372_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_402_ = (!lean_is_exclusive(v_x_372_)) as u8;
                    if v_isSharedCheck_402_ == 0 {
                        v___x_395_ = v_x_372_;
                        v_isShared_396_ = v_isSharedCheck_402_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_value_391_);
                        lean_inc(v_type_390_);
                        lean_inc(v_userName_389_);
                        lean_inc(v_fvarId_388_);
                        lean_inc(v_index_387_);
                        lean_dec(v_x_372_);
                        v___x_395_ = lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_402_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_382_ = l_Lean_Meta_FVarSubst_apply(v_s_371_, v_type_376_);
                lean_dec_ref(v_type_376_);
                if v_isShared_381_ == 0 {
                    lean_ctor_set(v___x_380_, 3, v___x_382_);
                    v___x_384_ = v___x_380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_385_, 0, v_index_373_);
                    lean_ctor_set(v_reuseFailAlloc_385_, 1, v_fvarId_374_);
                    lean_ctor_set(v_reuseFailAlloc_385_, 2, v_userName_375_);
                    lean_ctor_set(v_reuseFailAlloc_385_, 3, v___x_382_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_385_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_bi_377_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_385_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
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
                lean_inc(v_s_371_);
                v___x_397_ = l_Lean_Meta_FVarSubst_apply(v_s_371_, v_type_390_);
                lean_dec_ref(v_type_390_);
                v___x_398_ = l_Lean_Meta_FVarSubst_apply(v_s_371_, v_value_391_);
                lean_dec_ref(v_value_391_);
                if v_isShared_396_ == 0 {
                    lean_ctor_set(v___x_395_, 4, v___x_398_);
                    lean_ctor_set(v___x_395_, 3, v___x_397_);
                    v___x_400_ = v___x_395_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 5, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_401_, 0, v_index_387_);
                    lean_ctor_set(v_reuseFailAlloc_401_, 1, v_fvarId_388_);
                    lean_ctor_set(v_reuseFailAlloc_401_, 2, v_userName_389_);
                    lean_ctor_set(v_reuseFailAlloc_401_, 3, v___x_397_);
                    lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_398_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_401_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_nondep_392_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_401_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
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
    mut v_s_403_: *mut LeanObject,
    mut v_e_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Meta_FVarSubst_apply(v_s_403_, v_e_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Expr_applyFVarSubst___boxed(
    mut v_s_406_: *mut LeanObject,
    mut v_e_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_408_: *mut LeanObject = core::ptr::null_mut();
    v_res_408_ = l_Lean_Expr_applyFVarSubst(v_s_406_, v_e_407_);
    lean_dec_ref(v_e_407_);
    return v_res_408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_LocalContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_instInhabitedFVarSubst_default = _init_l_Lean_Meta_instInhabitedFVarSubst_default();
    lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst_default);
    l_Lean_Meta_instInhabitedFVarSubst = _init_l_Lean_Meta_instInhabitedFVarSubst();
    lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst);
    l_Lean_Meta_FVarSubst_empty = _init_l_Lean_Meta_FVarSubst_empty();
    lean_mark_persistent(l_Lean_Meta_FVarSubst_empty);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_FVarSubst(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_FVarSubst(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_LocalContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ReplaceExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_FVarSubst(builtin);
}
