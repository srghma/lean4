// Lean compiler output
// Module: Lean.Meta.Sym.Arith.VarRename
// Imports: Init.Grind.Ring.CommSemiringAdapter Lean.Meta.Tactic.Grind.VarRename
use crate::ffi::{
    lean_array_get_size, lean_array_uget_borrowed, lean_nat_dec_eq, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Grind::Ring::CommSemiringAdapter::{
    initialize_Init_Grind_Ring_CommSemiringAdapter,
    runtime_initialize_Init_Grind_Ring_CommSemiringAdapter,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_VarRename, l_Lean_Meta_Grind_collectVar,
    runtime_initialize_Lean_Meta_Tactic_Grind_VarRename,
};
pub static l_Lean_Grind_CommRing_Expr_renameVars___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Grind_CommRing_Expr_renameVars___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Expr_renameVars___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(
    mut v_a_209_: *mut leanh::LeanObject,
    mut v_x_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_210_) == 0 {
                    v___x_211_ = leanh::lean_box(0);
                    return v___x_211_;
                } else {
                    v_key_212_ = leanh::lean_ctor_get(v_x_210_, 0);
                    v_value_213_ = leanh::lean_ctor_get(v_x_210_, 1);
                    v_tail_214_ = leanh::lean_ctor_get(v_x_210_, 2);
                    v___x_215_ = lean_nat_dec_eq(v_key_212_, v_a_209_);
                    if v___x_215_ == 0 {
                        v_x_210_ = v_tail_214_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_213_);
                        v___x_217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_217_, 0, v_value_213_);
                        return v___x_217_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg___boxed(
    mut v_a_218_: *mut leanh::LeanObject,
    mut v_x_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_220_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_a_218_, v_x_219_);
    leanh::lean_dec(v_x_219_);
    leanh::lean_dec(v_a_218_);
    return v_res_220_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(
    mut v_m_221_: *mut leanh::LeanObject,
    mut v_a_222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: u64 = 0;
    let mut v___x_226_: u64 = 0;
    let mut v___x_227_: u64 = 0;
    let mut v_fold_228_: u64 = 0;
    let mut v___x_229_: u64 = 0;
    let mut v___x_230_: u64 = 0;
    let mut v___x_231_: u64 = 0;
    let mut v___x_232_: usize = 0;
    let mut v___x_233_: usize = 0;
    let mut v___x_234_: usize = 0;
    let mut v___x_235_: usize = 0;
    let mut v___x_236_: usize = 0;
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_223_ = leanh::lean_ctor_get(v_m_221_, 1);
    v___x_224_ = lean_array_get_size(v_buckets_223_);
    v___x_225_ = lean_uint64_of_nat(v_a_222_);
    v___x_226_ = 32u64;
    v___x_227_ = lean_uint64_shift_right(v___x_225_, v___x_226_);
    v_fold_228_ = lean_uint64_xor(v___x_225_, v___x_227_);
    v___x_229_ = 16u64;
    v___x_230_ = lean_uint64_shift_right(v_fold_228_, v___x_229_);
    v___x_231_ = lean_uint64_xor(v_fold_228_, v___x_230_);
    v___x_232_ = lean_uint64_to_usize(v___x_231_);
    v___x_233_ = lean_usize_of_nat(v___x_224_);
    v___x_234_ = 1usize;
    v___x_235_ = lean_usize_sub(v___x_233_, v___x_234_);
    v___x_236_ = lean_usize_land(v___x_232_, v___x_235_);
    v___x_237_ = lean_array_uget_borrowed(v_buckets_223_, v___x_236_);
    v___x_238_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_a_222_, v___x_237_);
    return v___x_238_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(
    mut v_m_239_: *mut leanh::LeanObject,
    mut v_a_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_m_239_, v_a_240_);
    leanh::lean_dec(v_a_240_);
    leanh::lean_dec_ref(v_m_239_);
    return v_res_241_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_renameVars(
    mut v_pw_242_: *mut leanh::LeanObject,
    mut v_f_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_248_: u8 = 0;
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_244_ = leanh::lean_ctor_get(v_pw_242_, 0);
                v_k_245_ = leanh::lean_ctor_get(v_pw_242_, 1);
                v_isSharedCheck_258_ = (!leanh::lean_is_exclusive(v_pw_242_)) as u8;
                if v_isSharedCheck_258_ == 0 {
                    v___x_247_ = v_pw_242_;
                    v_isShared_248_ = v_isSharedCheck_258_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_k_245_);
                    leanh::lean_inc(v_x_244_);
                    leanh::lean_dec(v_pw_242_);
                    v___x_247_ = leanh::lean_box(0);
                    v_isShared_248_ = v_isSharedCheck_258_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_f_243_, v_x_244_);
                leanh::lean_dec(v_x_244_);
                if leanh::lean_obj_tag(v___x_249_) == 0 {
                    v___x_250_ = leanh::lean_unsigned_to_nat(0);
                    if v_isShared_248_ == 0 {
                        leanh::lean_ctor_set(v___x_247_, 0, v___x_250_);
                        v___x_252_ = v___x_247_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_253_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_253_, 1, v_k_245_);
                        v___x_252_ = v_reuseFailAlloc_253_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_254_ = leanh::lean_ctor_get(v___x_249_, 0);
                    leanh::lean_inc(v_val_254_);
                    leanh::lean_dec_ref_known(v___x_249_, 1);
                    if v_isShared_248_ == 0 {
                        leanh::lean_ctor_set(v___x_247_, 0, v_val_254_);
                        v___x_256_ = v___x_247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_257_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_257_, 0, v_val_254_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_245_);
                        v___x_256_ = v_reuseFailAlloc_257_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_252_;
            }
            3 => {
                return v___x_256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_renameVars___boxed(
    mut v_pw_259_: *mut leanh::LeanObject,
    mut v_f_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Grind_CommRing_Power_renameVars(v_pw_259_, v_f_260_);
    leanh::lean_dec_ref(v_f_260_);
    return v_res_261_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(
    mut v_00_u03b2_262_: *mut leanh::LeanObject,
    mut v_m_263_: *mut leanh::LeanObject,
    mut v_a_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_m_263_, v_a_264_);
    return v___x_265_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(
    mut v_00_u03b2_266_: *mut leanh::LeanObject,
    mut v_m_267_: *mut leanh::LeanObject,
    mut v_a_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(v_00_u03b2_266_, v_m_267_, v_a_268_);
    leanh::lean_dec(v_a_268_);
    leanh::lean_dec_ref(v_m_267_);
    return v_res_269_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(
    mut v_00_u03b2_270_: *mut leanh::LeanObject,
    mut v_a_271_: *mut leanh::LeanObject,
    mut v_x_272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_273_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_a_271_, v_x_272_);
    return v___x_273_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_274_: *mut leanh::LeanObject,
    mut v_a_275_: *mut leanh::LeanObject,
    mut v_x_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(v_00_u03b2_274_, v_a_275_, v_x_276_);
    leanh::lean_dec(v_x_276_);
    leanh::lean_dec(v_a_275_);
    return v_res_277_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_renameVars(
    mut v_m_278_: *mut leanh::LeanObject,
    mut v_f_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_284_: u8 = 0;
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_m_278_) == 0 {
                    return v_m_278_;
                } else {
                    v_p_280_ = leanh::lean_ctor_get(v_m_278_, 0);
                    v_m_281_ = leanh::lean_ctor_get(v_m_278_, 1);
                    v_isSharedCheck_290_ = (!leanh::lean_is_exclusive(v_m_278_)) as u8;
                    if v_isSharedCheck_290_ == 0 {
                        v___x_283_ = v_m_278_;
                        v_isShared_284_ = v_isSharedCheck_290_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_m_281_);
                        leanh::lean_inc(v_p_280_);
                        leanh::lean_dec(v_m_278_);
                        v___x_283_ = leanh::lean_box(0);
                        v_isShared_284_ = v_isSharedCheck_290_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_285_ = l_Lean_Grind_CommRing_Power_renameVars(v_p_280_, v_f_279_);
                v___x_286_ = l_Lean_Grind_CommRing_Mon_renameVars(v_m_281_, v_f_279_);
                if v_isShared_284_ == 0 {
                    leanh::lean_ctor_set(v___x_283_, 1, v___x_286_);
                    leanh::lean_ctor_set(v___x_283_, 0, v___x_285_);
                    v___x_288_ = v___x_283_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_289_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_286_);
                    v___x_288_ = v_reuseFailAlloc_289_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_renameVars___boxed(
    mut v_m_291_: *mut leanh::LeanObject,
    mut v_f_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l_Lean_Grind_CommRing_Mon_renameVars(v_m_291_, v_f_292_);
    leanh::lean_dec_ref(v_f_292_);
    return v_res_293_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_renameVars(
    mut v_p_294_: *mut leanh::LeanObject,
    mut v_f_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_301_: u8 = 0;
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_294_) == 0 {
                    return v_p_294_;
                } else {
                    v_k_296_ = leanh::lean_ctor_get(v_p_294_, 0);
                    v_v_297_ = leanh::lean_ctor_get(v_p_294_, 1);
                    v_p_298_ = leanh::lean_ctor_get(v_p_294_, 2);
                    v_isSharedCheck_307_ = (!leanh::lean_is_exclusive(v_p_294_)) as u8;
                    if v_isSharedCheck_307_ == 0 {
                        v___x_300_ = v_p_294_;
                        v_isShared_301_ = v_isSharedCheck_307_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_p_298_);
                        leanh::lean_inc(v_v_297_);
                        leanh::lean_inc(v_k_296_);
                        leanh::lean_dec(v_p_294_);
                        v___x_300_ = leanh::lean_box(0);
                        v_isShared_301_ = v_isSharedCheck_307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_302_ = l_Lean_Grind_CommRing_Mon_renameVars(v_v_297_, v_f_295_);
                v___x_303_ = l_Lean_Grind_CommRing_Poly_renameVars(v_p_298_, v_f_295_);
                if v_isShared_301_ == 0 {
                    leanh::lean_ctor_set(v___x_300_, 2, v___x_303_);
                    leanh::lean_ctor_set(v___x_300_, 1, v___x_302_);
                    v___x_305_ = v___x_300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_306_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_306_, 0, v_k_296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_306_, 2, v___x_303_);
                    v___x_305_ = v_reuseFailAlloc_306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_renameVars___boxed(
    mut v_p_308_: *mut leanh::LeanObject,
    mut v_f_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_310_ = l_Lean_Grind_CommRing_Poly_renameVars(v_p_308_, v_f_309_);
    leanh::lean_dec_ref(v_f_309_);
    return v_res_310_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_renameVars(
    mut v_e_313_: *mut leanh::LeanObject,
    mut v_f_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_325_: u8 = 0;
    let mut v_a_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_329_: u8 = 0;
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_334_: u8 = 0;
    let mut v_a_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_339_: u8 = 0;
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_345_: u8 = 0;
    let mut v_a_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_350_: u8 = 0;
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_356_: u8 = 0;
    let mut v_a_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_361_: u8 = 0;
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_367_: u8 = 0;
    let mut v_a_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_372_: u8 = 0;
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_313_) {
                3 => {
                    v_i_315_ = leanh::lean_ctor_get(v_e_313_, 0);
                    v_isSharedCheck_325_ = (!leanh::lean_is_exclusive(v_e_313_)) as u8;
                    if v_isSharedCheck_325_ == 0 {
                        v___x_317_ = v_e_313_;
                        v_isShared_318_ = v_isSharedCheck_325_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_315_);
                        leanh::lean_dec(v_e_313_);
                        v___x_317_ = leanh::lean_box(0);
                        v_isShared_318_ = v_isSharedCheck_325_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_a_326_ = leanh::lean_ctor_get(v_e_313_, 0);
                    v_isSharedCheck_334_ = (!leanh::lean_is_exclusive(v_e_313_)) as u8;
                    if v_isSharedCheck_334_ == 0 {
                        v___x_328_ = v_e_313_;
                        v_isShared_329_ = v_isSharedCheck_334_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_326_);
                        leanh::lean_dec(v_e_313_);
                        v___x_328_ = leanh::lean_box(0);
                        v_isShared_329_ = v_isSharedCheck_334_;
                        state = 3;
                        continue;
                    }
                }
                5 => {
                    v_a_335_ = leanh::lean_ctor_get(v_e_313_, 0);
                    v_b_336_ = leanh::lean_ctor_get(v_e_313_, 1);
                    v_isSharedCheck_345_ = (!leanh::lean_is_exclusive(v_e_313_)) as u8;
                    if v_isSharedCheck_345_ == 0 {
                        v___x_338_ = v_e_313_;
                        v_isShared_339_ = v_isSharedCheck_345_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_b_336_);
                        leanh::lean_inc(v_a_335_);
                        leanh::lean_dec(v_e_313_);
                        v___x_338_ = leanh::lean_box(0);
                        v_isShared_339_ = v_isSharedCheck_345_;
                        state = 5;
                        continue;
                    }
                }
                6 => {
                    v_a_346_ = leanh::lean_ctor_get(v_e_313_, 0);
                    v_b_347_ = leanh::lean_ctor_get(v_e_313_, 1);
                    v_isSharedCheck_356_ = (!leanh::lean_is_exclusive(v_e_313_)) as u8;
                    if v_isSharedCheck_356_ == 0 {
                        v___x_349_ = v_e_313_;
                        v_isShared_350_ = v_isSharedCheck_356_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_b_347_);
                        leanh::lean_inc(v_a_346_);
                        leanh::lean_dec(v_e_313_);
                        v___x_349_ = leanh::lean_box(0);
                        v_isShared_350_ = v_isSharedCheck_356_;
                        state = 7;
                        continue;
                    }
                }
                7 => {
                    v_a_357_ = leanh::lean_ctor_get(v_e_313_, 0);
                    v_b_358_ = leanh::lean_ctor_get(v_e_313_, 1);
                    v_isSharedCheck_367_ = (!leanh::lean_is_exclusive(v_e_313_)) as u8;
                    if v_isSharedCheck_367_ == 0 {
                        v___x_360_ = v_e_313_;
                        v_isShared_361_ = v_isSharedCheck_367_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_b_358_);
                        leanh::lean_inc(v_a_357_);
                        leanh::lean_dec(v_e_313_);
                        v___x_360_ = leanh::lean_box(0);
                        v_isShared_361_ = v_isSharedCheck_367_;
                        state = 9;
                        continue;
                    }
                }
                8 => {
                    v_a_368_ = leanh::lean_ctor_get(v_e_313_, 0);
                    v_k_369_ = leanh::lean_ctor_get(v_e_313_, 1);
                    v_isSharedCheck_377_ = (!leanh::lean_is_exclusive(v_e_313_)) as u8;
                    if v_isSharedCheck_377_ == 0 {
                        v___x_371_ = v_e_313_;
                        v_isShared_372_ = v_isSharedCheck_377_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_369_);
                        leanh::lean_inc(v_a_368_);
                        leanh::lean_dec(v_e_313_);
                        v___x_371_ = leanh::lean_box(0);
                        v_isShared_372_ = v_isSharedCheck_377_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    return v_e_313_;
                }
            },
            1 => {
                v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_f_314_, v_i_315_);
                leanh::lean_dec(v_i_315_);
                if leanh::lean_obj_tag(v___x_319_) == 0 {
                    leanh::lean_del_object(v___x_317_);
                    v___x_320_ = l_Lean_Grind_CommRing_Expr_renameVars___closed__0;
                    return v___x_320_;
                } else {
                    v_val_321_ = leanh::lean_ctor_get(v___x_319_, 0);
                    leanh::lean_inc(v_val_321_);
                    leanh::lean_dec_ref_known(v___x_319_, 1);
                    if v_isShared_318_ == 0 {
                        leanh::lean_ctor_set(v___x_317_, 0, v_val_321_);
                        v___x_323_ = v___x_317_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_324_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_324_, 0, v_val_321_);
                        v___x_323_ = v_reuseFailAlloc_324_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_323_;
            }
            3 => {
                v___x_330_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_326_, v_f_314_);
                if v_isShared_329_ == 0 {
                    leanh::lean_ctor_set(v___x_328_, 0, v___x_330_);
                    v___x_332_ = v___x_328_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_333_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
                    v___x_332_ = v_reuseFailAlloc_333_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_332_;
            }
            5 => {
                v___x_340_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_335_, v_f_314_);
                v___x_341_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_336_, v_f_314_);
                if v_isShared_339_ == 0 {
                    leanh::lean_ctor_set(v___x_338_, 1, v___x_341_);
                    leanh::lean_ctor_set(v___x_338_, 0, v___x_340_);
                    v___x_343_ = v___x_338_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_344_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_341_);
                    v___x_343_ = v_reuseFailAlloc_344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_343_;
            }
            7 => {
                v___x_351_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_346_, v_f_314_);
                v___x_352_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_347_, v_f_314_);
                if v_isShared_350_ == 0 {
                    leanh::lean_ctor_set(v___x_349_, 1, v___x_352_);
                    leanh::lean_ctor_set(v___x_349_, 0, v___x_351_);
                    v___x_354_ = v___x_349_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_355_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_352_);
                    v___x_354_ = v_reuseFailAlloc_355_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_354_;
            }
            9 => {
                v___x_362_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_357_, v_f_314_);
                v___x_363_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_358_, v_f_314_);
                if v_isShared_361_ == 0 {
                    leanh::lean_ctor_set(v___x_360_, 1, v___x_363_);
                    leanh::lean_ctor_set(v___x_360_, 0, v___x_362_);
                    v___x_365_ = v___x_360_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_366_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
                    v___x_365_ = v_reuseFailAlloc_366_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_365_;
            }
            11 => {
                v___x_373_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_368_, v_f_314_);
                if v_isShared_372_ == 0 {
                    leanh::lean_ctor_set(v___x_371_, 0, v___x_373_);
                    v___x_375_ = v___x_371_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_369_);
                    v___x_375_ = v_reuseFailAlloc_376_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_renameVars___boxed(
    mut v_e_378_: *mut leanh::LeanObject,
    mut v_f_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_380_ = l_Lean_Grind_CommRing_Expr_renameVars(v_e_378_, v_f_379_);
    leanh::lean_dec_ref(v_f_379_);
    return v_res_380_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_collectVars(
    mut v_pw_381_: *mut leanh::LeanObject,
    mut v_a_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_383_ = leanh::lean_ctor_get(v_pw_381_, 0);
    leanh::lean_inc(v_x_383_);
    leanh::lean_dec_ref(v_pw_381_);
    v___x_384_ = l_Lean_Meta_Grind_collectVar(v_x_383_, v_a_382_);
    return v___x_384_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_collectVars(
    mut v_m_385_: *mut leanh::LeanObject,
    mut v_a_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_m_385_) == 0 {
                    return v_a_386_;
                } else {
                    v_p_387_ = leanh::lean_ctor_get(v_m_385_, 0);
                    leanh::lean_inc_ref(v_p_387_);
                    v_m_388_ = leanh::lean_ctor_get(v_m_385_, 1);
                    leanh::lean_inc(v_m_388_);
                    leanh::lean_dec_ref_known(v_m_385_, 2);
                    v___x_389_ = l_Lean_Grind_CommRing_Power_collectVars(v_p_387_, v_a_386_);
                    v_m_385_ = v_m_388_;
                    v_a_386_ = v___x_389_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_collectVars(
    mut v_p_391_: *mut leanh::LeanObject,
    mut v_a_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_391_) == 0 {
                    leanh::lean_dec_ref_known(v_p_391_, 1);
                    return v_a_392_;
                } else {
                    v_v_393_ = leanh::lean_ctor_get(v_p_391_, 1);
                    leanh::lean_inc(v_v_393_);
                    v_p_394_ = leanh::lean_ctor_get(v_p_391_, 2);
                    leanh::lean_inc_ref(v_p_394_);
                    leanh::lean_dec_ref_known(v_p_391_, 3);
                    v___x_395_ = l_Lean_Grind_CommRing_Mon_collectVars(v_v_393_, v_a_392_);
                    v_p_391_ = v_p_394_;
                    v_a_392_ = v___x_395_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_collectVars(
    mut v_e_397_: *mut leanh::LeanObject,
    mut v_a_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_397_) {
                3 => {
                    v_i_405_ = leanh::lean_ctor_get(v_e_397_, 0);
                    leanh::lean_inc(v_i_405_);
                    leanh::lean_dec_ref_known(v_e_397_, 1);
                    v___x_406_ = l_Lean_Meta_Grind_collectVar(v_i_405_, v_a_398_);
                    return v___x_406_;
                }
                4 => {
                    v_a_407_ = leanh::lean_ctor_get(v_e_397_, 0);
                    leanh::lean_inc_ref(v_a_407_);
                    leanh::lean_dec_ref_known(v_e_397_, 1);
                    v_e_397_ = v_a_407_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_409_ = leanh::lean_ctor_get(v_e_397_, 0);
                    leanh::lean_inc_ref(v_a_409_);
                    v_b_410_ = leanh::lean_ctor_get(v_e_397_, 1);
                    leanh::lean_inc_ref(v_b_410_);
                    leanh::lean_dec_ref_known(v_e_397_, 2);
                    v_a_400_ = v_a_409_;
                    v_b_401_ = v_b_410_;
                    v___y_402_ = v_a_398_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_a_411_ = leanh::lean_ctor_get(v_e_397_, 0);
                    leanh::lean_inc_ref(v_a_411_);
                    v_b_412_ = leanh::lean_ctor_get(v_e_397_, 1);
                    leanh::lean_inc_ref(v_b_412_);
                    leanh::lean_dec_ref_known(v_e_397_, 2);
                    v_a_400_ = v_a_411_;
                    v_b_401_ = v_b_412_;
                    v___y_402_ = v_a_398_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_a_413_ = leanh::lean_ctor_get(v_e_397_, 0);
                    leanh::lean_inc_ref(v_a_413_);
                    v_b_414_ = leanh::lean_ctor_get(v_e_397_, 1);
                    leanh::lean_inc_ref(v_b_414_);
                    leanh::lean_dec_ref_known(v_e_397_, 2);
                    v_a_400_ = v_a_413_;
                    v_b_401_ = v_b_414_;
                    v___y_402_ = v_a_398_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_a_415_ = leanh::lean_ctor_get(v_e_397_, 0);
                    leanh::lean_inc_ref(v_a_415_);
                    leanh::lean_dec_ref_known(v_e_397_, 2);
                    v_e_397_ = v_a_415_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_e_397_);
                    return v_a_398_;
                }
            },
            1 => {
                v___x_403_ = l_Lean_Grind_CommRing_Expr_collectVars(v_a_400_, v___y_402_);
                v_e_397_ = v_b_401_;
                v_a_398_ = v___x_403_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_VarRename(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_VarRename(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_VarRename(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
}