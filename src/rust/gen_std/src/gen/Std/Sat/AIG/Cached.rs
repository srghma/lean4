// Lean compiler output
// Module: Std.Sat.AIG.Cached
// Imports: Std.Sat.AIG.Lemmas Init.Omega
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_lor,
    lean_nat_mul,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Sat::AIG::Basic::{
    l_Std_Sat_AIG_getConstant___redArg, l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg,
    l_Std_Sat_AIG_instHashableDecl_hash___boxed,
};
use crate::r#gen::Std::Sat::AIG::Lemmas::{
    initialize_Std_Sat_AIG_Lemmas, runtime_initialize_Std_Sat_AIG_Lemmas,
};
pub static l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(
    mut v_inst_195_: *mut crate::leanh::LeanObject,
    mut v_a_196_: *mut crate::leanh::LeanObject,
    mut v_b_197_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_198_: u8 = 0;
    v___x_198_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_195_, v_a_196_, v_b_197_);
    return v___x_198_;
}
pub unsafe fn l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(
    mut v_inst_199_: *mut crate::leanh::LeanObject,
    mut v_a_200_: *mut crate::leanh::LeanObject,
    mut v_b_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_202_: u8 = 0;
    let mut v_r_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(v_inst_199_, v_a_200_, v_b_201_);
    v_r_203_ = crate::leanh::lean_box((v_res_202_) as usize);
    return v_r_203_;
}
pub unsafe fn l_Std_Sat_AIG_mkAtomCached___redArg(
    mut v_inst_204_: *mut crate::leanh::LeanObject,
    mut v_inst_205_: *mut crate::leanh::LeanObject,
    mut v_aig_206_: *mut crate::leanh::LeanObject,
    mut v_n_207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_212_: u8 = 0;
    let mut v___f_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: u8 = 0;
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_208_ = crate::leanh::lean_ctor_get(v_aig_206_, 0);
                v_cache_209_ = crate::leanh::lean_ctor_get(v_aig_206_, 1);
                v_isSharedCheck_234_ = (!crate::leanh::lean_is_exclusive(v_aig_206_)) as u8;
                if v_isSharedCheck_234_ == 0 {
                    v___x_211_ = v_aig_206_;
                    v_isShared_212_ = v_isSharedCheck_234_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_209_);
                    crate::leanh::lean_inc(v_decls_208_);
                    crate::leanh::lean_dec(v_aig_206_);
                    v___x_211_ = crate::leanh::lean_box(0);
                    v_isShared_212_ = v_isSharedCheck_234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_213_ = crate::leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_213_, 0, v_inst_205_);
                v_decl_214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v_decl_214_, 0, v_n_207_);
                v___x_215_ = crate::leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_215_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_215_, 1, v_inst_204_);
                v___f_216_ = crate::leanh::lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_216_, 0, v___f_213_);
                crate::leanh::lean_inc_ref(v_decl_214_);
                crate::leanh::lean_inc_ref(v___x_215_);
                crate::leanh::lean_inc_ref(v___f_216_);
                v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___f_216_,
                    v___x_215_,
                    v_cache_209_,
                    v_decl_214_,
                );
                if crate::leanh::lean_obj_tag(v___x_217_) == 0 {
                    v_g_218_ = lean_array_get_size(v_decls_208_);
                    crate::leanh::lean_inc_ref(v_decl_214_);
                    v_cache_219_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v___f_216_,
                        v___x_215_,
                        v_cache_209_,
                        v_decl_214_,
                        v_g_218_,
                    );
                    v_decls_220_ = lean_array_push(v_decls_208_, v_decl_214_);
                    if v_isShared_212_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_211_, 1, v_cache_219_);
                        crate::leanh::lean_ctor_set(v___x_211_, 0, v_decls_220_);
                        v___x_222_ = v___x_211_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_226_, 0, v_decls_220_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_226_, 1, v_cache_219_);
                        v___x_222_ = v_reuseFailAlloc_226_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_216_);
                    crate::leanh::lean_dec_ref(v___x_215_);
                    crate::leanh::lean_dec_ref_known(v_decl_214_, 1);
                    v_val_227_ = crate::leanh::lean_ctor_get(v___x_217_, 0);
                    crate::leanh::lean_inc(v_val_227_);
                    crate::leanh::lean_dec_ref_known(v___x_217_, 1);
                    if v_isShared_212_ == 0 {
                        v___x_229_ = v___x_211_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_233_, 0, v_decls_208_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_233_, 1, v_cache_209_);
                        v___x_229_ = v_reuseFailAlloc_233_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_223_ = 0;
                v___x_224_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_224_, 0, v_g_218_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_224_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_223_,
                );
                v___x_225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_225_, 0, v___x_222_);
                crate::leanh::lean_ctor_set(v___x_225_, 1, v___x_224_);
                return v___x_225_;
            }
            3 => {
                v___x_230_ = 0;
                v___x_231_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_231_, 0, v_val_227_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_231_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_230_,
                );
                v___x_232_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_232_, 0, v___x_229_);
                crate::leanh::lean_ctor_set(v___x_232_, 1, v___x_231_);
                return v___x_232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkAtomCached(
    mut v_00_u03b1_235_: *mut crate::leanh::LeanObject,
    mut v_inst_236_: *mut crate::leanh::LeanObject,
    mut v_inst_237_: *mut crate::leanh::LeanObject,
    mut v_aig_238_: *mut crate::leanh::LeanObject,
    mut v_n_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ =
        l_Std_Sat_AIG_mkAtomCached___redArg(v_inst_236_, v_inst_237_, v_aig_238_, v_n_239_);
    return v___x_240_;
}
pub unsafe fn l_Std_Sat_AIG_mkConstCached___redArg(
    mut v_val_241_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_242_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_243_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_243_, 0, v___x_242_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_243_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_val_241_,
    );
    return v___x_243_;
}
pub unsafe fn l_Std_Sat_AIG_mkConstCached___redArg___boxed(
    mut v_val_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_245_: u8 = 0;
    let mut v_res_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_245_ = (crate::leanh::lean_unbox(v_val_244_) as u8);
    v_res_246_ = l_Std_Sat_AIG_mkConstCached___redArg(v_val_boxed_245_);
    return v_res_246_;
}
pub unsafe fn l_Std_Sat_AIG_mkConstCached(
    mut v_00_u03b1_247_: *mut crate::leanh::LeanObject,
    mut v_inst_248_: *mut crate::leanh::LeanObject,
    mut v_inst_249_: *mut crate::leanh::LeanObject,
    mut v_aig_250_: *mut crate::leanh::LeanObject,
    mut v_val_251_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_253_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_253_, 0, v___x_252_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_253_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_val_251_,
    );
    return v___x_253_;
}
pub unsafe fn l_Std_Sat_AIG_mkConstCached___boxed(
    mut v_00_u03b1_254_: *mut crate::leanh::LeanObject,
    mut v_inst_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
    mut v_aig_257_: *mut crate::leanh::LeanObject,
    mut v_val_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_259_: u8 = 0;
    let mut v_res_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_259_ = (crate::leanh::lean_unbox(v_val_258_) as u8);
    v_res_260_ = l_Std_Sat_AIG_mkConstCached(
        v_00_u03b1_254_,
        v_inst_255_,
        v_inst_256_,
        v_aig_257_,
        v_val_boxed_259_,
    );
    crate::leanh::lean_dec_ref(v_aig_257_);
    crate::leanh::lean_dec_ref(v_inst_256_);
    crate::leanh::lean_dec_ref(v_inst_255_);
    return v_res_260_;
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached_go___redArg(
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_inst_265_: *mut crate::leanh::LeanObject,
    mut v_aig_266_: *mut crate::leanh::LeanObject,
    mut v_input_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_272_: u8 = 0;
    let mut v_decls_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_277_: u8 = 0;
    let mut v_gate_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_279_: u8 = 0;
    let mut v_gate_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_281_: u8 = 0;
    let mut v___f_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_298_: u8 = 0;
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_303_: u8 = 0;
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsVal_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhsVal_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v_val_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: u8 = 0;
    let mut v_val_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: u8 = 0;
    let mut v_val_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: u8 = 0;
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: u8 = 0;
    let mut v_g_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_336_: u8 = 0;
    let mut v_unused_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_341_: u8 = 0;
    let mut v_val_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_351_: u8 = 0;
    let mut v_unused_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_354_: u8 = 0;
    let mut v_isSharedCheck_355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_268_ = crate::leanh::lean_ctor_get(v_input_267_, 0);
                v_rhs_269_ = crate::leanh::lean_ctor_get(v_input_267_, 1);
                v_isSharedCheck_355_ = (!crate::leanh::lean_is_exclusive(v_input_267_)) as u8;
                if v_isSharedCheck_355_ == 0 {
                    v___x_271_ = v_input_267_;
                    v_isShared_272_ = v_isSharedCheck_355_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_269_);
                    crate::leanh::lean_inc(v_lhs_268_);
                    crate::leanh::lean_dec(v_input_267_);
                    v___x_271_ = crate::leanh::lean_box(0);
                    v_isShared_272_ = v_isSharedCheck_355_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_273_ = crate::leanh::lean_ctor_get(v_aig_266_, 0);
                v_cache_274_ = crate::leanh::lean_ctor_get(v_aig_266_, 1);
                v_isSharedCheck_354_ = (!crate::leanh::lean_is_exclusive(v_aig_266_)) as u8;
                if v_isSharedCheck_354_ == 0 {
                    v___x_276_ = v_aig_266_;
                    v_isShared_277_ = v_isSharedCheck_354_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_274_);
                    crate::leanh::lean_inc(v_decls_273_);
                    crate::leanh::lean_dec(v_aig_266_);
                    v___x_276_ = crate::leanh::lean_box(0);
                    v_isShared_277_ = v_isSharedCheck_354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_278_ = crate::leanh::lean_ctor_get(v_lhs_268_, 0);
                crate::leanh::lean_inc(v_gate_278_);
                v_invert_279_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_268_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_gate_280_ = crate::leanh::lean_ctor_get(v_rhs_269_, 0);
                v_invert_281_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_269_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___f_282_ = crate::leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_282_, 0, v_inst_265_);
                v___x_283_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_284_ = lean_nat_mul(v_gate_278_, v___x_283_);
                v___x_285_ = l_Bool_toNat(v_invert_279_);
                v___x_286_ = lean_nat_lor(v___x_284_, v___x_285_);
                crate::leanh::lean_dec(v___x_285_);
                crate::leanh::lean_dec(v___x_284_);
                v___x_287_ = lean_nat_mul(v_gate_280_, v___x_283_);
                v___x_288_ = l_Bool_toNat(v_invert_281_);
                v___x_289_ = lean_nat_lor(v___x_287_, v___x_288_);
                crate::leanh::lean_dec(v___x_288_);
                crate::leanh::lean_dec(v___x_287_);
                if v_isShared_272_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_271_, 2);
                    crate::leanh::lean_ctor_set(v___x_271_, 1, v___x_289_);
                    crate::leanh::lean_ctor_set(v___x_271_, 0, v___x_286_);
                    v_decl_291_ = v___x_271_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_353_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_289_);
                    v_decl_291_ = v_reuseFailAlloc_353_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_292_ = crate::leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_292_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_292_, 1, v_inst_264_);
                v___f_293_ = crate::leanh::lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_293_, 0, v___f_282_);
                crate::leanh::lean_inc_ref(v_decl_291_);
                crate::leanh::lean_inc_ref(v___x_292_);
                crate::leanh::lean_inc_ref(v___f_293_);
                v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___f_293_,
                    v___x_292_,
                    v_cache_274_,
                    v_decl_291_,
                );
                if crate::leanh::lean_obj_tag(v___x_294_) == 0 {
                    crate::leanh::lean_inc(v_gate_280_);
                    crate::leanh::lean_inc_ref(v_cache_274_);
                    crate::leanh::lean_inc_ref(v_decls_273_);
                    if v_isShared_277_ == 0 {
                        v___x_296_ = v___x_276_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_338_, 0, v_decls_273_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_338_, 1, v_cache_274_);
                        v___x_296_ = v_reuseFailAlloc_338_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_293_);
                    crate::leanh::lean_dec_ref(v___x_292_);
                    crate::leanh::lean_dec_ref(v_decl_291_);
                    crate::leanh::lean_dec(v_gate_278_);
                    crate::leanh::lean_dec_ref(v_lhs_268_);
                    v_isSharedCheck_351_ = (!crate::leanh::lean_is_exclusive(v_rhs_269_)) as u8;
                    if v_isSharedCheck_351_ == 0 {
                        v_unused_352_ = crate::leanh::lean_ctor_get(v_rhs_269_, 0);
                        crate::leanh::lean_dec(v_unused_352_);
                        v___x_340_ = v_rhs_269_;
                        v_isShared_341_ = v_isSharedCheck_351_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_rhs_269_);
                        v___x_340_ = crate::leanh::lean_box(0);
                        v_isShared_341_ = v_isSharedCheck_351_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v_lhsVal_312_ = l_Std_Sat_AIG_getConstant___redArg(v___x_296_, v_lhs_268_);
                crate::leanh::lean_dec_ref(v_lhs_268_);
                v_rhsVal_313_ = l_Std_Sat_AIG_getConstant___redArg(v___x_296_, v_rhs_269_);
                v_isSharedCheck_336_ = (!crate::leanh::lean_is_exclusive(v_rhs_269_)) as u8;
                if v_isSharedCheck_336_ == 0 {
                    v_unused_337_ = crate::leanh::lean_ctor_get(v_rhs_269_, 0);
                    crate::leanh::lean_dec(v_unused_337_);
                    v___x_315_ = v_rhs_269_;
                    v_isShared_316_ = v_isSharedCheck_336_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_rhs_269_);
                    v___x_315_ = crate::leanh::lean_box(0);
                    v_isShared_316_ = v_isSharedCheck_336_;
                    state = 9;
                    continue;
                }
            }
            5 => {
                v___x_299_ = crate::leanh::lean_unsigned_to_nat(0);
                v_ref_300_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v_ref_300_, 0, v___x_299_);
                crate::leanh::lean_ctor_set_uint8(
                    v_ref_300_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_298_,
                );
                v___x_301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_301_, 0, v___x_296_);
                crate::leanh::lean_ctor_set(v___x_301_, 1, v_ref_300_);
                return v___x_301_;
            }
            6 => {
                if v___y_303_ == 0 {
                    crate::leanh::lean_dec(v_gate_278_);
                    v___y_298_ = v___y_303_;
                    state = 5;
                    continue;
                } else {
                    v___x_304_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_304_, 0, v_gate_278_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_304_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_279_,
                    );
                    v___x_305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_305_, 0, v___x_296_);
                    crate::leanh::lean_ctor_set(v___x_305_, 1, v___x_304_);
                    return v___x_305_;
                }
            }
            7 => {
                v___x_307_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_307_, 0, v_gate_280_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_307_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_281_,
                );
                v___x_308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_308_, 0, v___x_296_);
                crate::leanh::lean_ctor_set(v___x_308_, 1, v___x_307_);
                return v___x_308_;
            }
            8 => {
                v_ref_310_ = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
                v___x_311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_311_, 0, v___x_296_);
                crate::leanh::lean_ctor_set(v___x_311_, 1, v_ref_310_);
                return v___x_311_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_lhsVal_312_) == 1 {
                    crate::leanh::lean_del_object(v___x_315_);
                    crate::leanh::lean_dec_ref(v___f_293_);
                    crate::leanh::lean_dec_ref(v___x_292_);
                    crate::leanh::lean_dec_ref(v_decl_291_);
                    crate::leanh::lean_dec(v_gate_278_);
                    crate::leanh::lean_dec_ref(v_cache_274_);
                    crate::leanh::lean_dec_ref(v_decls_273_);
                    v_val_317_ = crate::leanh::lean_ctor_get(v_lhsVal_312_, 0);
                    crate::leanh::lean_inc(v_val_317_);
                    crate::leanh::lean_dec_ref_known(v_lhsVal_312_, 1);
                    v___x_318_ = (crate::leanh::lean_unbox(v_val_317_) as u8);
                    crate::leanh::lean_dec(v_val_317_);
                    if v___x_318_ == 0 {
                        crate::leanh::lean_dec(v_rhsVal_313_);
                        crate::leanh::lean_dec(v_gate_280_);
                        state = 8;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_rhsVal_313_) == 1 {
                            v_val_319_ = crate::leanh::lean_ctor_get(v_rhsVal_313_, 0);
                            crate::leanh::lean_inc(v_val_319_);
                            crate::leanh::lean_dec_ref_known(v_rhsVal_313_, 1);
                            v___x_320_ = (crate::leanh::lean_unbox(v_val_319_) as u8);
                            crate::leanh::lean_dec(v_val_319_);
                            if v___x_320_ == 0 {
                                crate::leanh::lean_dec(v_gate_280_);
                                state = 8;
                                continue;
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_rhsVal_313_);
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_lhsVal_312_);
                    if crate::leanh::lean_obj_tag(v_rhsVal_313_) == 1 {
                        crate::leanh::lean_dec_ref(v___f_293_);
                        crate::leanh::lean_dec_ref(v___x_292_);
                        crate::leanh::lean_dec_ref(v_decl_291_);
                        crate::leanh::lean_dec(v_gate_280_);
                        crate::leanh::lean_dec_ref(v_cache_274_);
                        crate::leanh::lean_dec_ref(v_decls_273_);
                        v_val_321_ = crate::leanh::lean_ctor_get(v_rhsVal_313_, 0);
                        crate::leanh::lean_inc(v_val_321_);
                        crate::leanh::lean_dec_ref_known(v_rhsVal_313_, 1);
                        v___x_322_ = (crate::leanh::lean_unbox(v_val_321_) as u8);
                        crate::leanh::lean_dec(v_val_321_);
                        if v___x_322_ == 0 {
                            crate::leanh::lean_del_object(v___x_315_);
                            crate::leanh::lean_dec(v_gate_278_);
                            state = 8;
                            continue;
                        } else {
                            if v_isShared_316_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_315_, 0, v_gate_278_);
                                v___x_324_ = v___x_315_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_326_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_326_, 0, v_gate_278_);
                                v___x_324_ = v_reuseFailAlloc_326_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_rhsVal_313_);
                        v___x_327_ = lean_nat_dec_eq(v_gate_278_, v_gate_280_);
                        crate::leanh::lean_dec(v_gate_280_);
                        if v___x_327_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_296_);
                            crate::leanh::lean_dec(v_gate_278_);
                            v_g_328_ = lean_array_get_size(v_decls_273_);
                            crate::leanh::lean_inc_ref(v_decl_291_);
                            v_cache_329_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                                v___f_293_,
                                v___x_292_,
                                v_cache_274_,
                                v_decl_291_,
                                v_g_328_,
                            );
                            v_decls_330_ = lean_array_push(v_decls_273_, v_decl_291_);
                            v___x_331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_331_, 0, v_decls_330_);
                            crate::leanh::lean_ctor_set(v___x_331_, 1, v_cache_329_);
                            if v_isShared_316_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_315_, 0, v_g_328_);
                                v___x_333_ = v___x_315_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_335_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_335_, 0, v_g_328_);
                                v___x_333_ = v_reuseFailAlloc_335_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_315_);
                            crate::leanh::lean_dec_ref(v___f_293_);
                            crate::leanh::lean_dec_ref(v___x_292_);
                            crate::leanh::lean_dec_ref(v_decl_291_);
                            crate::leanh::lean_dec_ref(v_cache_274_);
                            crate::leanh::lean_dec_ref(v_decls_273_);
                            if v_invert_279_ == 0 {
                                if v_invert_281_ == 0 {
                                    v___y_303_ = v___x_327_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_gate_278_);
                                    v___y_298_ = v_invert_279_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___y_303_ = v_invert_281_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_324_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_279_,
                );
                v___x_325_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_325_, 0, v___x_296_);
                crate::leanh::lean_ctor_set(v___x_325_, 1, v___x_324_);
                return v___x_325_;
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_333_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_327_,
                );
                v___x_334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_334_, 0, v___x_331_);
                crate::leanh::lean_ctor_set(v___x_334_, 1, v___x_333_);
                return v___x_334_;
            }
            12 => {
                v_val_342_ = crate::leanh::lean_ctor_get(v___x_294_, 0);
                crate::leanh::lean_inc(v_val_342_);
                crate::leanh::lean_dec_ref_known(v___x_294_, 1);
                if v_isShared_277_ == 0 {
                    v___x_344_ = v___x_276_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_350_, 0, v_decls_273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_350_, 1, v_cache_274_);
                    v___x_344_ = v_reuseFailAlloc_350_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_345_ = 0;
                if v_isShared_341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_340_, 0, v_val_342_);
                    v___x_347_ = v___x_340_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_349_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_349_, 0, v_val_342_);
                    v___x_347_ = v_reuseFailAlloc_349_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_345_,
                );
                v___x_348_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_348_, 0, v___x_344_);
                crate::leanh::lean_ctor_set(v___x_348_, 1, v___x_347_);
                return v___x_348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached_go(
    mut v_00_u03b1_356_: *mut crate::leanh::LeanObject,
    mut v_inst_357_: *mut crate::leanh::LeanObject,
    mut v_inst_358_: *mut crate::leanh::LeanObject,
    mut v_aig_359_: *mut crate::leanh::LeanObject,
    mut v_input_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_361_ =
        l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_357_, v_inst_358_, v_aig_359_, v_input_360_);
    return v___x_361_;
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached___redArg(
    mut v_inst_362_: *mut crate::leanh::LeanObject,
    mut v_inst_363_: *mut crate::leanh::LeanObject,
    mut v_aig_364_: *mut crate::leanh::LeanObject,
    mut v_input_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v_gate_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: u8 = 0;
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_366_ = crate::leanh::lean_ctor_get(v_input_365_, 0);
                v_rhs_367_ = crate::leanh::lean_ctor_get(v_input_365_, 1);
                v_isSharedCheck_382_ = (!crate::leanh::lean_is_exclusive(v_input_365_)) as u8;
                if v_isSharedCheck_382_ == 0 {
                    v___x_369_ = v_input_365_;
                    v_isShared_370_ = v_isSharedCheck_382_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_367_);
                    crate::leanh::lean_inc(v_lhs_366_);
                    crate::leanh::lean_dec(v_input_365_);
                    v___x_369_ = crate::leanh::lean_box(0);
                    v_isShared_370_ = v_isSharedCheck_382_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_371_ = crate::leanh::lean_ctor_get(v_lhs_366_, 0);
                v_gate_372_ = crate::leanh::lean_ctor_get(v_rhs_367_, 0);
                v___x_373_ = lean_nat_dec_lt(v_gate_371_, v_gate_372_);
                if v___x_373_ == 0 {
                    if v_isShared_370_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_369_, 1, v_lhs_366_);
                        crate::leanh::lean_ctor_set(v___x_369_, 0, v_rhs_367_);
                        v___x_375_ = v___x_369_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_377_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_377_, 0, v_rhs_367_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_377_, 1, v_lhs_366_);
                        v___x_375_ = v_reuseFailAlloc_377_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_370_ == 0 {
                        v___x_379_ = v___x_369_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_381_, 0, v_lhs_366_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_381_, 1, v_rhs_367_);
                        v___x_379_ = v_reuseFailAlloc_381_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_376_ = l_Std_Sat_AIG_mkGateCached_go___redArg(
                    v_inst_362_,
                    v_inst_363_,
                    v_aig_364_,
                    v___x_375_,
                );
                return v___x_376_;
            }
            3 => {
                v___x_380_ = l_Std_Sat_AIG_mkGateCached_go___redArg(
                    v_inst_362_,
                    v_inst_363_,
                    v_aig_364_,
                    v___x_379_,
                );
                return v___x_380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGateCached(
    mut v_00_u03b1_383_: *mut crate::leanh::LeanObject,
    mut v_inst_384_: *mut crate::leanh::LeanObject,
    mut v_inst_385_: *mut crate::leanh::LeanObject,
    mut v_aig_386_: *mut crate::leanh::LeanObject,
    mut v_input_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ =
        l_Std_Sat_AIG_mkGateCached___redArg(v_inst_384_, v_inst_385_, v_aig_386_, v_input_387_);
    return v___x_388_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_Cached(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_Cached(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_Cached(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Cached(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_Cached(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_Cached(builtin);
}
