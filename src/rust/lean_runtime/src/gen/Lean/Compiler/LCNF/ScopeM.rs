// Lean compiler output
// Module: Lean.Compiler.LCNF.ScopeM
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::l_Lean_FVarIdSet_insert;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag,
};
pub static l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0_value
)
    as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(
    mut v_a_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    v___x_218_ = lean_st_ref_get(v_a_216_);
    v___x_219_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_219_, 0, v___x_218_);
    return v___x_219_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope___redArg___boxed(
    mut v_a_220_: *mut LeanObject,
    mut v_a_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_220_);
    lean_dec(v_a_220_);
    return v_res_222_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope(
    mut v_a_223_: *mut LeanObject,
    mut v_a_224_: *mut LeanObject,
    mut v_a_225_: *mut LeanObject,
    mut v_a_226_: *mut LeanObject,
    mut v_a_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    v___x_229_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_223_);
    return v___x_229_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope___boxed(
    mut v_a_230_: *mut LeanObject,
    mut v_a_231_: *mut LeanObject,
    mut v_a_232_: *mut LeanObject,
    mut v_a_233_: *mut LeanObject,
    mut v_a_234_: *mut LeanObject,
    mut v_a_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_236_: *mut LeanObject = core::ptr::null_mut();
    v_res_236_ =
        l_Lean_Compiler_LCNF_ScopeM_getScope(v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
    lean_dec(v_a_234_);
    lean_dec_ref(v_a_233_);
    lean_dec(v_a_232_);
    lean_dec_ref(v_a_231_);
    lean_dec(v_a_230_);
    return v_res_236_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(
    mut v_newScope_237_: *mut LeanObject,
    mut v_a_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    v___x_240_ = lean_st_ref_set(v_a_238_, v_newScope_237_);
    v___x_241_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_241_, 0, v___x_240_);
    return v___x_241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope___redArg___boxed(
    mut v_newScope_242_: *mut LeanObject,
    mut v_a_243_: *mut LeanObject,
    mut v_a_244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_245_: *mut LeanObject = core::ptr::null_mut();
    v_res_245_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_242_, v_a_243_);
    lean_dec(v_a_243_);
    return v_res_245_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope(
    mut v_newScope_246_: *mut LeanObject,
    mut v_a_247_: *mut LeanObject,
    mut v_a_248_: *mut LeanObject,
    mut v_a_249_: *mut LeanObject,
    mut v_a_250_: *mut LeanObject,
    mut v_a_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    v___x_253_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_246_, v_a_247_);
    return v___x_253_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope___boxed(
    mut v_newScope_254_: *mut LeanObject,
    mut v_a_255_: *mut LeanObject,
    mut v_a_256_: *mut LeanObject,
    mut v_a_257_: *mut LeanObject,
    mut v_a_258_: *mut LeanObject,
    mut v_a_259_: *mut LeanObject,
    mut v_a_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Compiler_LCNF_ScopeM_setScope(
        v_newScope_254_,
        v_a_255_,
        v_a_256_,
        v_a_257_,
        v_a_258_,
        v_a_259_,
    );
    lean_dec(v_a_259_);
    lean_dec_ref(v_a_258_);
    lean_dec(v_a_257_);
    lean_dec_ref(v_a_256_);
    lean_dec(v_a_255_);
    return v_res_261_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(
    mut v_a_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    v___x_264_ = lean_box(1);
    v___x_265_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v___x_264_, v_a_262_);
    return v___x_265_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg___boxed(
    mut v_a_266_: *mut LeanObject,
    mut v_a_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_266_);
    lean_dec(v_a_266_);
    return v_res_268_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope(
    mut v_a_269_: *mut LeanObject,
    mut v_a_270_: *mut LeanObject,
    mut v_a_271_: *mut LeanObject,
    mut v_a_272_: *mut LeanObject,
    mut v_a_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    v___x_275_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_269_);
    return v___x_275_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed(
    mut v_a_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
    mut v_a_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_282_: *mut LeanObject = core::ptr::null_mut();
    v_res_282_ =
        l_Lean_Compiler_LCNF_ScopeM_clearScope(v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
    lean_dec(v_a_280_);
    lean_dec_ref(v_a_279_);
    lean_dec(v_a_278_);
    lean_dec_ref(v_a_277_);
    lean_dec(v_a_276_);
    return v_res_282_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(
    mut v_x_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_284_: *mut LeanObject = core::ptr::null_mut();
    v_fst_284_ = lean_ctor_get(v_x_283_, 0);
    lean_inc(v_fst_284_);
    return v_fst_284_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed(
    mut v_x_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_286_: *mut LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(v_x_285_);
    lean_dec_ref(v_x_285_);
    return v_res_286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(
    mut v___x_287_: *mut LeanObject,
    mut v_x_288_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_287_);
    return v___x_287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed(
    mut v___x_289_: *mut LeanObject,
    mut v_x_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_291_: *mut LeanObject = core::ptr::null_mut();
    v_res_291_ =
        l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(v___x_289_, v_x_290_);
    lean_dec(v_x_290_);
    lean_dec(v___x_289_);
    return v_res_291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2(
    mut v_toFunctor_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
    mut v_inst_294_: *mut LeanObject,
    mut v_x_295_: *mut LeanObject,
    mut v___f_296_: *mut LeanObject,
    mut v_scope_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v_map_298_ = lean_ctor_get(v_toFunctor_292_, 0);
    lean_inc(v_map_298_);
    lean_dec_ref(v_toFunctor_292_);
    v___x_299_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_setScope___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___x_299_, 0, v_scope_297_);
    v___x_300_ = lean_apply_2(v_inst_293_, lean_box(0), v___x_299_);
    v___f_301_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_301_, 0, v___x_300_);
    v_y_302_ = lean_apply_4(v_inst_294_, lean_box(0), lean_box(0), v_x_295_, v___f_301_);
    v___x_303_ = lean_apply_4(v_map_298_, lean_box(0), lean_box(0), v___f_296_, v_y_302_);
    return v___x_303_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(
    mut v_inst_305_: *mut LeanObject,
    mut v_inst_306_: *mut LeanObject,
    mut v_inst_307_: *mut LeanObject,
    mut v_x_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_309_ = lean_ctor_get(v_inst_306_, 0);
    lean_inc_ref(v_toApplicative_309_);
    v_toBind_310_ = lean_ctor_get(v_inst_306_, 1);
    lean_inc(v_toBind_310_);
    lean_dec_ref(v_inst_306_);
    v_toFunctor_311_ = lean_ctor_get(v_toApplicative_309_, 0);
    lean_inc_ref(v_toFunctor_311_);
    lean_dec_ref(v_toApplicative_309_);
    v___f_312_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0;
    v___x_313_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_getScope___boxed as *mut core::ffi::c_void,
        6,
        0,
    );
    lean_inc(v_inst_305_);
    v___x_314_ = lean_apply_2(v_inst_305_, lean_box(0), v___x_313_);
    v___f_315_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_315_, 0, v_toFunctor_311_);
    lean_closure_set(v___f_315_, 1, v_inst_305_);
    lean_closure_set(v___f_315_, 2, v_inst_307_);
    lean_closure_set(v___f_315_, 3, v_x_308_);
    lean_closure_set(v___f_315_, 4, v___f_312_);
    v___x_316_ = lean_apply_4(
        v_toBind_310_,
        lean_box(0),
        lean_box(0),
        v___x_314_,
        v___f_315_,
    );
    return v___x_316_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope(
    mut v_m_317_: *mut LeanObject,
    mut v_00_u03b1_318_: *mut LeanObject,
    mut v_inst_319_: *mut LeanObject,
    mut v_inst_320_: *mut LeanObject,
    mut v_inst_321_: *mut LeanObject,
    mut v_x_322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_323_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(
        v_inst_319_,
        v_inst_320_,
        v_inst_321_,
        v_x_322_,
    );
    return v___x_323_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(
    mut v_x_324_: *mut LeanObject,
    mut v_____r_325_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_324_);
    return v_x_324_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed(
    mut v_x_326_: *mut LeanObject,
    mut v_____r_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_328_: *mut LeanObject = core::ptr::null_mut();
    v_res_328_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(v_x_326_, v_____r_327_);
    lean_dec(v_x_326_);
    return v_res_328_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(
    mut v_inst_329_: *mut LeanObject,
    mut v_inst_330_: *mut LeanObject,
    mut v_inst_331_: *mut LeanObject,
    mut v_x_332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_333_ = lean_ctor_get(v_inst_330_, 1);
    v___f_334_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_334_, 0, v_x_332_);
    v___x_335_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed as *mut core::ffi::c_void,
        6,
        0,
    );
    lean_inc(v_inst_329_);
    v___x_336_ = lean_apply_2(v_inst_329_, lean_box(0), v___x_335_);
    lean_inc(v_toBind_333_);
    v___x_337_ = lean_apply_4(
        v_toBind_333_,
        lean_box(0),
        lean_box(0),
        v___x_336_,
        v___f_334_,
    );
    v___x_338_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(
        v_inst_329_,
        v_inst_330_,
        v_inst_331_,
        v___x_337_,
    );
    return v___x_338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope(
    mut v_m_339_: *mut LeanObject,
    mut v_00_u03b1_340_: *mut LeanObject,
    mut v_inst_341_: *mut LeanObject,
    mut v_inst_342_: *mut LeanObject,
    mut v_inst_343_: *mut LeanObject,
    mut v_x_344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    v___x_345_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(
        v_inst_341_,
        v_inst_342_,
        v_inst_343_,
        v_x_344_,
    );
    return v___x_345_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(
    mut v_k_346_: *mut LeanObject,
    mut v_t_347_: *mut LeanObject,
) -> u8 {
    let mut v_k_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: u8 = 0;
    let mut v___x_353_: u8 = 0;
    let mut v___x_355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_347_) == 0 {
                    v_k_348_ = lean_ctor_get(v_t_347_, 1);
                    v_l_349_ = lean_ctor_get(v_t_347_, 3);
                    v_r_350_ = lean_ctor_get(v_t_347_, 4);
                    v___x_351_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_346_, v_k_348_);
                    match v___x_351_ {
                        0 => {
                            v_t_347_ = v_l_349_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_353_ = 1;
                            return v___x_353_;
                        }
                        _ => {
                            v_t_347_ = v_r_350_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_355_ = 0;
                    return v___x_355_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg___boxed(
    mut v_k_356_: *mut LeanObject,
    mut v_t_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_358_: u8 = 0;
    let mut v_r_359_: *mut LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_356_, v_t_357_);
    lean_dec(v_t_357_);
    lean_dec(v_k_356_);
    v_r_359_ = lean_box((v_res_358_) as usize);
    return v_r_359_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(
    mut v_fvarId_360_: *mut LeanObject,
    mut v_a_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v___x_368_: u8 = 0;
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_363_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_361_);
                v_a_364_ = lean_ctor_get(v___x_363_, 0);
                v_isSharedCheck_373_ = (!lean_is_exclusive(v___x_363_)) as u8;
                if v_isSharedCheck_373_ == 0 {
                    v___x_366_ = v___x_363_;
                    v_isShared_367_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_364_);
                    lean_dec(v___x_363_);
                    v___x_366_ = lean_box(0);
                    v_isShared_367_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_368_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_fvarId_360_, v_a_364_);
                lean_dec(v_a_364_);
                v___x_369_ = lean_box((v___x_368_) as usize);
                if v_isShared_367_ == 0 {
                    lean_ctor_set(v___x_366_, 0, v___x_369_);
                    v___x_371_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
                    v___x_371_ = v_reuseFailAlloc_372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg___boxed(
    mut v_fvarId_374_: *mut LeanObject,
    mut v_a_375_: *mut LeanObject,
    mut v_a_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_377_: *mut LeanObject = core::ptr::null_mut();
    v_res_377_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_374_, v_a_375_);
    lean_dec(v_a_375_);
    lean_dec(v_fvarId_374_);
    return v_res_377_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope(
    mut v_fvarId_378_: *mut LeanObject,
    mut v_a_379_: *mut LeanObject,
    mut v_a_380_: *mut LeanObject,
    mut v_a_381_: *mut LeanObject,
    mut v_a_382_: *mut LeanObject,
    mut v_a_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_385_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_378_, v_a_379_);
    return v___x_385_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope___boxed(
    mut v_fvarId_386_: *mut LeanObject,
    mut v_a_387_: *mut LeanObject,
    mut v_a_388_: *mut LeanObject,
    mut v_a_389_: *mut LeanObject,
    mut v_a_390_: *mut LeanObject,
    mut v_a_391_: *mut LeanObject,
    mut v_a_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_393_: *mut LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Lean_Compiler_LCNF_ScopeM_isInScope(
        v_fvarId_386_,
        v_a_387_,
        v_a_388_,
        v_a_389_,
        v_a_390_,
        v_a_391_,
    );
    lean_dec(v_a_391_);
    lean_dec_ref(v_a_390_);
    lean_dec(v_a_389_);
    lean_dec_ref(v_a_388_);
    lean_dec(v_a_387_);
    lean_dec(v_fvarId_386_);
    return v_res_393_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(
    mut v_00_u03b2_394_: *mut LeanObject,
    mut v_k_395_: *mut LeanObject,
    mut v_t_396_: *mut LeanObject,
) -> u8 {
    let mut v___x_397_: u8 = 0;
    v___x_397_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_395_, v_t_396_);
    return v___x_397_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___boxed(
    mut v_00_u03b2_398_: *mut LeanObject,
    mut v_k_399_: *mut LeanObject,
    mut v_t_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_401_: u8 = 0;
    let mut v_r_402_: *mut LeanObject = core::ptr::null_mut();
    v_res_401_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(
            v_00_u03b2_398_,
            v_k_399_,
            v_t_400_,
        );
    lean_dec(v_t_400_);
    lean_dec(v_k_399_);
    v_r_402_ = lean_box((v_res_401_) as usize);
    return v_r_402_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(
    mut v_fvarId_403_: *mut LeanObject,
    mut v_a_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = lean_st_ref_take(v_a_404_);
    v___x_407_ = l_Lean_FVarIdSet_insert(v___x_406_, v_fvarId_403_);
    v___x_408_ = lean_st_ref_set(v_a_404_, v___x_407_);
    v___x_409_ = lean_box(0);
    v___x_410_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_410_, 0, v___x_409_);
    return v___x_410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg___boxed(
    mut v_fvarId_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v_a_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_411_, v_a_412_);
    lean_dec(v_a_412_);
    return v_res_414_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope(
    mut v_fvarId_415_: *mut LeanObject,
    mut v_a_416_: *mut LeanObject,
    mut v_a_417_: *mut LeanObject,
    mut v_a_418_: *mut LeanObject,
    mut v_a_419_: *mut LeanObject,
    mut v_a_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_415_, v_a_416_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope___boxed(
    mut v_fvarId_423_: *mut LeanObject,
    mut v_a_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
    mut v_a_426_: *mut LeanObject,
    mut v_a_427_: *mut LeanObject,
    mut v_a_428_: *mut LeanObject,
    mut v_a_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_430_: *mut LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Lean_Compiler_LCNF_ScopeM_addToScope(
        v_fvarId_423_,
        v_a_424_,
        v_a_425_,
        v_a_426_,
        v_a_427_,
        v_a_428_,
    );
    lean_dec(v_a_428_);
    lean_dec_ref(v_a_427_);
    lean_dec(v_a_426_);
    lean_dec_ref(v_a_425_);
    lean_dec(v_a_424_);
    return v_res_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ScopeM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ScopeM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ScopeM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ScopeM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ScopeM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ScopeM(builtin);
}
