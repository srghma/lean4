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
pub static l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(
    mut v_a_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_218_ = lean_st_ref_get(v_a_216_);
    v___x_219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_219_, 0, v___x_218_);
    return v___x_219_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope___redArg___boxed(
    mut v_a_220_: *mut crate::leanh::LeanObject,
    mut v_a_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_220_);
    crate::leanh::lean_dec(v_a_220_);
    return v_res_222_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope(
    mut v_a_223_: *mut crate::leanh::LeanObject,
    mut v_a_224_: *mut crate::leanh::LeanObject,
    mut v_a_225_: *mut crate::leanh::LeanObject,
    mut v_a_226_: *mut crate::leanh::LeanObject,
    mut v_a_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_223_);
    return v___x_229_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_getScope___boxed(
    mut v_a_230_: *mut crate::leanh::LeanObject,
    mut v_a_231_: *mut crate::leanh::LeanObject,
    mut v_a_232_: *mut crate::leanh::LeanObject,
    mut v_a_233_: *mut crate::leanh::LeanObject,
    mut v_a_234_: *mut crate::leanh::LeanObject,
    mut v_a_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ =
        l_Lean_Compiler_LCNF_ScopeM_getScope(v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
    crate::leanh::lean_dec(v_a_234_);
    crate::leanh::lean_dec_ref(v_a_233_);
    crate::leanh::lean_dec(v_a_232_);
    crate::leanh::lean_dec_ref(v_a_231_);
    crate::leanh::lean_dec(v_a_230_);
    return v_res_236_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(
    mut v_newScope_237_: *mut crate::leanh::LeanObject,
    mut v_a_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = lean_st_ref_set(v_a_238_, v_newScope_237_);
    v___x_241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_241_, 0, v___x_240_);
    return v___x_241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope___redArg___boxed(
    mut v_newScope_242_: *mut crate::leanh::LeanObject,
    mut v_a_243_: *mut crate::leanh::LeanObject,
    mut v_a_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_245_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_242_, v_a_243_);
    crate::leanh::lean_dec(v_a_243_);
    return v_res_245_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope(
    mut v_newScope_246_: *mut crate::leanh::LeanObject,
    mut v_a_247_: *mut crate::leanh::LeanObject,
    mut v_a_248_: *mut crate::leanh::LeanObject,
    mut v_a_249_: *mut crate::leanh::LeanObject,
    mut v_a_250_: *mut crate::leanh::LeanObject,
    mut v_a_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_253_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_246_, v_a_247_);
    return v___x_253_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_setScope___boxed(
    mut v_newScope_254_: *mut crate::leanh::LeanObject,
    mut v_a_255_: *mut crate::leanh::LeanObject,
    mut v_a_256_: *mut crate::leanh::LeanObject,
    mut v_a_257_: *mut crate::leanh::LeanObject,
    mut v_a_258_: *mut crate::leanh::LeanObject,
    mut v_a_259_: *mut crate::leanh::LeanObject,
    mut v_a_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Compiler_LCNF_ScopeM_setScope(
        v_newScope_254_,
        v_a_255_,
        v_a_256_,
        v_a_257_,
        v_a_258_,
        v_a_259_,
    );
    crate::leanh::lean_dec(v_a_259_);
    crate::leanh::lean_dec_ref(v_a_258_);
    crate::leanh::lean_dec(v_a_257_);
    crate::leanh::lean_dec_ref(v_a_256_);
    crate::leanh::lean_dec(v_a_255_);
    return v_res_261_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(
    mut v_a_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_264_ = crate::leanh::lean_box(1);
    v___x_265_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v___x_264_, v_a_262_);
    return v___x_265_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg___boxed(
    mut v_a_266_: *mut crate::leanh::LeanObject,
    mut v_a_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_266_);
    crate::leanh::lean_dec(v_a_266_);
    return v_res_268_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope(
    mut v_a_269_: *mut crate::leanh::LeanObject,
    mut v_a_270_: *mut crate::leanh::LeanObject,
    mut v_a_271_: *mut crate::leanh::LeanObject,
    mut v_a_272_: *mut crate::leanh::LeanObject,
    mut v_a_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_275_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_269_);
    return v___x_275_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed(
    mut v_a_276_: *mut crate::leanh::LeanObject,
    mut v_a_277_: *mut crate::leanh::LeanObject,
    mut v_a_278_: *mut crate::leanh::LeanObject,
    mut v_a_279_: *mut crate::leanh::LeanObject,
    mut v_a_280_: *mut crate::leanh::LeanObject,
    mut v_a_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_282_ =
        l_Lean_Compiler_LCNF_ScopeM_clearScope(v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
    crate::leanh::lean_dec(v_a_280_);
    crate::leanh::lean_dec_ref(v_a_279_);
    crate::leanh::lean_dec(v_a_278_);
    crate::leanh::lean_dec_ref(v_a_277_);
    crate::leanh::lean_dec(v_a_276_);
    return v_res_282_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(
    mut v_x_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_284_ = crate::leanh::lean_ctor_get(v_x_283_, 0);
    crate::leanh::lean_inc(v_fst_284_);
    return v_fst_284_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed(
    mut v_x_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(v_x_285_);
    crate::leanh::lean_dec_ref(v_x_285_);
    return v_res_286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(
    mut v___x_287_: *mut crate::leanh::LeanObject,
    mut v_x_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_287_);
    return v___x_287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed(
    mut v___x_289_: *mut crate::leanh::LeanObject,
    mut v_x_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ =
        l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(v___x_289_, v_x_290_);
    crate::leanh::lean_dec(v_x_290_);
    crate::leanh::lean_dec(v___x_289_);
    return v_res_291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2(
    mut v_toFunctor_292_: *mut crate::leanh::LeanObject,
    mut v_inst_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
    mut v_x_295_: *mut crate::leanh::LeanObject,
    mut v___f_296_: *mut crate::leanh::LeanObject,
    mut v_scope_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_298_ = crate::leanh::lean_ctor_get(v_toFunctor_292_, 0);
    crate::leanh::lean_inc(v_map_298_);
    crate::leanh::lean_dec_ref(v_toFunctor_292_);
    v___x_299_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_setScope___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___x_299_, 0, v_scope_297_);
    v___x_300_ = crate::leanh::lean_apply_2(v_inst_293_, crate::leanh::lean_box(0), v___x_299_);
    v___f_301_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_301_, 0, v___x_300_);
    v_y_302_ = crate::leanh::lean_apply_4(
        v_inst_294_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_295_,
        v___f_301_,
    );
    v___x_303_ = crate::leanh::lean_apply_4(
        v_map_298_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_296_,
        v_y_302_,
    );
    return v___x_303_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_inst_306_: *mut crate::leanh::LeanObject,
    mut v_inst_307_: *mut crate::leanh::LeanObject,
    mut v_x_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_309_ = crate::leanh::lean_ctor_get(v_inst_306_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_309_);
    v_toBind_310_ = crate::leanh::lean_ctor_get(v_inst_306_, 1);
    crate::leanh::lean_inc(v_toBind_310_);
    crate::leanh::lean_dec_ref(v_inst_306_);
    v_toFunctor_311_ = crate::leanh::lean_ctor_get(v_toApplicative_309_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_311_);
    crate::leanh::lean_dec_ref(v_toApplicative_309_);
    v___f_312_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0;
    v___x_313_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_getScope___boxed as *mut core::ffi::c_void,
        6,
        0,
    );
    crate::leanh::lean_inc(v_inst_305_);
    v___x_314_ = crate::leanh::lean_apply_2(v_inst_305_, crate::leanh::lean_box(0), v___x_313_);
    v___f_315_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_315_, 0, v_toFunctor_311_);
    crate::leanh::lean_closure_set(v___f_315_, 1, v_inst_305_);
    crate::leanh::lean_closure_set(v___f_315_, 2, v_inst_307_);
    crate::leanh::lean_closure_set(v___f_315_, 3, v_x_308_);
    crate::leanh::lean_closure_set(v___f_315_, 4, v___f_312_);
    v___x_316_ = crate::leanh::lean_apply_4(
        v_toBind_310_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_314_,
        v___f_315_,
    );
    return v___x_316_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope(
    mut v_m_317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_318_: *mut crate::leanh::LeanObject,
    mut v_inst_319_: *mut crate::leanh::LeanObject,
    mut v_inst_320_: *mut crate::leanh::LeanObject,
    mut v_inst_321_: *mut crate::leanh::LeanObject,
    mut v_x_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(
        v_inst_319_,
        v_inst_320_,
        v_inst_321_,
        v_x_322_,
    );
    return v___x_323_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(
    mut v_x_324_: *mut crate::leanh::LeanObject,
    mut v_____r_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_324_);
    return v_x_324_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed(
    mut v_x_326_: *mut crate::leanh::LeanObject,
    mut v_____r_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_328_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(v_x_326_, v_____r_327_);
    crate::leanh::lean_dec(v_x_326_);
    return v_res_328_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(
    mut v_inst_329_: *mut crate::leanh::LeanObject,
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_inst_331_: *mut crate::leanh::LeanObject,
    mut v_x_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_333_ = crate::leanh::lean_ctor_get(v_inst_330_, 1);
    v___f_334_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_334_, 0, v_x_332_);
    v___x_335_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed as *mut core::ffi::c_void,
        6,
        0,
    );
    crate::leanh::lean_inc(v_inst_329_);
    v___x_336_ = crate::leanh::lean_apply_2(v_inst_329_, crate::leanh::lean_box(0), v___x_335_);
    crate::leanh::lean_inc(v_toBind_333_);
    v___x_337_ = crate::leanh::lean_apply_4(
        v_toBind_333_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_m_339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_340_: *mut crate::leanh::LeanObject,
    mut v_inst_341_: *mut crate::leanh::LeanObject,
    mut v_inst_342_: *mut crate::leanh::LeanObject,
    mut v_inst_343_: *mut crate::leanh::LeanObject,
    mut v_x_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(
        v_inst_341_,
        v_inst_342_,
        v_inst_343_,
        v_x_344_,
    );
    return v___x_345_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(
    mut v_k_346_: *mut crate::leanh::LeanObject,
    mut v_t_347_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: u8 = 0;
    let mut v___x_353_: u8 = 0;
    let mut v___x_355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_347_) == 0 {
                    v_k_348_ = crate::leanh::lean_ctor_get(v_t_347_, 1);
                    v_l_349_ = crate::leanh::lean_ctor_get(v_t_347_, 3);
                    v_r_350_ = crate::leanh::lean_ctor_get(v_t_347_, 4);
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
    mut v_k_356_: *mut crate::leanh::LeanObject,
    mut v_t_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_358_: u8 = 0;
    let mut v_r_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_356_, v_t_357_);
    crate::leanh::lean_dec(v_t_357_);
    crate::leanh::lean_dec(v_k_356_);
    v_r_359_ = crate::leanh::lean_box((v_res_358_) as usize);
    return v_r_359_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(
    mut v_fvarId_360_: *mut crate::leanh::LeanObject,
    mut v_a_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v___x_368_: u8 = 0;
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_363_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_361_);
                v_a_364_ = crate::leanh::lean_ctor_get(v___x_363_, 0);
                v_isSharedCheck_373_ = (!crate::leanh::lean_is_exclusive(v___x_363_)) as u8;
                if v_isSharedCheck_373_ == 0 {
                    v___x_366_ = v___x_363_;
                    v_isShared_367_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_364_);
                    crate::leanh::lean_dec(v___x_363_);
                    v___x_366_ = crate::leanh::lean_box(0);
                    v_isShared_367_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_368_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_fvarId_360_, v_a_364_);
                crate::leanh::lean_dec(v_a_364_);
                v___x_369_ = crate::leanh::lean_box((v___x_368_) as usize);
                if v_isShared_367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_366_, 0, v___x_369_);
                    v___x_371_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
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
    mut v_fvarId_374_: *mut crate::leanh::LeanObject,
    mut v_a_375_: *mut crate::leanh::LeanObject,
    mut v_a_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_377_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_374_, v_a_375_);
    crate::leanh::lean_dec(v_a_375_);
    crate::leanh::lean_dec(v_fvarId_374_);
    return v_res_377_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope(
    mut v_fvarId_378_: *mut crate::leanh::LeanObject,
    mut v_a_379_: *mut crate::leanh::LeanObject,
    mut v_a_380_: *mut crate::leanh::LeanObject,
    mut v_a_381_: *mut crate::leanh::LeanObject,
    mut v_a_382_: *mut crate::leanh::LeanObject,
    mut v_a_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_378_, v_a_379_);
    return v___x_385_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_isInScope___boxed(
    mut v_fvarId_386_: *mut crate::leanh::LeanObject,
    mut v_a_387_: *mut crate::leanh::LeanObject,
    mut v_a_388_: *mut crate::leanh::LeanObject,
    mut v_a_389_: *mut crate::leanh::LeanObject,
    mut v_a_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
    mut v_a_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Lean_Compiler_LCNF_ScopeM_isInScope(
        v_fvarId_386_,
        v_a_387_,
        v_a_388_,
        v_a_389_,
        v_a_390_,
        v_a_391_,
    );
    crate::leanh::lean_dec(v_a_391_);
    crate::leanh::lean_dec_ref(v_a_390_);
    crate::leanh::lean_dec(v_a_389_);
    crate::leanh::lean_dec_ref(v_a_388_);
    crate::leanh::lean_dec(v_a_387_);
    crate::leanh::lean_dec(v_fvarId_386_);
    return v_res_393_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(
    mut v_00_u03b2_394_: *mut crate::leanh::LeanObject,
    mut v_k_395_: *mut crate::leanh::LeanObject,
    mut v_t_396_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_397_: u8 = 0;
    v___x_397_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_395_, v_t_396_);
    return v___x_397_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___boxed(
    mut v_00_u03b2_398_: *mut crate::leanh::LeanObject,
    mut v_k_399_: *mut crate::leanh::LeanObject,
    mut v_t_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_401_: u8 = 0;
    let mut v_r_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_401_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(
            v_00_u03b2_398_,
            v_k_399_,
            v_t_400_,
        );
    crate::leanh::lean_dec(v_t_400_);
    crate::leanh::lean_dec(v_k_399_);
    v_r_402_ = crate::leanh::lean_box((v_res_401_) as usize);
    return v_r_402_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(
    mut v_fvarId_403_: *mut crate::leanh::LeanObject,
    mut v_a_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = lean_st_ref_take(v_a_404_);
    v___x_407_ = l_Lean_FVarIdSet_insert(v___x_406_, v_fvarId_403_);
    v___x_408_ = lean_st_ref_set(v_a_404_, v___x_407_);
    v___x_409_ = crate::leanh::lean_box(0);
    v___x_410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_410_, 0, v___x_409_);
    return v___x_410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg___boxed(
    mut v_fvarId_411_: *mut crate::leanh::LeanObject,
    mut v_a_412_: *mut crate::leanh::LeanObject,
    mut v_a_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_411_, v_a_412_);
    crate::leanh::lean_dec(v_a_412_);
    return v_res_414_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope(
    mut v_fvarId_415_: *mut crate::leanh::LeanObject,
    mut v_a_416_: *mut crate::leanh::LeanObject,
    mut v_a_417_: *mut crate::leanh::LeanObject,
    mut v_a_418_: *mut crate::leanh::LeanObject,
    mut v_a_419_: *mut crate::leanh::LeanObject,
    mut v_a_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_415_, v_a_416_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ScopeM_addToScope___boxed(
    mut v_fvarId_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
    mut v_a_426_: *mut crate::leanh::LeanObject,
    mut v_a_427_: *mut crate::leanh::LeanObject,
    mut v_a_428_: *mut crate::leanh::LeanObject,
    mut v_a_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Lean_Compiler_LCNF_ScopeM_addToScope(
        v_fvarId_423_,
        v_a_424_,
        v_a_425_,
        v_a_426_,
        v_a_427_,
        v_a_428_,
    );
    crate::leanh::lean_dec(v_a_428_);
    crate::leanh::lean_dec_ref(v_a_427_);
    crate::leanh::lean_dec(v_a_426_);
    crate::leanh::lean_dec_ref(v_a_425_);
    crate::leanh::lean_dec(v_a_424_);
    return v_res_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ScopeM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ScopeM(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ScopeM(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ScopeM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ScopeM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ScopeM(builtin);
}
