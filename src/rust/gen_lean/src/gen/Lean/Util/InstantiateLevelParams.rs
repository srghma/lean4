// Lean compiler output
// Module: Lean.Util.InstantiateLevelParams
// Imports: Lean.Util.ReplaceExpr
use crate::r#gen::Init::Data::List::Basic::{
    l_List_isEmpty___redArg, l_List_mapTR_loop___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Util::l_ptrEqList___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_hasLevelParam, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq,
};
use crate::r#gen::Lean::Level::l___private_Lean_Level_0__Lean_Level_substParams_go;
use crate::r#gen::Lean::Util::ReplaceExpr::{
    initialize_Lean_Util_ReplaceExpr, runtime_initialize_Lean_Util_ReplaceExpr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Util::ReplaceExpr::lean_replace_expr;
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___lam__0(
    mut v_s_301_: *mut crate::leanh::LeanObject,
    mut v_u_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_303_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_301_, v_u_302_);
    return v___x_303_;
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn(
    mut v_s_304_: *mut crate::leanh::LeanObject,
    mut v_e_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_306_: u8 = 0;
    v___x_306_ = l_Lean_Expr_hasLevelParam(v_e_305_);
    if v___x_306_ == 0 {
        let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_304_);
        v___x_307_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_307_, 0, v_e_305_);
        return v___x_307_;
    } else {
        match crate::leanh::lean_obj_tag(v_e_305_) {
            4 => {
                let mut v_declName_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_us_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_313_: u8 = 0;
                v_declName_308_ = crate::leanh::lean_ctor_get(v_e_305_, 0);
                v_us_309_ = crate::leanh::lean_ctor_get(v_e_305_, 1);
                v___f_310_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___lam__0 as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_310_, 0, v_s_304_);
                v___x_311_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_us_309_);
                v___x_312_ = l_List_mapTR_loop___redArg(v___f_310_, v_us_309_, v___x_311_);
                v___x_313_ = l_ptrEqList___redArg(v_us_309_, v___x_312_);
                if v___x_313_ == 0 {
                    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc(v_declName_308_);
                    crate::leanh::lean_dec_ref_known(v_e_305_, 2);
                    v___x_314_ = l_Lean_Expr_const___override(v_declName_308_, v___x_312_);
                    v___x_315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
                    return v___x_315_;
                } else {
                    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_312_);
                    v___x_316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_316_, 0, v_e_305_);
                    return v___x_316_;
                }
            }
            3 => {
                let mut v_u_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_319_: usize = 0;
                let mut v___x_320_: usize = 0;
                let mut v___x_321_: u8 = 0;
                v_u_317_ = crate::leanh::lean_ctor_get(v_e_305_, 0);
                crate::leanh::lean_inc(v_u_317_);
                v___x_318_ =
                    l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_304_, v_u_317_);
                v___x_319_ = lean_ptr_addr(v_u_317_);
                v___x_320_ = lean_ptr_addr(v___x_318_);
                v___x_321_ = lean_usize_dec_eq(v___x_319_, v___x_320_);
                if v___x_321_ == 0 {
                    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_e_305_, 1);
                    v___x_322_ = l_Lean_Expr_sort___override(v___x_318_);
                    v___x_323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_323_, 0, v___x_322_);
                    return v___x_323_;
                } else {
                    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_318_);
                    v___x_324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_324_, 0, v_e_305_);
                    return v___x_324_;
                }
            }
            _ => {
                let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_e_305_);
                crate::leanh::lean_dec_ref(v_s_304_);
                v___x_325_ = crate::leanh::lean_box(0);
                return v___x_325_;
            }
        }
    }
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsCore(
    mut v_s_326_: *mut crate::leanh::LeanObject,
    mut v_e_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_328_, 0, v_s_326_);
    v___x_329_ = lean_replace_expr(v___x_328_, v_e_327_);
    crate::leanh::lean_dec_ref(v___x_328_);
    return v___x_329_;
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsCore___boxed(
    mut v_s_330_: *mut crate::leanh::LeanObject,
    mut v_e_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Lean_Expr_instantiateLevelParamsCore(v_s_330_, v_e_331_);
    crate::leanh::lean_dec_ref(v_e_331_);
    return v_res_332_;
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(
    mut v_x_333_: *mut crate::leanh::LeanObject,
    mut v_x_334_: *mut crate::leanh::LeanObject,
    mut v_x_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u8 = 0;
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_333_) == 1 {
                    if crate::leanh::lean_obj_tag(v_x_334_) == 1 {
                        v_head_336_ = crate::leanh::lean_ctor_get(v_x_333_, 0);
                        v_tail_337_ = crate::leanh::lean_ctor_get(v_x_333_, 1);
                        v_head_338_ = crate::leanh::lean_ctor_get(v_x_334_, 0);
                        v_tail_339_ = crate::leanh::lean_ctor_get(v_x_334_, 1);
                        v___x_340_ = lean_name_eq(v_head_336_, v_x_335_);
                        if v___x_340_ == 0 {
                            v_x_333_ = v_tail_337_;
                            v_x_334_ = v_tail_339_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_338_);
                            v___x_342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_342_, 0, v_head_338_);
                            return v___x_342_;
                        }
                    } else {
                        v___x_343_ = crate::leanh::lean_box(0);
                        return v___x_343_;
                    }
                } else {
                    v___x_344_ = crate::leanh::lean_box(0);
                    return v___x_344_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed(
    mut v_x_345_: *mut crate::leanh::LeanObject,
    mut v_x_346_: *mut crate::leanh::LeanObject,
    mut v_x_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(
        v_x_345_, v_x_346_, v_x_347_,
    );
    crate::leanh::lean_dec(v_x_347_);
    crate::leanh::lean_dec(v_x_346_);
    crate::leanh::lean_dec(v_x_345_);
    return v_res_348_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(
    mut v_paramNames_349_: *mut crate::leanh::LeanObject,
    mut v_lvls_350_: *mut crate::leanh::LeanObject,
    mut v_a_351_: *mut crate::leanh::LeanObject,
    mut v_a_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_358_: u8 = 0;
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_351_) == 0 {
                    crate::leanh::lean_dec(v_lvls_350_);
                    crate::leanh::lean_dec(v_paramNames_349_);
                    v___x_353_ = l_List_reverse___redArg(v_a_352_);
                    return v___x_353_;
                } else {
                    v_head_354_ = crate::leanh::lean_ctor_get(v_a_351_, 0);
                    v_tail_355_ = crate::leanh::lean_ctor_get(v_a_351_, 1);
                    v_isSharedCheck_365_ = (!crate::leanh::lean_is_exclusive(v_a_351_)) as u8;
                    if v_isSharedCheck_365_ == 0 {
                        v___x_357_ = v_a_351_;
                        v_isShared_358_ = v_isSharedCheck_365_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_355_);
                        crate::leanh::lean_inc(v_head_354_);
                        crate::leanh::lean_dec(v_a_351_);
                        v___x_357_ = crate::leanh::lean_box(0);
                        v_isShared_358_ = v_isSharedCheck_365_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_lvls_350_);
                crate::leanh::lean_inc(v_paramNames_349_);
                v___x_359_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_359_, 0, v_paramNames_349_);
                crate::leanh::lean_closure_set(v___x_359_, 1, v_lvls_350_);
                v___x_360_ =
                    l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_359_, v_head_354_);
                if v_isShared_358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_357_, 1, v_a_352_);
                    crate::leanh::lean_ctor_set(v___x_357_, 0, v___x_360_);
                    v___x_362_ = v___x_357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_364_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_352_);
                    v___x_362_ = v_reuseFailAlloc_364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_351_ = v_tail_355_;
                v_a_352_ = v___x_362_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(
    mut v_paramNames_366_: *mut crate::leanh::LeanObject,
    mut v_lvls_367_: *mut crate::leanh::LeanObject,
    mut v_e_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: u8 = 0;
    v___x_369_ = l_Lean_Expr_hasLevelParam(v_e_368_);
    if v___x_369_ == 0 {
        let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_lvls_367_);
        crate::leanh::lean_dec(v_paramNames_366_);
        v___x_370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_370_, 0, v_e_368_);
        return v___x_370_;
    } else {
        match crate::leanh::lean_obj_tag(v_e_368_) {
            4 => {
                let mut v_declName_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_us_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_375_: u8 = 0;
                v_declName_371_ = crate::leanh::lean_ctor_get(v_e_368_, 0);
                v_us_372_ = crate::leanh::lean_ctor_get(v_e_368_, 1);
                v___x_373_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_us_372_);
                v___x_374_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(v_paramNames_366_, v_lvls_367_, v_us_372_, v___x_373_);
                v___x_375_ = l_ptrEqList___redArg(v_us_372_, v___x_374_);
                if v___x_375_ == 0 {
                    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc(v_declName_371_);
                    crate::leanh::lean_dec_ref_known(v_e_368_, 2);
                    v___x_376_ = l_Lean_Expr_const___override(v_declName_371_, v___x_374_);
                    v___x_377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_376_);
                    return v___x_377_;
                } else {
                    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_374_);
                    v___x_378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_378_, 0, v_e_368_);
                    return v___x_378_;
                }
            }
            3 => {
                let mut v_u_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_382_: usize = 0;
                let mut v___x_383_: usize = 0;
                let mut v___x_384_: u8 = 0;
                v_u_379_ = crate::leanh::lean_ctor_get(v_e_368_, 0);
                v___x_380_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_380_, 0, v_paramNames_366_);
                crate::leanh::lean_closure_set(v___x_380_, 1, v_lvls_367_);
                crate::leanh::lean_inc(v_u_379_);
                v___x_381_ =
                    l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_380_, v_u_379_);
                v___x_382_ = lean_ptr_addr(v_u_379_);
                v___x_383_ = lean_ptr_addr(v___x_381_);
                v___x_384_ = lean_usize_dec_eq(v___x_382_, v___x_383_);
                if v___x_384_ == 0 {
                    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_e_368_, 1);
                    v___x_385_ = l_Lean_Expr_sort___override(v___x_381_);
                    v___x_386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_386_, 0, v___x_385_);
                    return v___x_386_;
                } else {
                    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_381_);
                    v___x_387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_387_, 0, v_e_368_);
                    return v___x_387_;
                }
            }
            _ => {
                let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_e_368_);
                crate::leanh::lean_dec(v_lvls_367_);
                crate::leanh::lean_dec(v_paramNames_366_);
                v___x_388_ = crate::leanh::lean_box(0);
                return v___x_388_;
            }
        }
    }
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(
    mut v_paramNames_389_: *mut crate::leanh::LeanObject,
    mut v_lvls_390_: *mut crate::leanh::LeanObject,
    mut v_e_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_392_, 0, v_paramNames_389_);
    crate::leanh::lean_closure_set(v___x_392_, 1, v_lvls_390_);
    v___x_393_ = lean_replace_expr(v___x_392_, v_e_391_);
    crate::leanh::lean_dec_ref(v___x_392_);
    return v___x_393_;
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0___boxed(
    mut v_paramNames_394_: *mut crate::leanh::LeanObject,
    mut v_lvls_395_: *mut crate::leanh::LeanObject,
    mut v_e_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_397_ =
        l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(
            v_paramNames_394_,
            v_lvls_395_,
            v_e_396_,
        );
    crate::leanh::lean_dec_ref(v_e_396_);
    return v_res_397_;
}
pub unsafe fn l_Lean_Expr_instantiateLevelParams(
    mut v_e_398_: *mut crate::leanh::LeanObject,
    mut v_paramNames_399_: *mut crate::leanh::LeanObject,
    mut v_lvls_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_402_: u8 = 0;
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: u8 = 0;
    let mut v___x_405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_404_ = l_List_isEmpty___redArg(v_paramNames_399_);
                if v___x_404_ == 0 {
                    v___x_405_ = l_List_isEmpty___redArg(v_lvls_400_);
                    v___y_402_ = v___x_405_;
                    state = 1;
                    continue;
                } else {
                    v___y_402_ = v___x_404_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_402_ == 0 {
                    v___x_403_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(v_paramNames_399_, v_lvls_400_, v_e_398_);
                    return v___x_403_;
                } else {
                    crate::leanh::lean_dec(v_lvls_400_);
                    crate::leanh::lean_dec(v_paramNames_399_);
                    crate::leanh::lean_inc_ref(v_e_398_);
                    return v_e_398_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_instantiateLevelParams___boxed(
    mut v_e_406_: *mut crate::leanh::LeanObject,
    mut v_paramNames_407_: *mut crate::leanh::LeanObject,
    mut v_lvls_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Lean_Expr_instantiateLevelParams(v_e_406_, v_paramNames_407_, v_lvls_408_);
    crate::leanh::lean_dec_ref(v_e_406_);
    return v_res_409_;
}
pub unsafe fn l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(
    mut v_paramNames_410_: *mut crate::leanh::LeanObject,
    mut v_lvls_411_: *mut crate::leanh::LeanObject,
    mut v_e_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_417_: u8 = 0;
    let mut v_d_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_421_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: usize = 0;
    let mut v___x_426_: usize = 0;
    let mut v___x_427_: u8 = 0;
    let mut v___x_428_: usize = 0;
    let mut v___x_429_: usize = 0;
    let mut v___x_430_: u8 = 0;
    let mut v_binderName_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_434_: u8 = 0;
    let mut v_d_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_438_: u8 = 0;
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: u8 = 0;
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: usize = 0;
    let mut v___x_443_: usize = 0;
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: usize = 0;
    let mut v___x_446_: usize = 0;
    let mut v___x_447_: u8 = 0;
    let mut v_data_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: usize = 0;
    let mut v___x_452_: usize = 0;
    let mut v___x_453_: u8 = 0;
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_459_: u8 = 0;
    let mut v_t_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_464_: u8 = 0;
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: usize = 0;
    let mut v___x_467_: usize = 0;
    let mut v___x_468_: u8 = 0;
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: usize = 0;
    let mut v___x_471_: usize = 0;
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: usize = 0;
    let mut v___x_475_: u8 = 0;
    let mut v_fn_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: usize = 0;
    let mut v___x_484_: usize = 0;
    let mut v___x_485_: u8 = 0;
    let mut v___x_486_: usize = 0;
    let mut v___x_487_: usize = 0;
    let mut v___x_488_: u8 = 0;
    let mut v_typeName_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: usize = 0;
    let mut v___x_494_: usize = 0;
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_412_);
                crate::leanh::lean_inc(v_lvls_411_);
                crate::leanh::lean_inc(v_paramNames_410_);
                v___x_413_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(v_paramNames_410_, v_lvls_411_, v_e_412_);
                if crate::leanh::lean_obj_tag(v___x_413_) == 0 {
                    match crate::leanh::lean_obj_tag(v_e_412_) {
                        7 => {
                            v_binderName_414_ = crate::leanh::lean_ctor_get(v_e_412_, 0);
                            v_binderType_415_ = crate::leanh::lean_ctor_get(v_e_412_, 1);
                            v_body_416_ = crate::leanh::lean_ctor_get(v_e_412_, 2);
                            v_binderInfo_417_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_412_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_415_);
                            crate::leanh::lean_inc(v_lvls_411_);
                            crate::leanh::lean_inc(v_paramNames_410_);
                            v_d_418_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_binderType_415_);
                            crate::leanh::lean_inc_ref(v_body_416_);
                            v_b_419_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_body_416_);
                            v___x_425_ = lean_ptr_addr(v_binderType_415_);
                            v___x_426_ = lean_ptr_addr(v_d_418_);
                            v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
                            if v___x_427_ == 0 {
                                v___y_421_ = v___x_427_;
                                state = 1;
                                continue;
                            } else {
                                v___x_428_ = lean_ptr_addr(v_body_416_);
                                v___x_429_ = lean_ptr_addr(v_b_419_);
                                v___x_430_ = lean_usize_dec_eq(v___x_428_, v___x_429_);
                                v___y_421_ = v___x_430_;
                                state = 1;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_431_ = crate::leanh::lean_ctor_get(v_e_412_, 0);
                            v_binderType_432_ = crate::leanh::lean_ctor_get(v_e_412_, 1);
                            v_body_433_ = crate::leanh::lean_ctor_get(v_e_412_, 2);
                            v_binderInfo_434_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_412_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_432_);
                            crate::leanh::lean_inc(v_lvls_411_);
                            crate::leanh::lean_inc(v_paramNames_410_);
                            v_d_435_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_binderType_432_);
                            crate::leanh::lean_inc_ref(v_body_433_);
                            v_b_436_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_body_433_);
                            v___x_442_ = lean_ptr_addr(v_binderType_432_);
                            v___x_443_ = lean_ptr_addr(v_d_435_);
                            v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
                            if v___x_444_ == 0 {
                                v___y_438_ = v___x_444_;
                                state = 2;
                                continue;
                            } else {
                                v___x_445_ = lean_ptr_addr(v_body_433_);
                                v___x_446_ = lean_ptr_addr(v_b_436_);
                                v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
                                v___y_438_ = v___x_447_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            v_data_448_ = crate::leanh::lean_ctor_get(v_e_412_, 0);
                            v_expr_449_ = crate::leanh::lean_ctor_get(v_e_412_, 1);
                            crate::leanh::lean_inc_ref(v_expr_449_);
                            v_b_450_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_expr_449_);
                            v___x_451_ = lean_ptr_addr(v_expr_449_);
                            v___x_452_ = lean_ptr_addr(v_b_450_);
                            v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
                            if v___x_453_ == 0 {
                                crate::leanh::lean_inc(v_data_448_);
                                crate::leanh::lean_dec_ref_known(v_e_412_, 2);
                                v___x_454_ = l_Lean_Expr_mdata___override(v_data_448_, v_b_450_);
                                return v___x_454_;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_450_);
                                return v_e_412_;
                            }
                        }
                        8 => {
                            v_declName_455_ = crate::leanh::lean_ctor_get(v_e_412_, 0);
                            v_type_456_ = crate::leanh::lean_ctor_get(v_e_412_, 1);
                            v_value_457_ = crate::leanh::lean_ctor_get(v_e_412_, 2);
                            v_body_458_ = crate::leanh::lean_ctor_get(v_e_412_, 3);
                            v_nondep_459_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_412_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_type_456_);
                            crate::leanh::lean_inc_n(v_lvls_411_, 2);
                            crate::leanh::lean_inc_n(v_paramNames_410_, 2);
                            v_t_460_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_type_456_);
                            crate::leanh::lean_inc_ref(v_value_457_);
                            v_v_461_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_value_457_);
                            crate::leanh::lean_inc_ref(v_body_458_);
                            v_b_462_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_body_458_);
                            v___x_470_ = lean_ptr_addr(v_type_456_);
                            v___x_471_ = lean_ptr_addr(v_t_460_);
                            v___x_472_ = lean_usize_dec_eq(v___x_470_, v___x_471_);
                            if v___x_472_ == 0 {
                                v___y_464_ = v___x_472_;
                                state = 3;
                                continue;
                            } else {
                                v___x_473_ = lean_ptr_addr(v_value_457_);
                                v___x_474_ = lean_ptr_addr(v_v_461_);
                                v___x_475_ = lean_usize_dec_eq(v___x_473_, v___x_474_);
                                v___y_464_ = v___x_475_;
                                state = 3;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_476_ = crate::leanh::lean_ctor_get(v_e_412_, 0);
                            v_arg_477_ = crate::leanh::lean_ctor_get(v_e_412_, 1);
                            crate::leanh::lean_inc_ref(v_fn_476_);
                            crate::leanh::lean_inc(v_lvls_411_);
                            crate::leanh::lean_inc(v_paramNames_410_);
                            v_f_478_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_fn_476_);
                            crate::leanh::lean_inc_ref(v_arg_477_);
                            v_a_479_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_arg_477_);
                            v___x_483_ = lean_ptr_addr(v_fn_476_);
                            v___x_484_ = lean_ptr_addr(v_f_478_);
                            v___x_485_ = lean_usize_dec_eq(v___x_483_, v___x_484_);
                            if v___x_485_ == 0 {
                                v___y_481_ = v___x_485_;
                                state = 4;
                                continue;
                            } else {
                                v___x_486_ = lean_ptr_addr(v_arg_477_);
                                v___x_487_ = lean_ptr_addr(v_a_479_);
                                v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
                                v___y_481_ = v___x_488_;
                                state = 4;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_489_ = crate::leanh::lean_ctor_get(v_e_412_, 0);
                            v_idx_490_ = crate::leanh::lean_ctor_get(v_e_412_, 1);
                            v_struct_491_ = crate::leanh::lean_ctor_get(v_e_412_, 2);
                            crate::leanh::lean_inc_ref(v_struct_491_);
                            v_b_492_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_410_, v_lvls_411_, v_struct_491_);
                            v___x_493_ = lean_ptr_addr(v_struct_491_);
                            v___x_494_ = lean_ptr_addr(v_b_492_);
                            v___x_495_ = lean_usize_dec_eq(v___x_493_, v___x_494_);
                            if v___x_495_ == 0 {
                                crate::leanh::lean_inc(v_idx_490_);
                                crate::leanh::lean_inc(v_typeName_489_);
                                crate::leanh::lean_dec_ref_known(v_e_412_, 3);
                                v___x_496_ = l_Lean_Expr_proj___override(
                                    v_typeName_489_,
                                    v_idx_490_,
                                    v_b_492_,
                                );
                                return v___x_496_;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_492_);
                                return v_e_412_;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_lvls_411_);
                            crate::leanh::lean_dec(v_paramNames_410_);
                            return v_e_412_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_412_);
                    crate::leanh::lean_dec(v_lvls_411_);
                    crate::leanh::lean_dec(v_paramNames_410_);
                    v_val_497_ = crate::leanh::lean_ctor_get(v___x_413_, 0);
                    crate::leanh::lean_inc(v_val_497_);
                    crate::leanh::lean_dec_ref_known(v___x_413_, 1);
                    return v_val_497_;
                }
            }
            1 => {
                if v___y_421_ == 0 {
                    crate::leanh::lean_inc(v_binderName_414_);
                    crate::leanh::lean_dec_ref_known(v_e_412_, 3);
                    v___x_422_ = l_Lean_Expr_forallE___override(
                        v_binderName_414_,
                        v_d_418_,
                        v_b_419_,
                        v_binderInfo_417_,
                    );
                    return v___x_422_;
                } else {
                    v___x_423_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_417_, v_binderInfo_417_);
                    if v___x_423_ == 0 {
                        crate::leanh::lean_inc(v_binderName_414_);
                        crate::leanh::lean_dec_ref_known(v_e_412_, 3);
                        v___x_424_ = l_Lean_Expr_forallE___override(
                            v_binderName_414_,
                            v_d_418_,
                            v_b_419_,
                            v_binderInfo_417_,
                        );
                        return v___x_424_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_419_);
                        crate::leanh::lean_dec_ref(v_d_418_);
                        return v_e_412_;
                    }
                }
            }
            2 => {
                if v___y_438_ == 0 {
                    crate::leanh::lean_inc(v_binderName_431_);
                    crate::leanh::lean_dec_ref_known(v_e_412_, 3);
                    v___x_439_ = l_Lean_Expr_lam___override(
                        v_binderName_431_,
                        v_d_435_,
                        v_b_436_,
                        v_binderInfo_434_,
                    );
                    return v___x_439_;
                } else {
                    v___x_440_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_434_, v_binderInfo_434_);
                    if v___x_440_ == 0 {
                        crate::leanh::lean_inc(v_binderName_431_);
                        crate::leanh::lean_dec_ref_known(v_e_412_, 3);
                        v___x_441_ = l_Lean_Expr_lam___override(
                            v_binderName_431_,
                            v_d_435_,
                            v_b_436_,
                            v_binderInfo_434_,
                        );
                        return v___x_441_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_436_);
                        crate::leanh::lean_dec_ref(v_d_435_);
                        return v_e_412_;
                    }
                }
            }
            3 => {
                if v___y_464_ == 0 {
                    crate::leanh::lean_inc(v_declName_455_);
                    crate::leanh::lean_dec_ref_known(v_e_412_, 4);
                    v___x_465_ = l_Lean_Expr_letE___override(
                        v_declName_455_,
                        v_t_460_,
                        v_v_461_,
                        v_b_462_,
                        v_nondep_459_,
                    );
                    return v___x_465_;
                } else {
                    v___x_466_ = lean_ptr_addr(v_body_458_);
                    v___x_467_ = lean_ptr_addr(v_b_462_);
                    v___x_468_ = lean_usize_dec_eq(v___x_466_, v___x_467_);
                    if v___x_468_ == 0 {
                        crate::leanh::lean_inc(v_declName_455_);
                        crate::leanh::lean_dec_ref_known(v_e_412_, 4);
                        v___x_469_ = l_Lean_Expr_letE___override(
                            v_declName_455_,
                            v_t_460_,
                            v_v_461_,
                            v_b_462_,
                            v_nondep_459_,
                        );
                        return v___x_469_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_462_);
                        crate::leanh::lean_dec_ref(v_v_461_);
                        crate::leanh::lean_dec_ref(v_t_460_);
                        return v_e_412_;
                    }
                }
            }
            4 => {
                if v___y_481_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_412_, 2);
                    v___x_482_ = l_Lean_Expr_app___override(v_f_478_, v_a_479_);
                    return v___x_482_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_479_);
                    crate::leanh::lean_dec_ref(v_f_478_);
                    return v_e_412_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsNoCache(
    mut v_e_498_: *mut crate::leanh::LeanObject,
    mut v_paramNames_499_: *mut crate::leanh::LeanObject,
    mut v_lvls_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_502_: u8 = 0;
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: u8 = 0;
    let mut v___x_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_504_ = l_List_isEmpty___redArg(v_paramNames_499_);
                if v___x_504_ == 0 {
                    v___x_505_ = l_List_isEmpty___redArg(v_lvls_500_);
                    v___y_502_ = v___x_505_;
                    state = 1;
                    continue;
                } else {
                    v___y_502_ = v___x_504_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_502_ == 0 {
                    v___x_503_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_499_, v_lvls_500_, v_e_498_);
                    return v___x_503_;
                } else {
                    crate::leanh::lean_dec(v_lvls_500_);
                    crate::leanh::lean_dec(v_paramNames_499_);
                    return v_e_498_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(
    mut v_ps_506_: *mut crate::leanh::LeanObject,
    mut v_us_507_: *mut crate::leanh::LeanObject,
    mut v_p_x27_508_: *mut crate::leanh::LeanObject,
    mut v_i_509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: u8 = 0;
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: u8 = 0;
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_510_ = lean_array_get_size(v_ps_506_);
                v___x_511_ = lean_nat_dec_lt(v_i_509_, v___x_510_);
                if v___x_511_ == 0 {
                    crate::leanh::lean_dec(v_i_509_);
                    v___x_512_ = crate::leanh::lean_box(0);
                    return v___x_512_;
                } else {
                    v___x_513_ = lean_array_get_size(v_us_507_);
                    v___x_514_ = lean_nat_dec_lt(v_i_509_, v___x_513_);
                    if v___x_514_ == 0 {
                        crate::leanh::lean_dec(v_i_509_);
                        v___x_515_ = crate::leanh::lean_box(0);
                        return v___x_515_;
                    } else {
                        v_p_516_ = lean_array_fget_borrowed(v_ps_506_, v_i_509_);
                        v___x_517_ = lean_name_eq(v_p_516_, v_p_x27_508_);
                        if v___x_517_ == 0 {
                            v___x_518_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_519_ = lean_nat_add(v_i_509_, v___x_518_);
                            crate::leanh::lean_dec(v_i_509_);
                            v_i_509_ = v___x_519_;
                            state = 0;
                            continue;
                        } else {
                            v_u_521_ = lean_array_fget_borrowed(v_us_507_, v_i_509_);
                            crate::leanh::lean_dec(v_i_509_);
                            crate::leanh::lean_inc(v_u_521_);
                            v___x_522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_522_, 0, v_u_521_);
                            return v___x_522_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(
    mut v_ps_523_: *mut crate::leanh::LeanObject,
    mut v_us_524_: *mut crate::leanh::LeanObject,
    mut v_p_x27_525_: *mut crate::leanh::LeanObject,
    mut v_i_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(
        v_ps_523_,
        v_us_524_,
        v_p_x27_525_,
        v_i_526_,
    );
    crate::leanh::lean_dec(v_p_x27_525_);
    crate::leanh::lean_dec_ref(v_us_524_);
    crate::leanh::lean_dec_ref(v_ps_523_);
    return v_res_527_;
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(
    mut v_paramNames_528_: *mut crate::leanh::LeanObject,
    mut v_lvls_529_: *mut crate::leanh::LeanObject,
    mut v_p_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_532_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(
        v_paramNames_528_,
        v_lvls_529_,
        v_p_530_,
        v___x_531_,
    );
    return v___x_532_;
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(
    mut v_paramNames_533_: *mut crate::leanh::LeanObject,
    mut v_lvls_534_: *mut crate::leanh::LeanObject,
    mut v_p_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_536_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(v_paramNames_533_, v_lvls_534_, v_p_535_);
    crate::leanh::lean_dec(v_p_535_);
    crate::leanh::lean_dec_ref(v_lvls_534_);
    crate::leanh::lean_dec_ref(v_paramNames_533_);
    return v_res_536_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(
    mut v_paramNames_537_: *mut crate::leanh::LeanObject,
    mut v_lvls_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
    mut v_a_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_546_: u8 = 0;
    let mut v___f_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_539_) == 0 {
                    crate::leanh::lean_dec_ref(v_lvls_538_);
                    crate::leanh::lean_dec_ref(v_paramNames_537_);
                    v___x_541_ = l_List_reverse___redArg(v_a_540_);
                    return v___x_541_;
                } else {
                    v_head_542_ = crate::leanh::lean_ctor_get(v_a_539_, 0);
                    v_tail_543_ = crate::leanh::lean_ctor_get(v_a_539_, 1);
                    v_isSharedCheck_553_ = (!crate::leanh::lean_is_exclusive(v_a_539_)) as u8;
                    if v_isSharedCheck_553_ == 0 {
                        v___x_545_ = v_a_539_;
                        v_isShared_546_ = v_isSharedCheck_553_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_543_);
                        crate::leanh::lean_inc(v_head_542_);
                        crate::leanh::lean_dec(v_a_539_);
                        v___x_545_ = crate::leanh::lean_box(0);
                        v_isShared_546_ = v_isSharedCheck_553_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lvls_538_);
                crate::leanh::lean_inc_ref(v_paramNames_537_);
                v___f_547_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                crate::leanh::lean_closure_set(v___f_547_, 0, v_paramNames_537_);
                crate::leanh::lean_closure_set(v___f_547_, 1, v_lvls_538_);
                v___x_548_ =
                    l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_547_, v_head_542_);
                if v_isShared_546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_545_, 1, v_a_540_);
                    crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_548_);
                    v___x_550_ = v___x_545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 1, v_a_540_);
                    v___x_550_ = v_reuseFailAlloc_552_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_539_ = v_tail_543_;
                v_a_540_ = v___x_550_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(
    mut v_paramNames_554_: *mut crate::leanh::LeanObject,
    mut v_lvls_555_: *mut crate::leanh::LeanObject,
    mut v_e_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_557_: u8 = 0;
    v___x_557_ = l_Lean_Expr_hasLevelParam(v_e_556_);
    if v___x_557_ == 0 {
        let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_lvls_555_);
        crate::leanh::lean_dec_ref(v_paramNames_554_);
        v___x_558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_558_, 0, v_e_556_);
        return v___x_558_;
    } else {
        match crate::leanh::lean_obj_tag(v_e_556_) {
            4 => {
                let mut v_declName_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_us_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_563_: u8 = 0;
                v_declName_559_ = crate::leanh::lean_ctor_get(v_e_556_, 0);
                v_us_560_ = crate::leanh::lean_ctor_get(v_e_556_, 1);
                v___x_561_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_us_560_);
                v___x_562_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(v_paramNames_554_, v_lvls_555_, v_us_560_, v___x_561_);
                v___x_563_ = l_ptrEqList___redArg(v_us_560_, v___x_562_);
                if v___x_563_ == 0 {
                    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc(v_declName_559_);
                    crate::leanh::lean_dec_ref_known(v_e_556_, 2);
                    v___x_564_ = l_Lean_Expr_const___override(v_declName_559_, v___x_562_);
                    v___x_565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_565_, 0, v___x_564_);
                    return v___x_565_;
                } else {
                    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_562_);
                    v___x_566_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_566_, 0, v_e_556_);
                    return v___x_566_;
                }
            }
            3 => {
                let mut v_u_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_570_: usize = 0;
                let mut v___x_571_: usize = 0;
                let mut v___x_572_: u8 = 0;
                v_u_567_ = crate::leanh::lean_ctor_get(v_e_556_, 0);
                v___f_568_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                crate::leanh::lean_closure_set(v___f_568_, 0, v_paramNames_554_);
                crate::leanh::lean_closure_set(v___f_568_, 1, v_lvls_555_);
                crate::leanh::lean_inc(v_u_567_);
                v___x_569_ =
                    l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_568_, v_u_567_);
                v___x_570_ = lean_ptr_addr(v_u_567_);
                v___x_571_ = lean_ptr_addr(v___x_569_);
                v___x_572_ = lean_usize_dec_eq(v___x_570_, v___x_571_);
                if v___x_572_ == 0 {
                    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_e_556_, 1);
                    v___x_573_ = l_Lean_Expr_sort___override(v___x_569_);
                    v___x_574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_574_, 0, v___x_573_);
                    return v___x_574_;
                } else {
                    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_569_);
                    v___x_575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_575_, 0, v_e_556_);
                    return v___x_575_;
                }
            }
            _ => {
                let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_e_556_);
                crate::leanh::lean_dec_ref(v_lvls_555_);
                crate::leanh::lean_dec_ref(v_paramNames_554_);
                v___x_576_ = crate::leanh::lean_box(0);
                return v___x_576_;
            }
        }
    }
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(
    mut v_paramNames_577_: *mut crate::leanh::LeanObject,
    mut v_lvls_578_: *mut crate::leanh::LeanObject,
    mut v_e_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_580_, 0, v_paramNames_577_);
    crate::leanh::lean_closure_set(v___x_580_, 1, v_lvls_578_);
    v___x_581_ = lean_replace_expr(v___x_580_, v_e_579_);
    crate::leanh::lean_dec_ref(v___x_580_);
    return v___x_581_;
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(
    mut v_paramNames_582_: *mut crate::leanh::LeanObject,
    mut v_lvls_583_: *mut crate::leanh::LeanObject,
    mut v_e_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_585_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_582_, v_lvls_583_, v_e_584_);
    crate::leanh::lean_dec_ref(v_e_584_);
    return v_res_585_;
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsArray(
    mut v_e_586_: *mut crate::leanh::LeanObject,
    mut v_paramNames_587_: *mut crate::leanh::LeanObject,
    mut v_lvls_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_590_: u8 = 0;
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: u8 = 0;
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_592_ = lean_array_get_size(v_paramNames_587_);
                v___x_593_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_594_ = lean_nat_dec_eq(v___x_592_, v___x_593_);
                if v___x_594_ == 0 {
                    v___x_595_ = lean_array_get_size(v_lvls_588_);
                    v___x_596_ = lean_nat_dec_eq(v___x_595_, v___x_593_);
                    v___y_590_ = v___x_596_;
                    state = 1;
                    continue;
                } else {
                    v___y_590_ = v___x_594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_590_ == 0 {
                    v___x_591_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_587_, v_lvls_588_, v_e_586_);
                    return v___x_591_;
                } else {
                    crate::leanh::lean_dec_ref(v_lvls_588_);
                    crate::leanh::lean_dec_ref(v_paramNames_587_);
                    crate::leanh::lean_inc_ref(v_e_586_);
                    return v_e_586_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_instantiateLevelParamsArray___boxed(
    mut v_e_597_: *mut crate::leanh::LeanObject,
    mut v_paramNames_598_: *mut crate::leanh::LeanObject,
    mut v_lvls_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Lean_Expr_instantiateLevelParamsArray(v_e_597_, v_paramNames_598_, v_lvls_599_);
    crate::leanh::lean_dec_ref(v_e_597_);
    return v_res_600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_InstantiateLevelParams(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_InstantiateLevelParams(
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
pub unsafe fn initialize_Lean_Util_InstantiateLevelParams(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ReplaceExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_InstantiateLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_InstantiateLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_InstantiateLevelParams(builtin);
}
