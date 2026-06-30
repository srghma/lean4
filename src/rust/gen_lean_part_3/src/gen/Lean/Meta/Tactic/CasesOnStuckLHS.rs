// Lean compiler output
// Module: Lean.Meta.Tactic.CasesOnStuckLHS
// Imports: Lean.Meta.Basic Lean.ProjFns Lean.Meta.Tactic.Cases
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_st_ref_get, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Declaration::l_Lean_RecursorVal_getMajorIdx;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_constName_x21,
    l_Lean_Expr_consumeMData, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConst, l_Lean_Expr_isFVar,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::MatchUtil::l_Lean_Meta_matchEqHEqLHS_x3f;
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_MVarId_cases,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::ProjFns::{
    initialize_Lean_ProjFns, l_Lean_Environment_getProjectionFnInfo_x3f,
    runtime_initialize_Lean_ProjFns,
};
static mut l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_casesOnStuckLHS___closed__0_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            39, 99, 97, 115, 101, 115, 79, 110, 83, 116, 117, 99, 107, 76, 72, 83, 39, 32, 102, 97,
            105, 108, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_casesOnStuckLHS___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_casesOnStuckLHS___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_casesOnStuckLHS___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_casesOnStuckLHS___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_casesOnStuckLHS___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_casesOnStuckLHS___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_casesOnStuckLHS___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(
    mut v_declName_316_: *mut leanh::LeanObject,
    mut v___y_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_st_ref_get(v___y_317_);
    v_env_320_ = leanh::lean_ctor_get(v___x_319_, 0);
    leanh::lean_inc_ref(v_env_320_);
    leanh::lean_dec(v___x_319_);
    v___x_321_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_320_, v_declName_316_);
    v___x_322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_322_, 0, v___x_321_);
    return v___x_322_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg___boxed(
    mut v_declName_323_: *mut leanh::LeanObject,
    mut v___y_324_: *mut leanh::LeanObject,
    mut v___y_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_323_, v___y_324_);
    leanh::lean_dec(v___y_324_);
    return v_res_326_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(
    mut v_declName_327_: *mut leanh::LeanObject,
    mut v___y_328_: *mut leanh::LeanObject,
    mut v___y_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
    mut v___y_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_327_, v___y_331_);
    return v___x_333_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___boxed(
    mut v_declName_334_: *mut leanh::LeanObject,
    mut v___y_335_: *mut leanh::LeanObject,
    mut v___y_336_: *mut leanh::LeanObject,
    mut v___y_337_: *mut leanh::LeanObject,
    mut v___y_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_340_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0(v_declName_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
    leanh::lean_dec(v___y_338_);
    leanh::lean_dec_ref(v___y_337_);
    leanh::lean_dec(v___y_336_);
    leanh::lean_dec_ref(v___y_335_);
    return v_res_340_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = leanh::lean_box(0);
    v_dummy_342_ = l_Lean_Expr_sort___override(v___x_341_);
    return v_dummy_342_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(
    mut v_e_343_: *mut leanh::LeanObject,
    mut v_a_344_: *mut leanh::LeanObject,
    mut v_a_345_: *mut leanh::LeanObject,
    mut v_a_346_: *mut leanh::LeanObject,
    mut v_a_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: u8 = 0;
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_363_: u8 = 0;
    let mut v_nargs_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: u8 = 0;
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_378_: u8 = 0;
    let mut v_val_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: u8 = 0;
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: u8 = 0;
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_402_: u8 = 0;
    let mut v_val_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_414_: u8 = 0;
    let mut v_a_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_418_: u8 = 0;
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_352_ = l_Lean_Expr_getAppFn(v_e_343_);
                if leanh::lean_obj_tag(v___x_352_) == 11 {
                    leanh::lean_dec_ref(v_e_343_);
                    v_struct_353_ = leanh::lean_ctor_get(v___x_352_, 2);
                    leanh::lean_inc_ref(v_struct_353_);
                    leanh::lean_dec_ref_known(v___x_352_, 3);
                    v_e_343_ = v_struct_353_;
                    state = 0;
                    continue;
                } else {
                    v___x_355_ = l_Lean_Expr_isConst(v___x_352_);
                    if v___x_355_ == 0 {
                        leanh::lean_dec_ref(v___x_352_);
                        leanh::lean_dec_ref(v_e_343_);
                        v___x_356_ = leanh::lean_box(0);
                        v___x_357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_357_, 0, v___x_356_);
                        return v___x_357_;
                    } else {
                        v_declName_358_ = l_Lean_Expr_constName_x21(v___x_352_);
                        v___x_359_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f_spec__0___redArg(v_declName_358_, v_a_347_);
                        if leanh::lean_obj_tag(v___x_359_) == 0 {
                            v_a_360_ = leanh::lean_ctor_get(v___x_359_, 0);
                            v_isSharedCheck_414_ =
                                (!leanh::lean_is_exclusive(v___x_359_)) as u8;
                            if v_isSharedCheck_414_ == 0 {
                                v___x_362_ = v___x_359_;
                                v_isShared_363_ = v_isSharedCheck_414_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_360_);
                                leanh::lean_dec(v___x_359_);
                                v___x_362_ = leanh::lean_box(0);
                                v_isShared_363_ = v_isSharedCheck_414_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_352_);
                            leanh::lean_dec_ref(v_e_343_);
                            v_a_415_ = leanh::lean_ctor_get(v___x_359_, 0);
                            v_isSharedCheck_422_ =
                                (!leanh::lean_is_exclusive(v___x_359_)) as u8;
                            if v_isSharedCheck_422_ == 0 {
                                v___x_417_ = v___x_359_;
                                v_isShared_418_ = v_isSharedCheck_422_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_415_);
                                leanh::lean_dec(v___x_359_);
                                v___x_417_ = leanh::lean_box(0);
                                v_isShared_418_ = v_isSharedCheck_422_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_350_ = leanh::lean_box(0);
                v___x_351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_351_, 0, v___x_350_);
                return v___x_351_;
            }
            2 => {
                v_nargs_364_ = l_Lean_Expr_getAppNumArgs(v_e_343_);
                v_dummy_365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0_once), _init_l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___closed__0);
                leanh::lean_inc(v_nargs_364_);
                v___x_366_ = lean_mk_array(v_nargs_364_, v_dummy_365_);
                v___x_367_ = leanh::lean_unsigned_to_nat(1);
                v___x_368_ = lean_nat_sub(v_nargs_364_, v___x_367_);
                leanh::lean_dec(v_nargs_364_);
                v_args_369_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_343_, v___x_366_, v___x_368_,
                );
                if leanh::lean_obj_tag(v_a_360_) == 0 {
                    if leanh::lean_obj_tag(v___x_352_) == 4 {
                        v_declName_370_ = leanh::lean_ctor_get(v___x_352_, 0);
                        leanh::lean_inc(v_declName_370_);
                        leanh::lean_dec_ref_known(v___x_352_, 2);
                        v___x_371_ = lean_st_ref_get(v_a_347_);
                        v_env_372_ = leanh::lean_ctor_get(v___x_371_, 0);
                        leanh::lean_inc_ref(v_env_372_);
                        leanh::lean_dec(v___x_371_);
                        v___x_373_ = 0;
                        v___x_374_ =
                            l_Lean_Environment_find_x3f(v_env_372_, v_declName_370_, v___x_373_);
                        if leanh::lean_obj_tag(v___x_374_) == 0 {
                            leanh::lean_dec_ref(v_args_369_);
                            leanh::lean_del_object(v___x_362_);
                            state = 1;
                            continue;
                        } else {
                            v_val_375_ = leanh::lean_ctor_get(v___x_374_, 0);
                            v_isSharedCheck_402_ =
                                (!leanh::lean_is_exclusive(v___x_374_)) as u8;
                            if v_isSharedCheck_402_ == 0 {
                                v___x_377_ = v___x_374_;
                                v_isShared_378_ = v_isSharedCheck_402_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_375_);
                                leanh::lean_dec(v___x_374_);
                                v___x_377_ = leanh::lean_box(0);
                                v_isShared_378_ = v_isSharedCheck_402_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_369_);
                        leanh::lean_del_object(v___x_362_);
                        leanh::lean_dec_ref(v___x_352_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_352_);
                    v_val_403_ = leanh::lean_ctor_get(v_a_360_, 0);
                    leanh::lean_inc(v_val_403_);
                    leanh::lean_dec_ref_known(v_a_360_, 1);
                    v_numParams_404_ = leanh::lean_ctor_get(v_val_403_, 1);
                    leanh::lean_inc(v_numParams_404_);
                    leanh::lean_dec(v_val_403_);
                    v___x_405_ = lean_array_get_size(v_args_369_);
                    v___x_406_ = lean_nat_dec_lt(v_numParams_404_, v___x_405_);
                    if v___x_406_ == 0 {
                        leanh::lean_dec(v_numParams_404_);
                        leanh::lean_dec_ref(v_args_369_);
                        v___x_407_ = leanh::lean_box(0);
                        if v_isShared_363_ == 0 {
                            leanh::lean_ctor_set(v___x_362_, 0, v___x_407_);
                            v___x_409_ = v___x_362_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
                            v___x_409_ = v_reuseFailAlloc_410_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_362_);
                        v___x_411_ = l_Lean_instInhabitedExpr;
                        v___x_412_ = lean_array_get(v___x_411_, v_args_369_, v_numParams_404_);
                        leanh::lean_dec(v_numParams_404_);
                        leanh::lean_dec_ref(v_args_369_);
                        v_e_343_ = v___x_412_;
                        state = 0;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_val_375_) == 7 {
                    v_val_379_ = leanh::lean_ctor_get(v_val_375_, 0);
                    leanh::lean_inc_ref(v_val_379_);
                    leanh::lean_dec_ref_known(v_val_375_, 1);
                    v___x_380_ = lean_array_get_size(v_args_369_);
                    v___x_381_ = l_Lean_RecursorVal_getMajorIdx(v_val_379_);
                    leanh::lean_dec_ref(v_val_379_);
                    v___x_382_ = lean_nat_dec_le(v___x_380_, v___x_381_);
                    if v___x_382_ == 0 {
                        v___x_383_ = l_Lean_instInhabitedExpr;
                        v___x_384_ = lean_array_get(v___x_383_, v_args_369_, v___x_381_);
                        leanh::lean_dec(v___x_381_);
                        leanh::lean_dec_ref(v_args_369_);
                        v___x_385_ = l_Lean_Expr_consumeMData(v___x_384_);
                        leanh::lean_dec(v___x_384_);
                        v___x_386_ = l_Lean_Expr_isFVar(v___x_385_);
                        if v___x_386_ == 0 {
                            leanh::lean_dec_ref(v___x_385_);
                            leanh::lean_del_object(v___x_377_);
                            v___x_387_ = leanh::lean_box(0);
                            if v_isShared_363_ == 0 {
                                leanh::lean_ctor_set(v___x_362_, 0, v___x_387_);
                                v___x_389_ = v___x_362_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_390_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
                                v___x_389_ = v_reuseFailAlloc_390_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_391_ = l_Lean_Expr_fvarId_x21(v___x_385_);
                            leanh::lean_dec_ref(v___x_385_);
                            if v_isShared_378_ == 0 {
                                leanh::lean_ctor_set(v___x_377_, 0, v___x_391_);
                                v___x_393_ = v___x_377_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_397_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_391_);
                                v___x_393_ = v_reuseFailAlloc_397_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_381_);
                        leanh::lean_del_object(v___x_377_);
                        leanh::lean_dec_ref(v_args_369_);
                        v___x_398_ = leanh::lean_box(0);
                        if v_isShared_363_ == 0 {
                            leanh::lean_ctor_set(v___x_362_, 0, v___x_398_);
                            v___x_400_ = v___x_362_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
                            v___x_400_ = v_reuseFailAlloc_401_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_377_);
                    leanh::lean_dec(v_val_375_);
                    leanh::lean_dec_ref(v_args_369_);
                    leanh::lean_del_object(v___x_362_);
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_389_;
            }
            5 => {
                if v_isShared_363_ == 0 {
                    leanh::lean_ctor_set(v___x_362_, 0, v___x_393_);
                    v___x_395_ = v___x_362_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
                    v___x_395_ = v_reuseFailAlloc_396_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_395_;
            }
            7 => {
                return v___x_400_;
            }
            8 => {
                return v___x_409_;
            }
            9 => {
                if v_isShared_418_ == 0 {
                    v___x_420_ = v___x_417_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
                    v___x_420_ = v_reuseFailAlloc_421_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f___boxed(
    mut v_e_423_: *mut leanh::LeanObject,
    mut v_a_424_: *mut leanh::LeanObject,
    mut v_a_425_: *mut leanh::LeanObject,
    mut v_a_426_: *mut leanh::LeanObject,
    mut v_a_427_: *mut leanh::LeanObject,
    mut v_a_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ =
        l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(
            v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_,
        );
    leanh::lean_dec(v_a_427_);
    leanh::lean_dec_ref(v_a_426_);
    leanh::lean_dec(v_a_425_);
    leanh::lean_dec_ref(v_a_424_);
    return v_res_429_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(
    mut v_sz_430_: usize,
    mut v_i_431_: usize,
    mut v_bs_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_433_: u8 = 0;
    let mut v_v_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: usize = 0;
    let mut v___x_440_: usize = 0;
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_433_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
                if v___x_433_ == 0 {
                    return v_bs_432_;
                } else {
                    v_v_434_ = lean_array_uget_borrowed(v_bs_432_, v_i_431_);
                    v_toInductionSubgoal_435_ = leanh::lean_ctor_get(v_v_434_, 0);
                    v_mvarId_436_ = leanh::lean_ctor_get(v_toInductionSubgoal_435_, 0);
                    leanh::lean_inc(v_mvarId_436_);
                    v___x_437_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_438_ = lean_array_uset(v_bs_432_, v_i_431_, v___x_437_);
                    v___x_439_ = 1usize;
                    v___x_440_ = lean_usize_add(v_i_431_, v___x_439_);
                    v___x_441_ = lean_array_uset(v_bs_x27_438_, v_i_431_, v_mvarId_436_);
                    v_i_431_ = v___x_440_;
                    v_bs_432_ = v___x_441_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1___boxed(
    mut v_sz_443_: *mut leanh::LeanObject,
    mut v_i_444_: *mut leanh::LeanObject,
    mut v_bs_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_446_: usize = 0;
    let mut v_i_boxed_447_: usize = 0;
    let mut v_res_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_446_ = leanh::lean_unbox_usize(v_sz_443_);
    leanh::lean_dec(v_sz_443_);
    v_i_boxed_447_ = leanh::lean_unbox_usize(v_i_444_);
    leanh::lean_dec(v_i_444_);
    v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(v_sz_boxed_446_, v_i_boxed_447_, v_bs_445_);
    return v_res_448_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(
    mut v_msgData_449_: *mut leanh::LeanObject,
    mut v___y_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
    mut v___y_452_: *mut leanh::LeanObject,
    mut v___y_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = lean_st_ref_get(v___y_453_);
    v_env_456_ = leanh::lean_ctor_get(v___x_455_, 0);
    leanh::lean_inc_ref(v_env_456_);
    leanh::lean_dec(v___x_455_);
    v___x_457_ = lean_st_ref_get(v___y_451_);
    v_mctx_458_ = leanh::lean_ctor_get(v___x_457_, 0);
    leanh::lean_inc_ref(v_mctx_458_);
    leanh::lean_dec(v___x_457_);
    v_lctx_459_ = leanh::lean_ctor_get(v___y_450_, 2);
    v_options_460_ = leanh::lean_ctor_get(v___y_452_, 2);
    leanh::lean_inc_ref(v_options_460_);
    leanh::lean_inc_ref(v_lctx_459_);
    v___x_461_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_461_, 0, v_env_456_);
    leanh::lean_ctor_set(v___x_461_, 1, v_mctx_458_);
    leanh::lean_ctor_set(v___x_461_, 2, v_lctx_459_);
    leanh::lean_ctor_set(v___x_461_, 3, v_options_460_);
    v___x_462_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_462_, 0, v___x_461_);
    leanh::lean_ctor_set(v___x_462_, 1, v_msgData_449_);
    v___x_463_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_463_, 0, v___x_462_);
    return v___x_463_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0___boxed(
    mut v_msgData_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
    mut v___y_467_: *mut leanh::LeanObject,
    mut v___y_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(v_msgData_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
    leanh::lean_dec(v___y_468_);
    leanh::lean_dec_ref(v___y_467_);
    leanh::lean_dec(v___y_466_);
    leanh::lean_dec_ref(v___y_465_);
    return v_res_470_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(
    mut v_msg_471_: *mut leanh::LeanObject,
    mut v___y_472_: *mut leanh::LeanObject,
    mut v___y_473_: *mut leanh::LeanObject,
    mut v___y_474_: *mut leanh::LeanObject,
    mut v___y_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_477_ = leanh::lean_ctor_get(v___y_474_, 5);
                v___x_478_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0_spec__0(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
                v_a_479_ = leanh::lean_ctor_get(v___x_478_, 0);
                v_isSharedCheck_487_ = (!leanh::lean_is_exclusive(v___x_478_)) as u8;
                if v_isSharedCheck_487_ == 0 {
                    v___x_481_ = v___x_478_;
                    v_isShared_482_ = v_isSharedCheck_487_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_479_);
                    leanh::lean_dec(v___x_478_);
                    v___x_481_ = leanh::lean_box(0);
                    v_isShared_482_ = v_isSharedCheck_487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_477_);
                v___x_483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_483_, 0, v_ref_477_);
                leanh::lean_ctor_set(v___x_483_, 1, v_a_479_);
                if v_isShared_482_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_481_, 1);
                    leanh::lean_ctor_set(v___x_481_, 0, v___x_483_);
                    v___x_485_ = v___x_481_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
                    v___x_485_ = v_reuseFailAlloc_486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg___boxed(
    mut v_msg_488_: *mut leanh::LeanObject,
    mut v___y_489_: *mut leanh::LeanObject,
    mut v___y_490_: *mut leanh::LeanObject,
    mut v___y_491_: *mut leanh::LeanObject,
    mut v___y_492_: *mut leanh::LeanObject,
    mut v___y_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(
        v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_,
    );
    leanh::lean_dec(v___y_492_);
    leanh::lean_dec_ref(v___y_491_);
    leanh::lean_dec(v___y_490_);
    leanh::lean_dec_ref(v___y_489_);
    return v_res_494_;
}
pub unsafe fn _init_l_Lean_Meta_casesOnStuckLHS___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = l_Lean_Meta_casesOnStuckLHS___closed__0;
    v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
    return v___x_497_;
}
pub unsafe fn l_Lean_Meta_casesOnStuckLHS(
    mut v_mvarId_500_: *mut leanh::LeanObject,
    mut v_a_501_: *mut leanh::LeanObject,
    mut v_a_502_: *mut leanh::LeanObject,
    mut v_a_503_: *mut leanh::LeanObject,
    mut v_a_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: u8 = 0;
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_529_: u8 = 0;
    let mut v_sz_530_: usize = 0;
    let mut v___x_531_: usize = 0;
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_536_: u8 = 0;
    let mut v_a_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_540_: u8 = 0;
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_544_: u8 = 0;
    let mut v_a_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_552_: u8 = 0;
    let mut v_a_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v_a_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_564_: u8 = 0;
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_500_);
                v___x_513_ =
                    l_Lean_MVarId_getType(v_mvarId_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
                if leanh::lean_obj_tag(v___x_513_) == 0 {
                    v_a_514_ = leanh::lean_ctor_get(v___x_513_, 0);
                    leanh::lean_inc(v_a_514_);
                    leanh::lean_dec_ref_known(v___x_513_, 1);
                    v___x_515_ = l_Lean_Meta_matchEqHEqLHS_x3f(
                        v_a_514_, v_a_501_, v_a_502_, v_a_503_, v_a_504_,
                    );
                    if leanh::lean_obj_tag(v___x_515_) == 0 {
                        v_a_516_ = leanh::lean_ctor_get(v___x_515_, 0);
                        leanh::lean_inc(v_a_516_);
                        leanh::lean_dec_ref_known(v___x_515_, 1);
                        if leanh::lean_obj_tag(v_a_516_) == 1 {
                            v_val_517_ = leanh::lean_ctor_get(v_a_516_, 0);
                            leanh::lean_inc(v_val_517_);
                            leanh::lean_dec_ref_known(v_a_516_, 1);
                            v_snd_518_ = leanh::lean_ctor_get(v_val_517_, 1);
                            leanh::lean_inc(v_snd_518_);
                            leanh::lean_dec(v_val_517_);
                            v___x_519_ = l___private_Lean_Meta_Tactic_CasesOnStuckLHS_0__Lean_Meta_casesOnStuckLHS_findFVar_x3f(v_snd_518_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
                            if leanh::lean_obj_tag(v___x_519_) == 0 {
                                v_a_520_ = leanh::lean_ctor_get(v___x_519_, 0);
                                leanh::lean_inc(v_a_520_);
                                leanh::lean_dec_ref_known(v___x_519_, 1);
                                if leanh::lean_obj_tag(v_a_520_) == 1 {
                                    v_val_521_ = leanh::lean_ctor_get(v_a_520_, 0);
                                    leanh::lean_inc(v_val_521_);
                                    leanh::lean_dec_ref_known(v_a_520_, 1);
                                    v___x_522_ = l_Lean_Meta_casesOnStuckLHS___closed__2;
                                    v___x_523_ = 0;
                                    v___x_524_ = leanh::lean_box(0);
                                    v___x_525_ = l_Lean_MVarId_cases(
                                        v_mvarId_500_,
                                        v_val_521_,
                                        v___x_522_,
                                        v___x_523_,
                                        v___x_524_,
                                        v_a_501_,
                                        v_a_502_,
                                        v_a_503_,
                                        v_a_504_,
                                    );
                                    if leanh::lean_obj_tag(v___x_525_) == 0 {
                                        v_a_526_ = leanh::lean_ctor_get(v___x_525_, 0);
                                        v_isSharedCheck_536_ =
                                            (!leanh::lean_is_exclusive(v___x_525_)) as u8;
                                        if v_isSharedCheck_536_ == 0 {
                                            v___x_528_ = v___x_525_;
                                            v_isShared_529_ = v_isSharedCheck_536_;
                                            state = 2;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_526_);
                                            leanh::lean_dec(v___x_525_);
                                            v___x_528_ = leanh::lean_box(0);
                                            v_isShared_529_ = v_isSharedCheck_536_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v_a_537_ = leanh::lean_ctor_get(v___x_525_, 0);
                                        v_isSharedCheck_544_ =
                                            (!leanh::lean_is_exclusive(v___x_525_)) as u8;
                                        if v_isSharedCheck_544_ == 0 {
                                            v___x_539_ = v___x_525_;
                                            v_isShared_540_ = v_isSharedCheck_544_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_537_);
                                            leanh::lean_dec(v___x_525_);
                                            v___x_539_ = leanh::lean_box(0);
                                            v_isShared_540_ = v_isSharedCheck_544_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_520_);
                                    leanh::lean_dec(v_mvarId_500_);
                                    v___y_507_ = v_a_501_;
                                    v___y_508_ = v_a_502_;
                                    v___y_509_ = v_a_503_;
                                    v___y_510_ = v_a_504_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_mvarId_500_);
                                v_a_545_ = leanh::lean_ctor_get(v___x_519_, 0);
                                v_isSharedCheck_552_ =
                                    (!leanh::lean_is_exclusive(v___x_519_)) as u8;
                                if v_isSharedCheck_552_ == 0 {
                                    v___x_547_ = v___x_519_;
                                    v_isShared_548_ = v_isSharedCheck_552_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_545_);
                                    leanh::lean_dec(v___x_519_);
                                    v___x_547_ = leanh::lean_box(0);
                                    v_isShared_548_ = v_isSharedCheck_552_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_516_);
                            leanh::lean_dec(v_mvarId_500_);
                            v___y_507_ = v_a_501_;
                            v___y_508_ = v_a_502_;
                            v___y_509_ = v_a_503_;
                            v___y_510_ = v_a_504_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_500_);
                        v_a_553_ = leanh::lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_560_ = (!leanh::lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_560_ == 0 {
                            v___x_555_ = v___x_515_;
                            v_isShared_556_ = v_isSharedCheck_560_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_553_);
                            leanh::lean_dec(v___x_515_);
                            v___x_555_ = leanh::lean_box(0);
                            v_isShared_556_ = v_isSharedCheck_560_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_500_);
                    v_a_561_ = leanh::lean_ctor_get(v___x_513_, 0);
                    v_isSharedCheck_568_ = (!leanh::lean_is_exclusive(v___x_513_)) as u8;
                    if v_isSharedCheck_568_ == 0 {
                        v___x_563_ = v___x_513_;
                        v_isShared_564_ = v_isSharedCheck_568_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_561_);
                        leanh::lean_dec(v___x_513_);
                        v___x_563_ = leanh::lean_box(0);
                        v_isShared_564_ = v_isSharedCheck_568_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_511_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_casesOnStuckLHS___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_casesOnStuckLHS___closed__1_once),
                    _init_l_Lean_Meta_casesOnStuckLHS___closed__1,
                );
                v___x_512_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(
                    v___x_511_, v___y_507_, v___y_508_, v___y_509_, v___y_510_,
                );
                return v___x_512_;
            }
            2 => {
                v_sz_530_ = lean_array_size(v_a_526_);
                v___x_531_ = 0usize;
                v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_casesOnStuckLHS_spec__1(v_sz_530_, v___x_531_, v_a_526_);
                if v_isShared_529_ == 0 {
                    leanh::lean_ctor_set(v___x_528_, 0, v___x_532_);
                    v___x_534_ = v___x_528_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
                    v___x_534_ = v_reuseFailAlloc_535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_534_;
            }
            4 => {
                if v_isShared_540_ == 0 {
                    v___x_542_ = v___x_539_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_543_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
                    v___x_542_ = v_reuseFailAlloc_543_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_542_;
            }
            6 => {
                if v_isShared_548_ == 0 {
                    v___x_550_ = v___x_547_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
                    v___x_550_ = v_reuseFailAlloc_551_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_550_;
            }
            8 => {
                if v_isShared_556_ == 0 {
                    v___x_558_ = v___x_555_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
                    v___x_558_ = v_reuseFailAlloc_559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_558_;
            }
            10 => {
                if v_isShared_564_ == 0 {
                    v___x_566_ = v___x_563_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_567_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
                    v___x_566_ = v_reuseFailAlloc_567_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_casesOnStuckLHS___boxed(
    mut v_mvarId_569_: *mut leanh::LeanObject,
    mut v_a_570_: *mut leanh::LeanObject,
    mut v_a_571_: *mut leanh::LeanObject,
    mut v_a_572_: *mut leanh::LeanObject,
    mut v_a_573_: *mut leanh::LeanObject,
    mut v_a_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Lean_Meta_casesOnStuckLHS(v_mvarId_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
    leanh::lean_dec(v_a_573_);
    leanh::lean_dec_ref(v_a_572_);
    leanh::lean_dec(v_a_571_);
    leanh::lean_dec_ref(v_a_570_);
    return v_res_575_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(
    mut v_00_u03b1_576_: *mut leanh::LeanObject,
    mut v_msg_577_: *mut leanh::LeanObject,
    mut v___y_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_583_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___redArg(
        v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_,
    );
    return v___x_583_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0___boxed(
    mut v_00_u03b1_584_: *mut leanh::LeanObject,
    mut v_msg_585_: *mut leanh::LeanObject,
    mut v___y_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
    mut v___y_588_: *mut leanh::LeanObject,
    mut v___y_589_: *mut leanh::LeanObject,
    mut v___y_590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_591_ = l_Lean_throwError___at___00Lean_Meta_casesOnStuckLHS_spec__0(
        v_00_u03b1_584_,
        v_msg_585_,
        v___y_586_,
        v___y_587_,
        v___y_588_,
        v___y_589_,
    );
    leanh::lean_dec(v___y_589_);
    leanh::lean_dec_ref(v___y_588_);
    leanh::lean_dec(v___y_587_);
    leanh::lean_dec_ref(v___y_586_);
    return v_res_591_;
}
pub unsafe fn l_Lean_Meta_casesOnStuckLHS_x3f(
    mut v_mvarId_592_: *mut leanh::LeanObject,
    mut v_a_593_: *mut leanh::LeanObject,
    mut v_a_594_: *mut leanh::LeanObject,
    mut v_a_595_: *mut leanh::LeanObject,
    mut v_a_596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_607_: u8 = 0;
    let mut v_a_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v___y_613_: u8 = 0;
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    let mut v___x_622_: u8 = 0;
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_598_ = l_Lean_Meta_casesOnStuckLHS(
                    v_mvarId_592_,
                    v_a_593_,
                    v_a_594_,
                    v_a_595_,
                    v_a_596_,
                );
                if leanh::lean_obj_tag(v___x_598_) == 0 {
                    v_a_599_ = leanh::lean_ctor_get(v___x_598_, 0);
                    v_isSharedCheck_607_ = (!leanh::lean_is_exclusive(v___x_598_)) as u8;
                    if v_isSharedCheck_607_ == 0 {
                        v___x_601_ = v___x_598_;
                        v_isShared_602_ = v_isSharedCheck_607_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_599_);
                        leanh::lean_dec(v___x_598_);
                        v___x_601_ = leanh::lean_box(0);
                        v_isShared_602_ = v_isSharedCheck_607_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_608_ = leanh::lean_ctor_get(v___x_598_, 0);
                    v_isSharedCheck_623_ = (!leanh::lean_is_exclusive(v___x_598_)) as u8;
                    if v_isSharedCheck_623_ == 0 {
                        v___x_610_ = v___x_598_;
                        v_isShared_611_ = v_isSharedCheck_623_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_608_);
                        leanh::lean_dec(v___x_598_);
                        v___x_610_ = leanh::lean_box(0);
                        v_isShared_611_ = v_isSharedCheck_623_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_603_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_603_, 0, v_a_599_);
                if v_isShared_602_ == 0 {
                    leanh::lean_ctor_set(v___x_601_, 0, v___x_603_);
                    v___x_605_ = v___x_601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
                    v___x_605_ = v_reuseFailAlloc_606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_605_;
            }
            3 => {
                v___x_621_ = l_Lean_Exception_isInterrupt(v_a_608_);
                if v___x_621_ == 0 {
                    leanh::lean_inc(v_a_608_);
                    v___x_622_ = l_Lean_Exception_isRuntime(v_a_608_);
                    v___y_613_ = v___x_622_;
                    state = 4;
                    continue;
                } else {
                    v___y_613_ = v___x_621_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_613_ == 0 {
                    leanh::lean_dec(v_a_608_);
                    v___x_614_ = leanh::lean_box(0);
                    if v_isShared_611_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_610_, 0);
                        leanh::lean_ctor_set(v___x_610_, 0, v___x_614_);
                        v___x_616_ = v___x_610_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_617_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
                        v___x_616_ = v_reuseFailAlloc_617_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_611_ == 0 {
                        v___x_619_ = v___x_610_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_608_);
                        v___x_619_ = v_reuseFailAlloc_620_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_616_;
            }
            6 => {
                return v___x_619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_casesOnStuckLHS_x3f___boxed(
    mut v_mvarId_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ =
        l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
    leanh::lean_dec(v_a_628_);
    leanh::lean_dec_ref(v_a_627_);
    leanh::lean_dec(v_a_626_);
    leanh::lean_dec_ref(v_a_625_);
    return v_res_630_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ProjFns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(
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
pub unsafe fn initialize_Lean_Meta_Tactic_CasesOnStuckLHS(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ProjFns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
}