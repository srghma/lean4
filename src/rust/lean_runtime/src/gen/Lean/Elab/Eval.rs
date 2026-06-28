// Lean compiler output
// Module: Lean.Elab.Eval
// Imports: Lean.Meta.Eval Lean.Elab.SyntheticMVars
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortTermExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::{
    initialize_Lean_Elab_SyntheticMVars, l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing,
    runtime_initialize_Lean_Elab_SyntheticMVars,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType, l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_unlockAsync;
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Eval::{
    initialize_Lean_Meta_Eval, l_Lean_Meta_evalExpr___redArg, runtime_initialize_Lean_Meta_Eval,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
};
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(
    mut v_e_360_: *mut LeanObject,
    mut v___y_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_363_: u8 = 0;
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_377_: u8 = 0;
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_383_: u8 = 0;
    let mut v_unused_384_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_363_ = l_Lean_Expr_hasMVar(v_e_360_);
                if v___x_363_ == 0 {
                    v___x_364_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_364_, 0, v_e_360_);
                    return v___x_364_;
                } else {
                    v___x_365_ = lean_st_ref_get(v___y_361_);
                    v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
                    lean_inc_ref(v_mctx_366_);
                    lean_dec(v___x_365_);
                    v___x_367_ = l_Lean_instantiateMVarsCore(v_mctx_366_, v_e_360_);
                    v_fst_368_ = lean_ctor_get(v___x_367_, 0);
                    lean_inc(v_fst_368_);
                    v_snd_369_ = lean_ctor_get(v___x_367_, 1);
                    lean_inc(v_snd_369_);
                    lean_dec_ref(v___x_367_);
                    v___x_370_ = lean_st_ref_take(v___y_361_);
                    v_cache_371_ = lean_ctor_get(v___x_370_, 1);
                    v_zetaDeltaFVarIds_372_ = lean_ctor_get(v___x_370_, 2);
                    v_postponed_373_ = lean_ctor_get(v___x_370_, 3);
                    v_diag_374_ = lean_ctor_get(v___x_370_, 4);
                    v_isSharedCheck_383_ = (!lean_is_exclusive(v___x_370_)) as u8;
                    if v_isSharedCheck_383_ == 0 {
                        v_unused_384_ = lean_ctor_get(v___x_370_, 0);
                        lean_dec(v_unused_384_);
                        v___x_376_ = v___x_370_;
                        v_isShared_377_ = v_isSharedCheck_383_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_374_);
                        lean_inc(v_postponed_373_);
                        lean_inc(v_zetaDeltaFVarIds_372_);
                        lean_inc(v_cache_371_);
                        lean_dec(v___x_370_);
                        v___x_376_ = lean_box(0);
                        v_isShared_377_ = v_isSharedCheck_383_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_377_ == 0 {
                    lean_ctor_set(v___x_376_, 0, v_snd_369_);
                    v___x_379_ = v___x_376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_382_, 0, v_snd_369_);
                    lean_ctor_set(v_reuseFailAlloc_382_, 1, v_cache_371_);
                    lean_ctor_set(v_reuseFailAlloc_382_, 2, v_zetaDeltaFVarIds_372_);
                    lean_ctor_set(v_reuseFailAlloc_382_, 3, v_postponed_373_);
                    lean_ctor_set(v_reuseFailAlloc_382_, 4, v_diag_374_);
                    v___x_379_ = v_reuseFailAlloc_382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_380_ = lean_st_ref_set(v___y_361_, v___x_379_);
                v___x_381_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_381_, 0, v_fst_368_);
                return v___x_381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg___boxed(
    mut v_e_385_: *mut LeanObject,
    mut v___y_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_388_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(
        v_e_385_, v___y_386_,
    );
    lean_dec(v___y_386_);
    return v_res_388_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0(
    mut v_e_389_: *mut LeanObject,
    mut v___y_390_: *mut LeanObject,
    mut v___y_391_: *mut LeanObject,
    mut v___y_392_: *mut LeanObject,
    mut v___y_393_: *mut LeanObject,
    mut v___y_394_: *mut LeanObject,
    mut v___y_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_397_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(
        v_e_389_, v___y_393_,
    );
    return v___x_397_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___boxed(
    mut v_e_398_: *mut LeanObject,
    mut v___y_399_: *mut LeanObject,
    mut v___y_400_: *mut LeanObject,
    mut v___y_401_: *mut LeanObject,
    mut v___y_402_: *mut LeanObject,
    mut v___y_403_: *mut LeanObject,
    mut v___y_404_: *mut LeanObject,
    mut v___y_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_406_: *mut LeanObject = core::ptr::null_mut();
    v_res_406_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0(
        v_e_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_,
    );
    lean_dec(v___y_404_);
    lean_dec_ref(v___y_403_);
    lean_dec(v___y_402_);
    lean_dec_ref(v___y_401_);
    lean_dec(v___y_400_);
    lean_dec_ref(v___y_399_);
    return v_res_406_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = lean_box(0);
    v___x_408_ = l_Lean_Elab_abortTermExceptionId;
    v___x_409_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_409_, 0, v___x_408_);
    lean_ctor_set(v___x_409_, 1, v___x_407_);
    return v___x_409_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg()
-> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0);
    v___x_412_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_412_, 0, v___x_411_);
    return v___x_412_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___boxed(
    mut v___y_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
    return v_res_414_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1(
    mut v_00_u03b1_415_: *mut LeanObject,
    mut v___y_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
    mut v___y_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
    return v___x_423_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___boxed(
    mut v_00_u03b1_424_: *mut LeanObject,
    mut v___y_425_: *mut LeanObject,
    mut v___y_426_: *mut LeanObject,
    mut v___y_427_: *mut LeanObject,
    mut v___y_428_: *mut LeanObject,
    mut v___y_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
    mut v___y_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_432_: *mut LeanObject = core::ptr::null_mut();
    v_res_432_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1(
        v_00_u03b1_424_,
        v___y_425_,
        v___y_426_,
        v___y_427_,
        v___y_428_,
        v___y_429_,
        v___y_430_,
    );
    lean_dec(v___y_430_);
    lean_dec_ref(v___y_429_);
    lean_dec(v___y_428_);
    lean_dec_ref(v___y_427_);
    lean_dec(v___y_426_);
    lean_dec_ref(v___y_425_);
    return v_res_432_;
}
pub unsafe fn l_Lean_Elab_Term_evalTerm___redArg___lam__0(
    mut v_value_433_: *mut LeanObject,
    mut v___x_434_: *mut LeanObject,
    mut v___x_435_: u8,
    mut v___x_436_: *mut LeanObject,
    mut v_type_437_: *mut LeanObject,
    mut v_safety_438_: u8,
    mut v___y_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
    mut v___y_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: u8 = 0;
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut v_a_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_476_: u8 = 0;
    let mut v_a_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_480_: u8 = 0;
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_484_: u8 = 0;
    let mut v_a_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_488_: u8 = 0;
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_492_: u8 = 0;
    let mut v_a_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_496_: u8 = 0;
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_500_: u8 = 0;
    let mut v_a_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_446_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v_value_433_,
                    v___x_434_,
                    v___x_435_,
                    v___x_435_,
                    v___x_436_,
                    v___y_439_,
                    v___y_440_,
                    v___y_441_,
                    v___y_442_,
                    v___y_443_,
                    v___y_444_,
                );
                if lean_obj_tag(v___x_446_) == 0 {
                    v_a_447_ = lean_ctor_get(v___x_446_, 0);
                    lean_inc(v_a_447_);
                    lean_dec_ref_known(v___x_446_, 1);
                    v___x_448_ = 0;
                    v___x_449_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                        v___x_448_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_,
                        v___y_444_,
                    );
                    if lean_obj_tag(v___x_449_) == 0 {
                        lean_dec_ref_known(v___x_449_, 1);
                        v___x_450_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(v_a_447_, v___y_442_);
                        if lean_obj_tag(v___x_450_) == 0 {
                            v_a_451_ = lean_ctor_get(v___x_450_, 0);
                            lean_inc_n(v_a_451_, 2);
                            lean_dec_ref_known(v___x_450_, 1);
                            v___x_452_ = l_Lean_Meta_getMVars(
                                v_a_451_, v___y_441_, v___y_442_, v___y_443_, v___y_444_,
                            );
                            if lean_obj_tag(v___x_452_) == 0 {
                                v_a_453_ = lean_ctor_get(v___x_452_, 0);
                                lean_inc(v_a_453_);
                                lean_dec_ref_known(v___x_452_, 1);
                                v___x_454_ = lean_box(0);
                                v___x_455_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                                    v_a_453_, v___x_454_, v___y_439_, v___y_440_, v___y_441_,
                                    v___y_442_, v___y_443_, v___y_444_,
                                );
                                lean_dec(v_a_453_);
                                if lean_obj_tag(v___x_455_) == 0 {
                                    v_a_456_ = lean_ctor_get(v___x_455_, 0);
                                    lean_inc(v_a_456_);
                                    lean_dec_ref_known(v___x_455_, 1);
                                    v___x_457_ = (lean_unbox(v_a_456_) as u8);
                                    lean_dec(v_a_456_);
                                    if v___x_457_ == 0 {
                                        v___x_458_ = l_Lean_Meta_evalExpr___redArg(
                                            v_type_437_,
                                            v_a_451_,
                                            v_safety_438_,
                                            v___x_435_,
                                            v___y_441_,
                                            v___y_442_,
                                            v___y_443_,
                                            v___y_444_,
                                        );
                                        return v___x_458_;
                                    } else {
                                        v___x_459_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
                                        if lean_obj_tag(v___x_459_) == 0 {
                                            lean_dec_ref_known(v___x_459_, 1);
                                            v___x_460_ = l_Lean_Meta_evalExpr___redArg(
                                                v_type_437_,
                                                v_a_451_,
                                                v_safety_438_,
                                                v___x_435_,
                                                v___y_441_,
                                                v___y_442_,
                                                v___y_443_,
                                                v___y_444_,
                                            );
                                            return v___x_460_;
                                        } else {
                                            lean_dec(v_a_451_);
                                            lean_dec_ref(v_type_437_);
                                            v_a_461_ = lean_ctor_get(v___x_459_, 0);
                                            v_isSharedCheck_468_ =
                                                (!lean_is_exclusive(v___x_459_)) as u8;
                                            if v_isSharedCheck_468_ == 0 {
                                                v___x_463_ = v___x_459_;
                                                v_isShared_464_ = v_isSharedCheck_468_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_461_);
                                                lean_dec(v___x_459_);
                                                v___x_463_ = lean_box(0);
                                                v_isShared_464_ = v_isSharedCheck_468_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_451_);
                                    lean_dec_ref(v_type_437_);
                                    v_a_469_ = lean_ctor_get(v___x_455_, 0);
                                    v_isSharedCheck_476_ = (!lean_is_exclusive(v___x_455_)) as u8;
                                    if v_isSharedCheck_476_ == 0 {
                                        v___x_471_ = v___x_455_;
                                        v_isShared_472_ = v_isSharedCheck_476_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_469_);
                                        lean_dec(v___x_455_);
                                        v___x_471_ = lean_box(0);
                                        v_isShared_472_ = v_isSharedCheck_476_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_451_);
                                lean_dec_ref(v_type_437_);
                                v_a_477_ = lean_ctor_get(v___x_452_, 0);
                                v_isSharedCheck_484_ = (!lean_is_exclusive(v___x_452_)) as u8;
                                if v_isSharedCheck_484_ == 0 {
                                    v___x_479_ = v___x_452_;
                                    v_isShared_480_ = v_isSharedCheck_484_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_477_);
                                    lean_dec(v___x_452_);
                                    v___x_479_ = lean_box(0);
                                    v_isShared_480_ = v_isSharedCheck_484_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_type_437_);
                            v_a_485_ = lean_ctor_get(v___x_450_, 0);
                            v_isSharedCheck_492_ = (!lean_is_exclusive(v___x_450_)) as u8;
                            if v_isSharedCheck_492_ == 0 {
                                v___x_487_ = v___x_450_;
                                v_isShared_488_ = v_isSharedCheck_492_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_485_);
                                lean_dec(v___x_450_);
                                v___x_487_ = lean_box(0);
                                v_isShared_488_ = v_isSharedCheck_492_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_447_);
                        lean_dec_ref(v_type_437_);
                        v_a_493_ = lean_ctor_get(v___x_449_, 0);
                        v_isSharedCheck_500_ = (!lean_is_exclusive(v___x_449_)) as u8;
                        if v_isSharedCheck_500_ == 0 {
                            v___x_495_ = v___x_449_;
                            v_isShared_496_ = v_isSharedCheck_500_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_493_);
                            lean_dec(v___x_449_);
                            v___x_495_ = lean_box(0);
                            v_isShared_496_ = v_isSharedCheck_500_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_437_);
                    v_a_501_ = lean_ctor_get(v___x_446_, 0);
                    v_isSharedCheck_508_ = (!lean_is_exclusive(v___x_446_)) as u8;
                    if v_isSharedCheck_508_ == 0 {
                        v___x_503_ = v___x_446_;
                        v_isShared_504_ = v_isSharedCheck_508_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_501_);
                        lean_dec(v___x_446_);
                        v___x_503_ = lean_box(0);
                        v_isShared_504_ = v_isSharedCheck_508_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_464_ == 0 {
                    v___x_466_ = v___x_463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
                    v___x_466_ = v_reuseFailAlloc_467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_466_;
            }
            3 => {
                if v_isShared_472_ == 0 {
                    v___x_474_ = v___x_471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
                    v___x_474_ = v_reuseFailAlloc_475_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_474_;
            }
            5 => {
                if v_isShared_480_ == 0 {
                    v___x_482_ = v___x_479_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
                    v___x_482_ = v_reuseFailAlloc_483_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_482_;
            }
            7 => {
                if v_isShared_488_ == 0 {
                    v___x_490_ = v___x_487_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
                    v___x_490_ = v_reuseFailAlloc_491_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_490_;
            }
            9 => {
                if v_isShared_496_ == 0 {
                    v___x_498_ = v___x_495_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
                    v___x_498_ = v_reuseFailAlloc_499_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_498_;
            }
            11 => {
                if v_isShared_504_ == 0 {
                    v___x_506_ = v___x_503_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
                    v___x_506_ = v_reuseFailAlloc_507_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_evalTerm___redArg___lam__0___boxed(
    mut v_value_509_: *mut LeanObject,
    mut v___x_510_: *mut LeanObject,
    mut v___x_511_: *mut LeanObject,
    mut v___x_512_: *mut LeanObject,
    mut v_type_513_: *mut LeanObject,
    mut v_safety_514_: *mut LeanObject,
    mut v___y_515_: *mut LeanObject,
    mut v___y_516_: *mut LeanObject,
    mut v___y_517_: *mut LeanObject,
    mut v___y_518_: *mut LeanObject,
    mut v___y_519_: *mut LeanObject,
    mut v___y_520_: *mut LeanObject,
    mut v___y_521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3646__boxed_522_: u8 = 0;
    let mut v_safety_boxed_523_: u8 = 0;
    let mut v_res_524_: *mut LeanObject = core::ptr::null_mut();
    v___x_3646__boxed_522_ = (lean_unbox(v___x_511_) as u8);
    v_safety_boxed_523_ = (lean_unbox(v_safety_514_) as u8);
    v_res_524_ = l_Lean_Elab_Term_evalTerm___redArg___lam__0(
        v_value_509_,
        v___x_510_,
        v___x_3646__boxed_522_,
        v___x_512_,
        v_type_513_,
        v_safety_boxed_523_,
        v___y_515_,
        v___y_516_,
        v___y_517_,
        v___y_518_,
        v___y_519_,
        v___y_520_,
    );
    lean_dec(v___y_520_);
    lean_dec_ref(v___y_519_);
    lean_dec(v___y_518_);
    lean_dec_ref(v___y_517_);
    lean_dec(v___y_516_);
    lean_dec_ref(v___y_515_);
    return v_res_524_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    v___x_525_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_525_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    v___x_526_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0);
    v___x_527_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_527_, 0, v___x_526_);
    return v___x_527_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1);
    v___x_529_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_529_, 0, v___x_528_);
    lean_ctor_set(v___x_529_, 1, v___x_528_);
    return v___x_529_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    v___x_530_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1);
    v___x_531_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_531_, 0, v___x_530_);
    lean_ctor_set(v___x_531_, 1, v___x_530_);
    lean_ctor_set(v___x_531_, 2, v___x_530_);
    lean_ctor_set(v___x_531_, 3, v___x_530_);
    lean_ctor_set(v___x_531_, 4, v___x_530_);
    lean_ctor_set(v___x_531_, 5, v___x_530_);
    return v___x_531_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(
    mut v_env_532_: *mut LeanObject,
    mut v___y_533_: *mut LeanObject,
    mut v___y_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_546_: u8 = 0;
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_558_: u8 = 0;
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v_unused_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_569_: u8 = 0;
    let mut v_unused_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_571_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_536_ = lean_st_ref_take(v___y_534_);
                v_nextMacroScope_537_ = lean_ctor_get(v___x_536_, 1);
                v_ngen_538_ = lean_ctor_get(v___x_536_, 2);
                v_auxDeclNGen_539_ = lean_ctor_get(v___x_536_, 3);
                v_traceState_540_ = lean_ctor_get(v___x_536_, 4);
                v_messages_541_ = lean_ctor_get(v___x_536_, 6);
                v_infoState_542_ = lean_ctor_get(v___x_536_, 7);
                v_snapshotTasks_543_ = lean_ctor_get(v___x_536_, 8);
                v_isSharedCheck_569_ = (!lean_is_exclusive(v___x_536_)) as u8;
                if v_isSharedCheck_569_ == 0 {
                    v_unused_570_ = lean_ctor_get(v___x_536_, 5);
                    lean_dec(v_unused_570_);
                    v_unused_571_ = lean_ctor_get(v___x_536_, 0);
                    lean_dec(v_unused_571_);
                    v___x_545_ = v___x_536_;
                    v_isShared_546_ = v_isSharedCheck_569_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_543_);
                    lean_inc(v_infoState_542_);
                    lean_inc(v_messages_541_);
                    lean_inc(v_traceState_540_);
                    lean_inc(v_auxDeclNGen_539_);
                    lean_inc(v_ngen_538_);
                    lean_inc(v_nextMacroScope_537_);
                    lean_dec(v___x_536_);
                    v___x_545_ = lean_box(0);
                    v_isShared_546_ = v_isSharedCheck_569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_547_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2);
                if v_isShared_546_ == 0 {
                    lean_ctor_set(v___x_545_, 5, v___x_547_);
                    lean_ctor_set(v___x_545_, 0, v_env_532_);
                    v___x_549_ = v___x_545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_568_, 0, v_env_532_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 1, v_nextMacroScope_537_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 2, v_ngen_538_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 3, v_auxDeclNGen_539_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 4, v_traceState_540_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 5, v___x_547_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 6, v_messages_541_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 7, v_infoState_542_);
                    lean_ctor_set(v_reuseFailAlloc_568_, 8, v_snapshotTasks_543_);
                    v___x_549_ = v_reuseFailAlloc_568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_550_ = lean_st_ref_set(v___y_534_, v___x_549_);
                v___x_551_ = lean_st_ref_take(v___y_533_);
                v_mctx_552_ = lean_ctor_get(v___x_551_, 0);
                v_zetaDeltaFVarIds_553_ = lean_ctor_get(v___x_551_, 2);
                v_postponed_554_ = lean_ctor_get(v___x_551_, 3);
                v_diag_555_ = lean_ctor_get(v___x_551_, 4);
                v_isSharedCheck_566_ = (!lean_is_exclusive(v___x_551_)) as u8;
                if v_isSharedCheck_566_ == 0 {
                    v_unused_567_ = lean_ctor_get(v___x_551_, 1);
                    lean_dec(v_unused_567_);
                    v___x_557_ = v___x_551_;
                    v_isShared_558_ = v_isSharedCheck_566_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_555_);
                    lean_inc(v_postponed_554_);
                    lean_inc(v_zetaDeltaFVarIds_553_);
                    lean_inc(v_mctx_552_);
                    lean_dec(v___x_551_);
                    v___x_557_ = lean_box(0);
                    v_isShared_558_ = v_isSharedCheck_566_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_559_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3);
                if v_isShared_558_ == 0 {
                    lean_ctor_set(v___x_557_, 1, v___x_559_);
                    v___x_561_ = v___x_557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_565_, 0, v_mctx_552_);
                    lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_559_);
                    lean_ctor_set(v_reuseFailAlloc_565_, 2, v_zetaDeltaFVarIds_553_);
                    lean_ctor_set(v_reuseFailAlloc_565_, 3, v_postponed_554_);
                    lean_ctor_set(v_reuseFailAlloc_565_, 4, v_diag_555_);
                    v___x_561_ = v_reuseFailAlloc_565_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_562_ = lean_st_ref_set(v___y_533_, v___x_561_);
                v___x_563_ = lean_box(0);
                v___x_564_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_564_, 0, v___x_563_);
                return v___x_564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___boxed(
    mut v_env_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
    mut v___y_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_576_: *mut LeanObject = core::ptr::null_mut();
    v_res_576_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_572_, v___y_573_, v___y_574_);
    lean_dec(v___y_574_);
    lean_dec(v___y_573_);
    return v_res_576_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(
    mut v_env_577_: *mut LeanObject,
    mut v_x_578_: *mut LeanObject,
    mut v___y_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
    mut v___y_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut v_unused_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_605_: u8 = 0;
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_609_: u8 = 0;
    let mut v_unused_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_611_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_586_ = lean_st_ref_get(v___y_584_);
                v_env_587_ = lean_ctor_get(v___x_586_, 0);
                lean_inc_ref(v_env_587_);
                lean_dec(v___x_586_);
                v___x_599_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_577_, v___y_582_, v___y_584_);
                lean_dec_ref(v___x_599_);
                lean_inc(v___y_584_);
                lean_inc_ref(v___y_583_);
                lean_inc(v___y_582_);
                lean_inc_ref(v___y_581_);
                lean_inc(v___y_580_);
                lean_inc_ref(v___y_579_);
                v___x_600_ = lean_apply_7(
                    v_x_578_,
                    v___y_579_,
                    v___y_580_,
                    v___y_581_,
                    v___y_582_,
                    v___y_583_,
                    v___y_584_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_600_) == 0 {
                    v_a_601_ = lean_ctor_get(v___x_600_, 0);
                    lean_inc(v_a_601_);
                    lean_dec_ref_known(v___x_600_, 1);
                    v___x_602_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_587_, v___y_582_, v___y_584_);
                    v_isSharedCheck_609_ = (!lean_is_exclusive(v___x_602_)) as u8;
                    if v_isSharedCheck_609_ == 0 {
                        v_unused_610_ = lean_ctor_get(v___x_602_, 0);
                        lean_dec(v_unused_610_);
                        v___x_604_ = v___x_602_;
                        v_isShared_605_ = v_isSharedCheck_609_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_602_);
                        v___x_604_ = lean_box(0);
                        v_isShared_605_ = v_isSharedCheck_609_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_611_ = lean_ctor_get(v___x_600_, 0);
                    lean_inc(v_a_611_);
                    lean_dec_ref_known(v___x_600_, 1);
                    v_a_589_ = v_a_611_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_590_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_587_, v___y_582_, v___y_584_);
                v_isSharedCheck_597_ = (!lean_is_exclusive(v___x_590_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v_unused_598_ = lean_ctor_get(v___x_590_, 0);
                    lean_dec(v_unused_598_);
                    v___x_592_ = v___x_590_;
                    v_isShared_593_ = v_isSharedCheck_597_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_590_);
                    v___x_592_ = lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_593_ == 0 {
                    lean_ctor_set_tag(v___x_592_, 1);
                    lean_ctor_set(v___x_592_, 0, v_a_589_);
                    v___x_595_ = v___x_592_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_589_);
                    v___x_595_ = v_reuseFailAlloc_596_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_595_;
            }
            4 => {
                if v_isShared_605_ == 0 {
                    lean_ctor_set(v___x_604_, 0, v_a_601_);
                    v___x_607_ = v___x_604_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_601_);
                    v___x_607_ = v_reuseFailAlloc_608_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg___boxed(
    mut v_env_612_: *mut LeanObject,
    mut v_x_613_: *mut LeanObject,
    mut v___y_614_: *mut LeanObject,
    mut v___y_615_: *mut LeanObject,
    mut v___y_616_: *mut LeanObject,
    mut v___y_617_: *mut LeanObject,
    mut v___y_618_: *mut LeanObject,
    mut v___y_619_: *mut LeanObject,
    mut v___y_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(
        v_env_612_, v_x_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_,
        v___y_619_,
    );
    lean_dec(v___y_619_);
    lean_dec_ref(v___y_618_);
    lean_dec(v___y_617_);
    lean_dec_ref(v___y_616_);
    lean_dec(v___y_615_);
    lean_dec_ref(v___y_614_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Elab_Term_evalTerm___redArg(
    mut v_type_622_: *mut LeanObject,
    mut v_value_623_: *mut LeanObject,
    mut v_safety_624_: u8,
    mut v_a_625_: *mut LeanObject,
    mut v_a_626_: *mut LeanObject,
    mut v_a_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
    mut v_a_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    v___x_632_ = lean_st_ref_get(v_a_630_);
    v_env_633_ = lean_ctor_get(v___x_632_, 0);
    lean_inc_ref(v_env_633_);
    lean_dec(v___x_632_);
    lean_inc_ref(v_type_622_);
    v___x_634_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_634_, 0, v_type_622_);
    v___x_635_ = 1;
    v___x_636_ = lean_box(0);
    v___x_637_ = lean_box((v___x_635_) as usize);
    v___x_638_ = lean_box((v_safety_624_) as usize);
    v___f_639_ = lean_alloc_closure(
        l_Lean_Elab_Term_evalTerm___redArg___lam__0___boxed as *mut core::ffi::c_void,
        13,
        6,
    );
    lean_closure_set(v___f_639_, 0, v_value_623_);
    lean_closure_set(v___f_639_, 1, v___x_634_);
    lean_closure_set(v___f_639_, 2, v___x_637_);
    lean_closure_set(v___f_639_, 3, v___x_636_);
    lean_closure_set(v___f_639_, 4, v_type_622_);
    lean_closure_set(v___f_639_, 5, v___x_638_);
    v___x_640_ = l_Lean_Environment_unlockAsync(v_env_633_);
    v___x_641_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(
        v___x_640_, v___f_639_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_,
    );
    return v___x_641_;
}
pub unsafe fn l_Lean_Elab_Term_evalTerm___redArg___boxed(
    mut v_type_642_: *mut LeanObject,
    mut v_value_643_: *mut LeanObject,
    mut v_safety_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_652_: u8 = 0;
    let mut v_res_653_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_652_ = (lean_unbox(v_safety_644_) as u8);
    v_res_653_ = l_Lean_Elab_Term_evalTerm___redArg(
        v_type_642_,
        v_value_643_,
        v_safety_boxed_652_,
        v_a_645_,
        v_a_646_,
        v_a_647_,
        v_a_648_,
        v_a_649_,
        v_a_650_,
    );
    lean_dec(v_a_650_);
    lean_dec_ref(v_a_649_);
    lean_dec(v_a_648_);
    lean_dec_ref(v_a_647_);
    lean_dec(v_a_646_);
    lean_dec_ref(v_a_645_);
    return v_res_653_;
}
pub unsafe fn l_Lean_Elab_Term_evalTerm(
    mut v_00_u03b1_654_: *mut LeanObject,
    mut v_type_655_: *mut LeanObject,
    mut v_value_656_: *mut LeanObject,
    mut v_safety_657_: u8,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
    mut v_a_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Lean_Elab_Term_evalTerm___redArg(
        v_type_655_,
        v_value_656_,
        v_safety_657_,
        v_a_658_,
        v_a_659_,
        v_a_660_,
        v_a_661_,
        v_a_662_,
        v_a_663_,
    );
    return v___x_665_;
}
pub unsafe fn l_Lean_Elab_Term_evalTerm___boxed(
    mut v_00_u03b1_666_: *mut LeanObject,
    mut v_type_667_: *mut LeanObject,
    mut v_value_668_: *mut LeanObject,
    mut v_safety_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
    mut v_a_672_: *mut LeanObject,
    mut v_a_673_: *mut LeanObject,
    mut v_a_674_: *mut LeanObject,
    mut v_a_675_: *mut LeanObject,
    mut v_a_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_safety_boxed_677_: u8 = 0;
    let mut v_res_678_: *mut LeanObject = core::ptr::null_mut();
    v_safety_boxed_677_ = (lean_unbox(v_safety_669_) as u8);
    v_res_678_ = l_Lean_Elab_Term_evalTerm(
        v_00_u03b1_666_,
        v_type_667_,
        v_value_668_,
        v_safety_boxed_677_,
        v_a_670_,
        v_a_671_,
        v_a_672_,
        v_a_673_,
        v_a_674_,
        v_a_675_,
    );
    lean_dec(v_a_675_);
    lean_dec_ref(v_a_674_);
    lean_dec(v_a_673_);
    lean_dec_ref(v_a_672_);
    lean_dec(v_a_671_);
    lean_dec_ref(v_a_670_);
    return v_res_678_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2(
    mut v_env_679_: *mut LeanObject,
    mut v___y_680_: *mut LeanObject,
    mut v___y_681_: *mut LeanObject,
    mut v___y_682_: *mut LeanObject,
    mut v___y_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_679_, v___y_683_, v___y_685_);
    return v___x_687_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___boxed(
    mut v_env_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2(
            v_env_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_,
        );
    lean_dec(v___y_694_);
    lean_dec_ref(v___y_693_);
    lean_dec(v___y_692_);
    lean_dec_ref(v___y_691_);
    lean_dec(v___y_690_);
    lean_dec_ref(v___y_689_);
    return v_res_696_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2(
    mut v_00_u03b1_697_: *mut LeanObject,
    mut v_env_698_: *mut LeanObject,
    mut v_x_699_: *mut LeanObject,
    mut v___y_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
    mut v___y_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(
        v_env_698_, v_x_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_,
        v___y_705_,
    );
    return v___x_707_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___boxed(
    mut v_00_u03b1_708_: *mut LeanObject,
    mut v_env_709_: *mut LeanObject,
    mut v_x_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
    mut v___y_713_: *mut LeanObject,
    mut v___y_714_: *mut LeanObject,
    mut v___y_715_: *mut LeanObject,
    mut v___y_716_: *mut LeanObject,
    mut v___y_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2(
        v_00_u03b1_708_,
        v_env_709_,
        v_x_710_,
        v___y_711_,
        v___y_712_,
        v___y_713_,
        v___y_714_,
        v___y_715_,
        v___y_716_,
    );
    lean_dec(v___y_716_);
    lean_dec_ref(v___y_715_);
    lean_dec(v___y_714_);
    lean_dec_ref(v___y_713_);
    lean_dec(v___y_712_);
    lean_dec_ref(v___y_711_);
    return v_res_718_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Eval(builtin);
}
