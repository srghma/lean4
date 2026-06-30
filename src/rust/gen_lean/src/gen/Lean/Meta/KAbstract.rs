// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Lean.HeadIndex Lean.Meta.Basic
use crate::ffi::{
    lean_array_push, lean_expr_abstract, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_usize_dec_eq,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Meta_Occurrences_contains;
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_instBEqOccurrences_beq;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_instBEqBinderInfo_beq, l_Lean_mkBVar,
};
use crate::r#gen::Lean::HeadIndex::{
    initialize_Lean_HeadIndex, l_Lean_Expr_headNumArgs, l_Lean_Expr_toHeadIndex,
    l_Lean_instBEqHeadIndex_beq, runtime_initialize_Lean_HeadIndex,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_isExprDefEq, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub unsafe fn l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
    mut v_p_318_: *mut leanh::LeanObject,
    mut v_occs_319_: *mut leanh::LeanObject,
    mut v_pHeadIdx_320_: *mut leanh::LeanObject,
    mut v_pNumArgs_321_: *mut leanh::LeanObject,
    mut v_e_322_: *mut leanh::LeanObject,
    mut v_offset_323_: *mut leanh::LeanObject,
    mut v_a_324_: *mut leanh::LeanObject,
    mut v_a_325_: *mut leanh::LeanObject,
    mut v_a_326_: *mut leanh::LeanObject,
    mut v_a_327_: *mut leanh::LeanObject,
    mut v_a_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_333_: u8 = 0;
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_341_: u8 = 0;
    let mut v___y_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_344_: u8 = 0;
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: usize = 0;
    let mut v___x_348_: usize = 0;
    let mut v___x_349_: u8 = 0;
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_356_: u8 = 0;
    let mut v___y_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_358_: u8 = 0;
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_369_: u8 = 0;
    let mut v___y_370_: u8 = 0;
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: u8 = 0;
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: usize = 0;
    let mut v___x_390_: usize = 0;
    let mut v___x_391_: u8 = 0;
    let mut v___x_392_: usize = 0;
    let mut v___x_393_: usize = 0;
    let mut v___x_394_: u8 = 0;
    let mut v_data_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_402_: usize = 0;
    let mut v___x_403_: usize = 0;
    let mut v___x_404_: u8 = 0;
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_412_: u8 = 0;
    let mut v_typeName_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_420_: u8 = 0;
    let mut v___x_421_: usize = 0;
    let mut v___x_422_: usize = 0;
    let mut v___x_423_: u8 = 0;
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_431_: u8 = 0;
    let mut v_declName_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_436_: u8 = 0;
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: usize = 0;
    let mut v___x_446_: usize = 0;
    let mut v___x_447_: u8 = 0;
    let mut v___x_448_: usize = 0;
    let mut v___x_449_: usize = 0;
    let mut v___x_450_: u8 = 0;
    let mut v_binderName_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_454_: u8 = 0;
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: usize = 0;
    let mut v___x_462_: usize = 0;
    let mut v___x_463_: u8 = 0;
    let mut v___x_464_: usize = 0;
    let mut v___x_465_: usize = 0;
    let mut v___x_466_: u8 = 0;
    let mut v_binderName_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_470_: u8 = 0;
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: usize = 0;
    let mut v___x_478_: usize = 0;
    let mut v___x_479_: u8 = 0;
    let mut v___x_480_: usize = 0;
    let mut v___x_481_: usize = 0;
    let mut v___x_482_: u8 = 0;
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u8 = 0;
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_509_: u8 = 0;
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_514_: u8 = 0;
    let mut v_unused_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut v_a_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_524_: u8 = 0;
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_484_ = l_Lean_Expr_hasLooseBVars(v_e_322_);
                if v___x_484_ == 0 {
                    leanh::lean_inc_ref(v_e_322_);
                    v___x_485_ = l_Lean_Expr_toHeadIndex(v_e_322_);
                    v___x_486_ = l_Lean_instBEqHeadIndex_beq(v___x_485_, v_pHeadIdx_320_);
                    leanh::lean_dec(v___x_485_);
                    if v___x_486_ == 0 {
                        v___y_378_ = v_a_324_;
                        v___y_379_ = v_a_325_;
                        v___y_380_ = v_a_326_;
                        v___y_381_ = v_a_327_;
                        v___y_382_ = v_a_328_;
                        state = 5;
                        continue;
                    } else {
                        if v___x_484_ == 0 {
                            v___x_487_ = l_Lean_Expr_headNumArgs(v_e_322_);
                            v___x_488_ = lean_nat_dec_eq(v___x_487_, v_pNumArgs_321_);
                            leanh::lean_dec(v___x_487_);
                            if v___x_488_ == 0 {
                                v___y_378_ = v_a_324_;
                                v___y_379_ = v_a_325_;
                                v___y_380_ = v_a_326_;
                                v___y_381_ = v_a_327_;
                                v___y_382_ = v_a_328_;
                                state = 5;
                                continue;
                            } else {
                                v___x_489_ = lean_st_ref_get(v_a_326_);
                                leanh::lean_inc_ref(v_p_318_);
                                leanh::lean_inc_ref(v_e_322_);
                                v___x_490_ = l_Lean_Meta_isExprDefEq(
                                    v_e_322_, v_p_318_, v_a_325_, v_a_326_, v_a_327_, v_a_328_,
                                );
                                if leanh::lean_obj_tag(v___x_490_) == 0 {
                                    v_a_491_ = leanh::lean_ctor_get(v___x_490_, 0);
                                    v_isSharedCheck_520_ =
                                        (!leanh::lean_is_exclusive(v___x_490_)) as u8;
                                    if v_isSharedCheck_520_ == 0 {
                                        v___x_493_ = v___x_490_;
                                        v_isShared_494_ = v_isSharedCheck_520_;
                                        state = 12;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_491_);
                                        leanh::lean_dec(v___x_490_);
                                        v___x_493_ = leanh::lean_box(0);
                                        v_isShared_494_ = v_isSharedCheck_520_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_489_);
                                    leanh::lean_dec(v_offset_323_);
                                    leanh::lean_dec_ref(v_e_322_);
                                    leanh::lean_dec_ref(v_p_318_);
                                    v_a_521_ = leanh::lean_ctor_get(v___x_490_, 0);
                                    v_isSharedCheck_528_ =
                                        (!leanh::lean_is_exclusive(v___x_490_)) as u8;
                                    if v_isSharedCheck_528_ == 0 {
                                        v___x_523_ = v___x_490_;
                                        v_isShared_524_ = v_isSharedCheck_528_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_521_);
                                        leanh::lean_dec(v___x_490_);
                                        v___x_523_ = leanh::lean_box(0);
                                        v_isShared_524_ = v_isSharedCheck_528_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___y_378_ = v_a_324_;
                            v___y_379_ = v_a_325_;
                            v___y_380_ = v_a_326_;
                            v___y_381_ = v_a_327_;
                            v___y_382_ = v_a_328_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___y_378_ = v_a_324_;
                    v___y_379_ = v_a_325_;
                    v___y_380_ = v_a_326_;
                    v___y_381_ = v_a_327_;
                    v___y_382_ = v_a_328_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                if v___y_333_ == 0 {
                    leanh::lean_dec_ref(v_e_322_);
                    v___x_334_ = l_Lean_Expr_app___override(v___y_331_, v___y_332_);
                    v___x_335_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_335_, 0, v___x_334_);
                    return v___x_335_;
                } else {
                    leanh::lean_dec_ref(v___y_332_);
                    leanh::lean_dec_ref(v___y_331_);
                    v___x_336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_336_, 0, v_e_322_);
                    return v___x_336_;
                }
            }
            2 => {
                if v___y_344_ == 0 {
                    leanh::lean_dec_ref(v___y_339_);
                    leanh::lean_dec_ref(v_e_322_);
                    v___x_345_ = l_Lean_Expr_letE___override(
                        v___y_340_, v___y_343_, v___y_338_, v___y_342_, v___y_341_,
                    );
                    v___x_346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_346_, 0, v___x_345_);
                    return v___x_346_;
                } else {
                    v___x_347_ = lean_ptr_addr(v___y_339_);
                    leanh::lean_dec_ref(v___y_339_);
                    v___x_348_ = lean_ptr_addr(v___y_342_);
                    v___x_349_ = lean_usize_dec_eq(v___x_347_, v___x_348_);
                    if v___x_349_ == 0 {
                        leanh::lean_dec_ref(v_e_322_);
                        v___x_350_ = l_Lean_Expr_letE___override(
                            v___y_340_, v___y_343_, v___y_338_, v___y_342_, v___y_341_,
                        );
                        v___x_351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_351_, 0, v___x_350_);
                        return v___x_351_;
                    } else {
                        leanh::lean_dec_ref(v___y_343_);
                        leanh::lean_dec_ref(v___y_342_);
                        leanh::lean_dec(v___y_340_);
                        leanh::lean_dec_ref(v___y_338_);
                        v___x_352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_352_, 0, v_e_322_);
                        return v___x_352_;
                    }
                }
            }
            3 => {
                if v___y_358_ == 0 {
                    leanh::lean_dec_ref(v_e_322_);
                    v___x_359_ =
                        l_Lean_Expr_lam___override(v___y_354_, v___y_355_, v___y_357_, v___y_356_);
                    v___x_360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_360_, 0, v___x_359_);
                    return v___x_360_;
                } else {
                    v___x_361_ = l_Lean_instBEqBinderInfo_beq(v___y_356_, v___y_356_);
                    if v___x_361_ == 0 {
                        leanh::lean_dec_ref(v_e_322_);
                        v___x_362_ = l_Lean_Expr_lam___override(
                            v___y_354_, v___y_355_, v___y_357_, v___y_356_,
                        );
                        v___x_363_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_363_, 0, v___x_362_);
                        return v___x_363_;
                    } else {
                        leanh::lean_dec_ref(v___y_357_);
                        leanh::lean_dec_ref(v___y_355_);
                        leanh::lean_dec(v___y_354_);
                        v___x_364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_364_, 0, v_e_322_);
                        return v___x_364_;
                    }
                }
            }
            4 => {
                if v___y_370_ == 0 {
                    leanh::lean_dec_ref(v_e_322_);
                    v___x_371_ = l_Lean_Expr_forallE___override(
                        v___y_368_, v___y_366_, v___y_367_, v___y_369_,
                    );
                    v___x_372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
                    return v___x_372_;
                } else {
                    v___x_373_ = l_Lean_instBEqBinderInfo_beq(v___y_369_, v___y_369_);
                    if v___x_373_ == 0 {
                        leanh::lean_dec_ref(v_e_322_);
                        v___x_374_ = l_Lean_Expr_forallE___override(
                            v___y_368_, v___y_366_, v___y_367_, v___y_369_,
                        );
                        v___x_375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_375_, 0, v___x_374_);
                        return v___x_375_;
                    } else {
                        leanh::lean_dec(v___y_368_);
                        leanh::lean_dec_ref(v___y_367_);
                        leanh::lean_dec_ref(v___y_366_);
                        v___x_376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_376_, 0, v_e_322_);
                        return v___x_376_;
                    }
                }
            }
            5 => match leanh::lean_obj_tag(v_e_322_) {
                5 => {
                    v_fn_383_ = leanh::lean_ctor_get(v_e_322_, 0);
                    v_arg_384_ = leanh::lean_ctor_get(v_e_322_, 1);
                    leanh::lean_inc(v_offset_323_);
                    leanh::lean_inc_ref(v_fn_383_);
                    leanh::lean_inc_ref(v_p_318_);
                    v___x_385_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_318_,
                        v_occs_319_,
                        v_pHeadIdx_320_,
                        v_pNumArgs_321_,
                        v_fn_383_,
                        v_offset_323_,
                        v___y_378_,
                        v___y_379_,
                        v___y_380_,
                        v___y_381_,
                        v___y_382_,
                    );
                    if leanh::lean_obj_tag(v___x_385_) == 0 {
                        v_a_386_ = leanh::lean_ctor_get(v___x_385_, 0);
                        leanh::lean_inc(v_a_386_);
                        leanh::lean_dec_ref_known(v___x_385_, 1);
                        leanh::lean_inc_ref(v_arg_384_);
                        v___x_387_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                            v_p_318_,
                            v_occs_319_,
                            v_pHeadIdx_320_,
                            v_pNumArgs_321_,
                            v_arg_384_,
                            v_offset_323_,
                            v___y_378_,
                            v___y_379_,
                            v___y_380_,
                            v___y_381_,
                            v___y_382_,
                        );
                        if leanh::lean_obj_tag(v___x_387_) == 0 {
                            v_a_388_ = leanh::lean_ctor_get(v___x_387_, 0);
                            leanh::lean_inc(v_a_388_);
                            leanh::lean_dec_ref_known(v___x_387_, 1);
                            v___x_389_ = lean_ptr_addr(v_fn_383_);
                            v___x_390_ = lean_ptr_addr(v_a_386_);
                            v___x_391_ = lean_usize_dec_eq(v___x_389_, v___x_390_);
                            if v___x_391_ == 0 {
                                v___y_331_ = v_a_386_;
                                v___y_332_ = v_a_388_;
                                v___y_333_ = v___x_391_;
                                state = 1;
                                continue;
                            } else {
                                v___x_392_ = lean_ptr_addr(v_arg_384_);
                                v___x_393_ = lean_ptr_addr(v_a_388_);
                                v___x_394_ = lean_usize_dec_eq(v___x_392_, v___x_393_);
                                v___y_331_ = v_a_386_;
                                v___y_332_ = v_a_388_;
                                v___y_333_ = v___x_394_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_386_);
                            leanh::lean_dec_ref_known(v_e_322_, 2);
                            return v___x_387_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_322_, 2);
                        leanh::lean_dec(v_offset_323_);
                        leanh::lean_dec_ref(v_p_318_);
                        return v___x_385_;
                    }
                }
                10 => {
                    v_data_395_ = leanh::lean_ctor_get(v_e_322_, 0);
                    v_expr_396_ = leanh::lean_ctor_get(v_e_322_, 1);
                    leanh::lean_inc_ref(v_expr_396_);
                    v___x_397_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_318_,
                        v_occs_319_,
                        v_pHeadIdx_320_,
                        v_pNumArgs_321_,
                        v_expr_396_,
                        v_offset_323_,
                        v___y_378_,
                        v___y_379_,
                        v___y_380_,
                        v___y_381_,
                        v___y_382_,
                    );
                    if leanh::lean_obj_tag(v___x_397_) == 0 {
                        v_a_398_ = leanh::lean_ctor_get(v___x_397_, 0);
                        v_isSharedCheck_412_ = (!leanh::lean_is_exclusive(v___x_397_)) as u8;
                        if v_isSharedCheck_412_ == 0 {
                            v___x_400_ = v___x_397_;
                            v_isShared_401_ = v_isSharedCheck_412_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_398_);
                            leanh::lean_dec(v___x_397_);
                            v___x_400_ = leanh::lean_box(0);
                            v_isShared_401_ = v_isSharedCheck_412_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_322_, 2);
                        return v___x_397_;
                    }
                }
                11 => {
                    v_typeName_413_ = leanh::lean_ctor_get(v_e_322_, 0);
                    v_idx_414_ = leanh::lean_ctor_get(v_e_322_, 1);
                    v_struct_415_ = leanh::lean_ctor_get(v_e_322_, 2);
                    leanh::lean_inc_ref(v_struct_415_);
                    v___x_416_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_318_,
                        v_occs_319_,
                        v_pHeadIdx_320_,
                        v_pNumArgs_321_,
                        v_struct_415_,
                        v_offset_323_,
                        v___y_378_,
                        v___y_379_,
                        v___y_380_,
                        v___y_381_,
                        v___y_382_,
                    );
                    if leanh::lean_obj_tag(v___x_416_) == 0 {
                        v_a_417_ = leanh::lean_ctor_get(v___x_416_, 0);
                        v_isSharedCheck_431_ = (!leanh::lean_is_exclusive(v___x_416_)) as u8;
                        if v_isSharedCheck_431_ == 0 {
                            v___x_419_ = v___x_416_;
                            v_isShared_420_ = v_isSharedCheck_431_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_417_);
                            leanh::lean_dec(v___x_416_);
                            v___x_419_ = leanh::lean_box(0);
                            v_isShared_420_ = v_isSharedCheck_431_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_322_, 3);
                        return v___x_416_;
                    }
                }
                8 => {
                    v_declName_432_ = leanh::lean_ctor_get(v_e_322_, 0);
                    v_type_433_ = leanh::lean_ctor_get(v_e_322_, 1);
                    v_value_434_ = leanh::lean_ctor_get(v_e_322_, 2);
                    v_body_435_ = leanh::lean_ctor_get(v_e_322_, 3);
                    v_nondep_436_ = leanh::lean_ctor_get_uint8(
                        v_e_322_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_323_);
                    leanh::lean_inc_ref(v_type_433_);
                    leanh::lean_inc_ref(v_p_318_);
                    v___x_437_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_318_,
                        v_occs_319_,
                        v_pHeadIdx_320_,
                        v_pNumArgs_321_,
                        v_type_433_,
                        v_offset_323_,
                        v___y_378_,
                        v___y_379_,
                        v___y_380_,
                        v___y_381_,
                        v___y_382_,
                    );
                    if leanh::lean_obj_tag(v___x_437_) == 0 {
                        v_a_438_ = leanh::lean_ctor_get(v___x_437_, 0);
                        leanh::lean_inc(v_a_438_);
                        leanh::lean_dec_ref_known(v___x_437_, 1);
                        leanh::lean_inc(v_offset_323_);
                        leanh::lean_inc_ref(v_value_434_);
                        leanh::lean_inc_ref(v_p_318_);
                        v___x_439_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                            v_p_318_,
                            v_occs_319_,
                            v_pHeadIdx_320_,
                            v_pNumArgs_321_,
                            v_value_434_,
                            v_offset_323_,
                            v___y_378_,
                            v___y_379_,
                            v___y_380_,
                            v___y_381_,
                            v___y_382_,
                        );
                        if leanh::lean_obj_tag(v___x_439_) == 0 {
                            v_a_440_ = leanh::lean_ctor_get(v___x_439_, 0);
                            leanh::lean_inc(v_a_440_);
                            leanh::lean_dec_ref_known(v___x_439_, 1);
                            v___x_441_ = leanh::lean_unsigned_to_nat(1);
                            v___x_442_ = lean_nat_add(v_offset_323_, v___x_441_);
                            leanh::lean_dec(v_offset_323_);
                            leanh::lean_inc_ref(v_body_435_);
                            v___x_443_ =
                                l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                                    v_p_318_,
                                    v_occs_319_,
                                    v_pHeadIdx_320_,
                                    v_pNumArgs_321_,
                                    v_body_435_,
                                    v___x_442_,
                                    v___y_378_,
                                    v___y_379_,
                                    v___y_380_,
                                    v___y_381_,
                                    v___y_382_,
                                );
                            if leanh::lean_obj_tag(v___x_443_) == 0 {
                                v_a_444_ = leanh::lean_ctor_get(v___x_443_, 0);
                                leanh::lean_inc(v_a_444_);
                                leanh::lean_dec_ref_known(v___x_443_, 1);
                                v___x_445_ = lean_ptr_addr(v_type_433_);
                                v___x_446_ = lean_ptr_addr(v_a_438_);
                                v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
                                if v___x_447_ == 0 {
                                    leanh::lean_inc(v_declName_432_);
                                    leanh::lean_inc_ref(v_body_435_);
                                    v___y_338_ = v_a_440_;
                                    v___y_339_ = v_body_435_;
                                    v___y_340_ = v_declName_432_;
                                    v___y_341_ = v_nondep_436_;
                                    v___y_342_ = v_a_444_;
                                    v___y_343_ = v_a_438_;
                                    v___y_344_ = v___x_447_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_448_ = lean_ptr_addr(v_value_434_);
                                    v___x_449_ = lean_ptr_addr(v_a_440_);
                                    v___x_450_ = lean_usize_dec_eq(v___x_448_, v___x_449_);
                                    leanh::lean_inc(v_declName_432_);
                                    leanh::lean_inc_ref(v_body_435_);
                                    v___y_338_ = v_a_440_;
                                    v___y_339_ = v_body_435_;
                                    v___y_340_ = v_declName_432_;
                                    v___y_341_ = v_nondep_436_;
                                    v___y_342_ = v_a_444_;
                                    v___y_343_ = v_a_438_;
                                    v___y_344_ = v___x_450_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_440_);
                                leanh::lean_dec(v_a_438_);
                                leanh::lean_dec_ref_known(v_e_322_, 4);
                                return v___x_443_;
                            }
                        } else {
                            leanh::lean_dec(v_a_438_);
                            leanh::lean_dec_ref_known(v_e_322_, 4);
                            leanh::lean_dec(v_offset_323_);
                            leanh::lean_dec_ref(v_p_318_);
                            return v___x_439_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_322_, 4);
                        leanh::lean_dec(v_offset_323_);
                        leanh::lean_dec_ref(v_p_318_);
                        return v___x_437_;
                    }
                }
                6 => {
                    v_binderName_451_ = leanh::lean_ctor_get(v_e_322_, 0);
                    v_binderType_452_ = leanh::lean_ctor_get(v_e_322_, 1);
                    v_body_453_ = leanh::lean_ctor_get(v_e_322_, 2);
                    v_binderInfo_454_ = leanh::lean_ctor_get_uint8(
                        v_e_322_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_323_);
                    leanh::lean_inc_ref(v_binderType_452_);
                    leanh::lean_inc_ref(v_p_318_);
                    v___x_455_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_318_,
                        v_occs_319_,
                        v_pHeadIdx_320_,
                        v_pNumArgs_321_,
                        v_binderType_452_,
                        v_offset_323_,
                        v___y_378_,
                        v___y_379_,
                        v___y_380_,
                        v___y_381_,
                        v___y_382_,
                    );
                    if leanh::lean_obj_tag(v___x_455_) == 0 {
                        v_a_456_ = leanh::lean_ctor_get(v___x_455_, 0);
                        leanh::lean_inc(v_a_456_);
                        leanh::lean_dec_ref_known(v___x_455_, 1);
                        v___x_457_ = leanh::lean_unsigned_to_nat(1);
                        v___x_458_ = lean_nat_add(v_offset_323_, v___x_457_);
                        leanh::lean_dec(v_offset_323_);
                        leanh::lean_inc_ref(v_body_453_);
                        v___x_459_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                            v_p_318_,
                            v_occs_319_,
                            v_pHeadIdx_320_,
                            v_pNumArgs_321_,
                            v_body_453_,
                            v___x_458_,
                            v___y_378_,
                            v___y_379_,
                            v___y_380_,
                            v___y_381_,
                            v___y_382_,
                        );
                        if leanh::lean_obj_tag(v___x_459_) == 0 {
                            v_a_460_ = leanh::lean_ctor_get(v___x_459_, 0);
                            leanh::lean_inc(v_a_460_);
                            leanh::lean_dec_ref_known(v___x_459_, 1);
                            v___x_461_ = lean_ptr_addr(v_binderType_452_);
                            v___x_462_ = lean_ptr_addr(v_a_456_);
                            v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
                            if v___x_463_ == 0 {
                                leanh::lean_inc(v_binderName_451_);
                                v___y_354_ = v_binderName_451_;
                                v___y_355_ = v_a_456_;
                                v___y_356_ = v_binderInfo_454_;
                                v___y_357_ = v_a_460_;
                                v___y_358_ = v___x_463_;
                                state = 3;
                                continue;
                            } else {
                                v___x_464_ = lean_ptr_addr(v_body_453_);
                                v___x_465_ = lean_ptr_addr(v_a_460_);
                                v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
                                leanh::lean_inc(v_binderName_451_);
                                v___y_354_ = v_binderName_451_;
                                v___y_355_ = v_a_456_;
                                v___y_356_ = v_binderInfo_454_;
                                v___y_357_ = v_a_460_;
                                v___y_358_ = v___x_466_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_456_);
                            leanh::lean_dec_ref_known(v_e_322_, 3);
                            return v___x_459_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_322_, 3);
                        leanh::lean_dec(v_offset_323_);
                        leanh::lean_dec_ref(v_p_318_);
                        return v___x_455_;
                    }
                }
                7 => {
                    v_binderName_467_ = leanh::lean_ctor_get(v_e_322_, 0);
                    v_binderType_468_ = leanh::lean_ctor_get(v_e_322_, 1);
                    v_body_469_ = leanh::lean_ctor_get(v_e_322_, 2);
                    v_binderInfo_470_ = leanh::lean_ctor_get_uint8(
                        v_e_322_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_323_);
                    leanh::lean_inc_ref(v_binderType_468_);
                    leanh::lean_inc_ref(v_p_318_);
                    v___x_471_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_318_,
                        v_occs_319_,
                        v_pHeadIdx_320_,
                        v_pNumArgs_321_,
                        v_binderType_468_,
                        v_offset_323_,
                        v___y_378_,
                        v___y_379_,
                        v___y_380_,
                        v___y_381_,
                        v___y_382_,
                    );
                    if leanh::lean_obj_tag(v___x_471_) == 0 {
                        v_a_472_ = leanh::lean_ctor_get(v___x_471_, 0);
                        leanh::lean_inc(v_a_472_);
                        leanh::lean_dec_ref_known(v___x_471_, 1);
                        v___x_473_ = leanh::lean_unsigned_to_nat(1);
                        v___x_474_ = lean_nat_add(v_offset_323_, v___x_473_);
                        leanh::lean_dec(v_offset_323_);
                        leanh::lean_inc_ref(v_body_469_);
                        v___x_475_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                            v_p_318_,
                            v_occs_319_,
                            v_pHeadIdx_320_,
                            v_pNumArgs_321_,
                            v_body_469_,
                            v___x_474_,
                            v___y_378_,
                            v___y_379_,
                            v___y_380_,
                            v___y_381_,
                            v___y_382_,
                        );
                        if leanh::lean_obj_tag(v___x_475_) == 0 {
                            v_a_476_ = leanh::lean_ctor_get(v___x_475_, 0);
                            leanh::lean_inc(v_a_476_);
                            leanh::lean_dec_ref_known(v___x_475_, 1);
                            v___x_477_ = lean_ptr_addr(v_binderType_468_);
                            v___x_478_ = lean_ptr_addr(v_a_472_);
                            v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
                            if v___x_479_ == 0 {
                                leanh::lean_inc(v_binderName_467_);
                                v___y_366_ = v_a_472_;
                                v___y_367_ = v_a_476_;
                                v___y_368_ = v_binderName_467_;
                                v___y_369_ = v_binderInfo_470_;
                                v___y_370_ = v___x_479_;
                                state = 4;
                                continue;
                            } else {
                                v___x_480_ = lean_ptr_addr(v_body_469_);
                                v___x_481_ = lean_ptr_addr(v_a_476_);
                                v___x_482_ = lean_usize_dec_eq(v___x_480_, v___x_481_);
                                leanh::lean_inc(v_binderName_467_);
                                v___y_366_ = v_a_472_;
                                v___y_367_ = v_a_476_;
                                v___y_368_ = v_binderName_467_;
                                v___y_369_ = v_binderInfo_470_;
                                v___y_370_ = v___x_482_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_472_);
                            leanh::lean_dec_ref_known(v_e_322_, 3);
                            return v___x_475_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_322_, 3);
                        leanh::lean_dec(v_offset_323_);
                        leanh::lean_dec_ref(v_p_318_);
                        return v___x_471_;
                    }
                }
                _ => {
                    leanh::lean_dec(v_offset_323_);
                    leanh::lean_dec_ref(v_p_318_);
                    v___x_483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_483_, 0, v_e_322_);
                    return v___x_483_;
                }
            },
            6 => {
                v___x_402_ = lean_ptr_addr(v_expr_396_);
                v___x_403_ = lean_ptr_addr(v_a_398_);
                v___x_404_ = lean_usize_dec_eq(v___x_402_, v___x_403_);
                if v___x_404_ == 0 {
                    leanh::lean_inc(v_data_395_);
                    leanh::lean_dec_ref_known(v_e_322_, 2);
                    v___x_405_ = l_Lean_Expr_mdata___override(v_data_395_, v_a_398_);
                    if v_isShared_401_ == 0 {
                        leanh::lean_ctor_set(v___x_400_, 0, v___x_405_);
                        v___x_407_ = v___x_400_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
                        v___x_407_ = v_reuseFailAlloc_408_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_398_);
                    if v_isShared_401_ == 0 {
                        leanh::lean_ctor_set(v___x_400_, 0, v_e_322_);
                        v___x_410_ = v___x_400_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_411_, 0, v_e_322_);
                        v___x_410_ = v_reuseFailAlloc_411_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_407_;
            }
            8 => {
                return v___x_410_;
            }
            9 => {
                v___x_421_ = lean_ptr_addr(v_struct_415_);
                v___x_422_ = lean_ptr_addr(v_a_417_);
                v___x_423_ = lean_usize_dec_eq(v___x_421_, v___x_422_);
                if v___x_423_ == 0 {
                    leanh::lean_inc(v_idx_414_);
                    leanh::lean_inc(v_typeName_413_);
                    leanh::lean_dec_ref_known(v_e_322_, 3);
                    v___x_424_ = l_Lean_Expr_proj___override(v_typeName_413_, v_idx_414_, v_a_417_);
                    if v_isShared_420_ == 0 {
                        leanh::lean_ctor_set(v___x_419_, 0, v___x_424_);
                        v___x_426_ = v___x_419_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
                        v___x_426_ = v_reuseFailAlloc_427_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_417_);
                    if v_isShared_420_ == 0 {
                        leanh::lean_ctor_set(v___x_419_, 0, v_e_322_);
                        v___x_429_ = v___x_419_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_430_, 0, v_e_322_);
                        v___x_429_ = v_reuseFailAlloc_430_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_426_;
            }
            11 => {
                return v___x_429_;
            }
            12 => {
                v___x_495_ = (leanh::lean_unbox(v_a_491_) as u8);
                leanh::lean_dec(v_a_491_);
                if v___x_495_ == 0 {
                    leanh::lean_del_object(v___x_493_);
                    leanh::lean_dec(v___x_489_);
                    v___y_378_ = v_a_324_;
                    v___y_379_ = v_a_325_;
                    v___y_380_ = v_a_326_;
                    v___y_381_ = v_a_327_;
                    v___y_382_ = v_a_328_;
                    state = 5;
                    continue;
                } else {
                    v___x_496_ = lean_st_ref_get(v_a_324_);
                    v___x_497_ = leanh::lean_unsigned_to_nat(1);
                    v___x_498_ = lean_nat_add(v___x_496_, v___x_497_);
                    v___x_499_ = lean_st_ref_set(v_a_324_, v___x_498_);
                    v___x_500_ = l_Lean_Meta_Occurrences_contains(v_occs_319_, v___x_496_);
                    leanh::lean_dec(v___x_496_);
                    if v___x_500_ == 0 {
                        leanh::lean_del_object(v___x_493_);
                        v___x_501_ = lean_st_ref_take(v_a_326_);
                        v_mctx_502_ = leanh::lean_ctor_get(v___x_489_, 0);
                        leanh::lean_inc_ref(v_mctx_502_);
                        leanh::lean_dec(v___x_489_);
                        v_cache_503_ = leanh::lean_ctor_get(v___x_501_, 1);
                        v_zetaDeltaFVarIds_504_ = leanh::lean_ctor_get(v___x_501_, 2);
                        v_postponed_505_ = leanh::lean_ctor_get(v___x_501_, 3);
                        v_diag_506_ = leanh::lean_ctor_get(v___x_501_, 4);
                        v_isSharedCheck_514_ = (!leanh::lean_is_exclusive(v___x_501_)) as u8;
                        if v_isSharedCheck_514_ == 0 {
                            v_unused_515_ = leanh::lean_ctor_get(v___x_501_, 0);
                            leanh::lean_dec(v_unused_515_);
                            v___x_508_ = v___x_501_;
                            v_isShared_509_ = v_isSharedCheck_514_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_diag_506_);
                            leanh::lean_inc(v_postponed_505_);
                            leanh::lean_inc(v_zetaDeltaFVarIds_504_);
                            leanh::lean_inc(v_cache_503_);
                            leanh::lean_dec(v___x_501_);
                            v___x_508_ = leanh::lean_box(0);
                            v_isShared_509_ = v_isSharedCheck_514_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_489_);
                        leanh::lean_dec_ref(v_e_322_);
                        leanh::lean_dec_ref(v_p_318_);
                        v___x_516_ = l_Lean_mkBVar(v_offset_323_);
                        if v_isShared_494_ == 0 {
                            leanh::lean_ctor_set(v___x_493_, 0, v___x_516_);
                            v___x_518_ = v___x_493_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
                            v___x_518_ = v_reuseFailAlloc_519_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if v_isShared_509_ == 0 {
                    leanh::lean_ctor_set(v___x_508_, 0, v_mctx_502_);
                    v___x_511_ = v___x_508_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_513_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_513_, 0, v_mctx_502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_513_, 1, v_cache_503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_513_, 2, v_zetaDeltaFVarIds_504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_513_, 3, v_postponed_505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_513_, 4, v_diag_506_);
                    v___x_511_ = v_reuseFailAlloc_513_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_512_ = lean_st_ref_set(v_a_326_, v___x_511_);
                v___y_378_ = v_a_324_;
                v___y_379_ = v_a_325_;
                v___y_380_ = v_a_326_;
                v___y_381_ = v_a_327_;
                v___y_382_ = v_a_328_;
                state = 5;
                continue;
            }
            15 => {
                return v___x_518_;
            }
            16 => {
                if v_isShared_524_ == 0 {
                    v___x_526_ = v___x_523_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
                    v___x_526_ = v_reuseFailAlloc_527_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(
    mut v_p_529_: *mut leanh::LeanObject,
    mut v_occs_530_: *mut leanh::LeanObject,
    mut v_pHeadIdx_531_: *mut leanh::LeanObject,
    mut v_pNumArgs_532_: *mut leanh::LeanObject,
    mut v_e_533_: *mut leanh::LeanObject,
    mut v_offset_534_: *mut leanh::LeanObject,
    mut v_a_535_: *mut leanh::LeanObject,
    mut v_a_536_: *mut leanh::LeanObject,
    mut v_a_537_: *mut leanh::LeanObject,
    mut v_a_538_: *mut leanh::LeanObject,
    mut v_a_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_541_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
        v_p_529_,
        v_occs_530_,
        v_pHeadIdx_531_,
        v_pNumArgs_532_,
        v_e_533_,
        v_offset_534_,
        v_a_535_,
        v_a_536_,
        v_a_537_,
        v_a_538_,
        v_a_539_,
    );
    leanh::lean_dec(v_a_539_);
    leanh::lean_dec_ref(v_a_538_);
    leanh::lean_dec(v_a_537_);
    leanh::lean_dec_ref(v_a_536_);
    leanh::lean_dec(v_a_535_);
    leanh::lean_dec(v_pNumArgs_532_);
    leanh::lean_dec(v_pHeadIdx_531_);
    leanh::lean_dec(v_occs_530_);
    return v_res_541_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(
    mut v_e_542_: *mut leanh::LeanObject,
    mut v___y_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_unused_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_545_ = l_Lean_Expr_hasMVar(v_e_542_);
                if v___x_545_ == 0 {
                    v___x_546_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_546_, 0, v_e_542_);
                    return v___x_546_;
                } else {
                    v___x_547_ = lean_st_ref_get(v___y_543_);
                    v_mctx_548_ = leanh::lean_ctor_get(v___x_547_, 0);
                    leanh::lean_inc_ref(v_mctx_548_);
                    leanh::lean_dec(v___x_547_);
                    v___x_549_ = l_Lean_instantiateMVarsCore(v_mctx_548_, v_e_542_);
                    v_fst_550_ = leanh::lean_ctor_get(v___x_549_, 0);
                    leanh::lean_inc(v_fst_550_);
                    v_snd_551_ = leanh::lean_ctor_get(v___x_549_, 1);
                    leanh::lean_inc(v_snd_551_);
                    leanh::lean_dec_ref(v___x_549_);
                    v___x_552_ = lean_st_ref_take(v___y_543_);
                    v_cache_553_ = leanh::lean_ctor_get(v___x_552_, 1);
                    v_zetaDeltaFVarIds_554_ = leanh::lean_ctor_get(v___x_552_, 2);
                    v_postponed_555_ = leanh::lean_ctor_get(v___x_552_, 3);
                    v_diag_556_ = leanh::lean_ctor_get(v___x_552_, 4);
                    v_isSharedCheck_565_ = (!leanh::lean_is_exclusive(v___x_552_)) as u8;
                    if v_isSharedCheck_565_ == 0 {
                        v_unused_566_ = leanh::lean_ctor_get(v___x_552_, 0);
                        leanh::lean_dec(v_unused_566_);
                        v___x_558_ = v___x_552_;
                        v_isShared_559_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_556_);
                        leanh::lean_inc(v_postponed_555_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_554_);
                        leanh::lean_inc(v_cache_553_);
                        leanh::lean_dec(v___x_552_);
                        v___x_558_ = leanh::lean_box(0);
                        v_isShared_559_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_559_ == 0 {
                    leanh::lean_ctor_set(v___x_558_, 0, v_snd_551_);
                    v___x_561_ = v___x_558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 0, v_snd_551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 1, v_cache_553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 2, v_zetaDeltaFVarIds_554_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 3, v_postponed_555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 4, v_diag_556_);
                    v___x_561_ = v_reuseFailAlloc_564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_562_ = lean_st_ref_set(v___y_543_, v___x_561_);
                v___x_563_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_563_, 0, v_fst_550_);
                return v___x_563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(
    mut v_e_567_: *mut leanh::LeanObject,
    mut v___y_568_: *mut leanh::LeanObject,
    mut v___y_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_570_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_567_, v___y_568_);
    leanh::lean_dec(v___y_568_);
    return v_res_570_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(
    mut v_e_571_: *mut leanh::LeanObject,
    mut v___y_572_: *mut leanh::LeanObject,
    mut v___y_573_: *mut leanh::LeanObject,
    mut v___y_574_: *mut leanh::LeanObject,
    mut v___y_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_577_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_571_, v___y_573_);
    return v___x_577_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(
    mut v_e_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(
        v_e_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_,
    );
    leanh::lean_dec(v___y_582_);
    leanh::lean_dec_ref(v___y_581_);
    leanh::lean_dec(v___y_580_);
    leanh::lean_dec_ref(v___y_579_);
    return v_res_584_;
}
pub unsafe fn l_Lean_Meta_kabstract(
    mut v_e_585_: *mut leanh::LeanObject,
    mut v_p_586_: *mut leanh::LeanObject,
    mut v_occs_587_: *mut leanh::LeanObject,
    mut v_a_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
    mut v_a_590_: *mut leanh::LeanObject,
    mut v_a_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_597_: u8 = 0;
    let mut v___y_599_: u8 = 0;
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_609_: u8 = 0;
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: u8 = 0;
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_593_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(
                    v_e_585_, v_a_589_,
                );
                v_a_594_ = leanh::lean_ctor_get(v___x_593_, 0);
                v_isSharedCheck_625_ = (!leanh::lean_is_exclusive(v___x_593_)) as u8;
                if v_isSharedCheck_625_ == 0 {
                    v___x_596_ = v___x_593_;
                    v_isShared_597_ = v_isSharedCheck_625_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_594_);
                    leanh::lean_dec(v___x_593_);
                    v___x_596_ = leanh::lean_box(0);
                    v_isShared_597_ = v_isSharedCheck_625_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_622_ = l_Lean_Expr_isFVar(v_p_586_);
                if v___x_622_ == 0 {
                    v___y_599_ = v___x_622_;
                    state = 2;
                    continue;
                } else {
                    v___x_623_ = leanh::lean_box(0);
                    leanh::lean_inc(v_occs_587_);
                    v___x_624_ = l_Lean_Meta_instBEqOccurrences_beq(v_occs_587_, v___x_623_);
                    v___y_599_ = v___x_624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_599_ == 0 {
                    leanh::lean_del_object(v___x_596_);
                    v___x_600_ = leanh::lean_unsigned_to_nat(1);
                    v___x_601_ = lean_st_mk_ref(v___x_600_);
                    leanh::lean_inc_ref(v_p_586_);
                    v___x_602_ = l_Lean_Expr_toHeadIndex(v_p_586_);
                    v___x_603_ = l_Lean_Expr_headNumArgs(v_p_586_);
                    v___x_604_ = leanh::lean_unsigned_to_nat(0);
                    v___x_605_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
                        v_p_586_,
                        v_occs_587_,
                        v___x_602_,
                        v___x_603_,
                        v_a_594_,
                        v___x_604_,
                        v___x_601_,
                        v_a_588_,
                        v_a_589_,
                        v_a_590_,
                        v_a_591_,
                    );
                    leanh::lean_dec(v___x_603_);
                    leanh::lean_dec(v___x_602_);
                    leanh::lean_dec(v_occs_587_);
                    if leanh::lean_obj_tag(v___x_605_) == 0 {
                        v_a_606_ = leanh::lean_ctor_get(v___x_605_, 0);
                        v_isSharedCheck_614_ = (!leanh::lean_is_exclusive(v___x_605_)) as u8;
                        if v_isSharedCheck_614_ == 0 {
                            v___x_608_ = v___x_605_;
                            v_isShared_609_ = v_isSharedCheck_614_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_606_);
                            leanh::lean_dec(v___x_605_);
                            v___x_608_ = leanh::lean_box(0);
                            v_isShared_609_ = v_isSharedCheck_614_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_601_);
                        return v___x_605_;
                    }
                } else {
                    leanh::lean_dec(v_occs_587_);
                    v___x_615_ = leanh::lean_unsigned_to_nat(1);
                    v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
                    v___x_617_ = lean_array_push(v___x_616_, v_p_586_);
                    v___x_618_ = lean_expr_abstract(v_a_594_, v___x_617_);
                    leanh::lean_dec_ref(v___x_617_);
                    leanh::lean_dec(v_a_594_);
                    if v_isShared_597_ == 0 {
                        leanh::lean_ctor_set(v___x_596_, 0, v___x_618_);
                        v___x_620_ = v___x_596_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_621_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
                        v___x_620_ = v_reuseFailAlloc_621_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_610_ = lean_st_ref_get(v___x_601_);
                leanh::lean_dec(v___x_601_);
                leanh::lean_dec(v___x_610_);
                if v_isShared_609_ == 0 {
                    v___x_612_ = v___x_608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
                    v___x_612_ = v_reuseFailAlloc_613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_612_;
            }
            5 => {
                return v___x_620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_kabstract___boxed(
    mut v_e_626_: *mut leanh::LeanObject,
    mut v_p_627_: *mut leanh::LeanObject,
    mut v_occs_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
    mut v_a_630_: *mut leanh::LeanObject,
    mut v_a_631_: *mut leanh::LeanObject,
    mut v_a_632_: *mut leanh::LeanObject,
    mut v_a_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Lean_Meta_kabstract(
        v_e_626_,
        v_p_627_,
        v_occs_628_,
        v_a_629_,
        v_a_630_,
        v_a_631_,
        v_a_632_,
    );
    leanh::lean_dec(v_a_632_);
    leanh::lean_dec_ref(v_a_631_);
    leanh::lean_dec(v_a_630_);
    leanh::lean_dec_ref(v_a_629_);
    return v_res_634_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_KAbstract(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_KAbstract(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_KAbstract(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_HeadIndex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KAbstract(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_KAbstract(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_KAbstract(builtin);
}