// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Lean.HeadIndex Lean.Meta.Basic
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_abstract;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(
    mut v_p_318_: *mut LeanObject,
    mut v_occs_319_: *mut LeanObject,
    mut v_pHeadIdx_320_: *mut LeanObject,
    mut v_pNumArgs_321_: *mut LeanObject,
    mut v_e_322_: *mut LeanObject,
    mut v_offset_323_: *mut LeanObject,
    mut v_a_324_: *mut LeanObject,
    mut v_a_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
    mut v_a_327_: *mut LeanObject,
    mut v_a_328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_333_: u8 = 0;
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_341_: u8 = 0;
    let mut v___y_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_344_: u8 = 0;
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: usize = 0;
    let mut v___x_348_: usize = 0;
    let mut v___x_349_: u8 = 0;
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_356_: u8 = 0;
    let mut v___y_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_358_: u8 = 0;
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_369_: u8 = 0;
    let mut v___y_370_: u8 = 0;
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: u8 = 0;
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: usize = 0;
    let mut v___x_390_: usize = 0;
    let mut v___x_391_: u8 = 0;
    let mut v___x_392_: usize = 0;
    let mut v___x_393_: usize = 0;
    let mut v___x_394_: u8 = 0;
    let mut v_data_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_402_: usize = 0;
    let mut v___x_403_: usize = 0;
    let mut v___x_404_: u8 = 0;
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_412_: u8 = 0;
    let mut v_typeName_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_420_: u8 = 0;
    let mut v___x_421_: usize = 0;
    let mut v___x_422_: usize = 0;
    let mut v___x_423_: u8 = 0;
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_431_: u8 = 0;
    let mut v_declName_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_436_: u8 = 0;
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: usize = 0;
    let mut v___x_446_: usize = 0;
    let mut v___x_447_: u8 = 0;
    let mut v___x_448_: usize = 0;
    let mut v___x_449_: usize = 0;
    let mut v___x_450_: u8 = 0;
    let mut v_binderName_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_454_: u8 = 0;
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: usize = 0;
    let mut v___x_462_: usize = 0;
    let mut v___x_463_: u8 = 0;
    let mut v___x_464_: usize = 0;
    let mut v___x_465_: usize = 0;
    let mut v___x_466_: u8 = 0;
    let mut v_binderName_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_470_: u8 = 0;
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: usize = 0;
    let mut v___x_478_: usize = 0;
    let mut v___x_479_: u8 = 0;
    let mut v___x_480_: usize = 0;
    let mut v___x_481_: usize = 0;
    let mut v___x_482_: u8 = 0;
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u8 = 0;
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_509_: u8 = 0;
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_514_: u8 = 0;
    let mut v_unused_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut v_a_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_524_: u8 = 0;
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_484_ = l_Lean_Expr_hasLooseBVars(v_e_322_);
                if v___x_484_ == 0 {
                    lean_inc_ref(v_e_322_);
                    v___x_485_ = l_Lean_Expr_toHeadIndex(v_e_322_);
                    v___x_486_ = l_Lean_instBEqHeadIndex_beq(v___x_485_, v_pHeadIdx_320_);
                    lean_dec(v___x_485_);
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
                            lean_dec(v___x_487_);
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
                                lean_inc_ref(v_p_318_);
                                lean_inc_ref(v_e_322_);
                                v___x_490_ = l_Lean_Meta_isExprDefEq(
                                    v_e_322_, v_p_318_, v_a_325_, v_a_326_, v_a_327_, v_a_328_,
                                );
                                if lean_obj_tag(v___x_490_) == 0 {
                                    v_a_491_ = lean_ctor_get(v___x_490_, 0);
                                    v_isSharedCheck_520_ = (!lean_is_exclusive(v___x_490_)) as u8;
                                    if v_isSharedCheck_520_ == 0 {
                                        v___x_493_ = v___x_490_;
                                        v_isShared_494_ = v_isSharedCheck_520_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_491_);
                                        lean_dec(v___x_490_);
                                        v___x_493_ = lean_box(0);
                                        v_isShared_494_ = v_isSharedCheck_520_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_489_);
                                    lean_dec(v_offset_323_);
                                    lean_dec_ref(v_e_322_);
                                    lean_dec_ref(v_p_318_);
                                    v_a_521_ = lean_ctor_get(v___x_490_, 0);
                                    v_isSharedCheck_528_ = (!lean_is_exclusive(v___x_490_)) as u8;
                                    if v_isSharedCheck_528_ == 0 {
                                        v___x_523_ = v___x_490_;
                                        v_isShared_524_ = v_isSharedCheck_528_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_a_521_);
                                        lean_dec(v___x_490_);
                                        v___x_523_ = lean_box(0);
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
                    lean_dec_ref(v_e_322_);
                    v___x_334_ = l_Lean_Expr_app___override(v___y_331_, v___y_332_);
                    v___x_335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_335_, 0, v___x_334_);
                    return v___x_335_;
                } else {
                    lean_dec_ref(v___y_332_);
                    lean_dec_ref(v___y_331_);
                    v___x_336_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_336_, 0, v_e_322_);
                    return v___x_336_;
                }
            }
            2 => {
                if v___y_344_ == 0 {
                    lean_dec_ref(v___y_339_);
                    lean_dec_ref(v_e_322_);
                    v___x_345_ = l_Lean_Expr_letE___override(
                        v___y_340_, v___y_343_, v___y_338_, v___y_342_, v___y_341_,
                    );
                    v___x_346_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_346_, 0, v___x_345_);
                    return v___x_346_;
                } else {
                    v___x_347_ = lean_ptr_addr(v___y_339_);
                    lean_dec_ref(v___y_339_);
                    v___x_348_ = lean_ptr_addr(v___y_342_);
                    v___x_349_ = lean_usize_dec_eq(v___x_347_, v___x_348_);
                    if v___x_349_ == 0 {
                        lean_dec_ref(v_e_322_);
                        v___x_350_ = l_Lean_Expr_letE___override(
                            v___y_340_, v___y_343_, v___y_338_, v___y_342_, v___y_341_,
                        );
                        v___x_351_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_351_, 0, v___x_350_);
                        return v___x_351_;
                    } else {
                        lean_dec_ref(v___y_343_);
                        lean_dec_ref(v___y_342_);
                        lean_dec(v___y_340_);
                        lean_dec_ref(v___y_338_);
                        v___x_352_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_352_, 0, v_e_322_);
                        return v___x_352_;
                    }
                }
            }
            3 => {
                if v___y_358_ == 0 {
                    lean_dec_ref(v_e_322_);
                    v___x_359_ =
                        l_Lean_Expr_lam___override(v___y_354_, v___y_355_, v___y_357_, v___y_356_);
                    v___x_360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_360_, 0, v___x_359_);
                    return v___x_360_;
                } else {
                    v___x_361_ = l_Lean_instBEqBinderInfo_beq(v___y_356_, v___y_356_);
                    if v___x_361_ == 0 {
                        lean_dec_ref(v_e_322_);
                        v___x_362_ = l_Lean_Expr_lam___override(
                            v___y_354_, v___y_355_, v___y_357_, v___y_356_,
                        );
                        v___x_363_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_363_, 0, v___x_362_);
                        return v___x_363_;
                    } else {
                        lean_dec_ref(v___y_357_);
                        lean_dec_ref(v___y_355_);
                        lean_dec(v___y_354_);
                        v___x_364_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_364_, 0, v_e_322_);
                        return v___x_364_;
                    }
                }
            }
            4 => {
                if v___y_370_ == 0 {
                    lean_dec_ref(v_e_322_);
                    v___x_371_ = l_Lean_Expr_forallE___override(
                        v___y_368_, v___y_366_, v___y_367_, v___y_369_,
                    );
                    v___x_372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_372_, 0, v___x_371_);
                    return v___x_372_;
                } else {
                    v___x_373_ = l_Lean_instBEqBinderInfo_beq(v___y_369_, v___y_369_);
                    if v___x_373_ == 0 {
                        lean_dec_ref(v_e_322_);
                        v___x_374_ = l_Lean_Expr_forallE___override(
                            v___y_368_, v___y_366_, v___y_367_, v___y_369_,
                        );
                        v___x_375_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_375_, 0, v___x_374_);
                        return v___x_375_;
                    } else {
                        lean_dec(v___y_368_);
                        lean_dec_ref(v___y_367_);
                        lean_dec_ref(v___y_366_);
                        v___x_376_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_376_, 0, v_e_322_);
                        return v___x_376_;
                    }
                }
            }
            5 => match lean_obj_tag(v_e_322_) {
                5 => {
                    v_fn_383_ = lean_ctor_get(v_e_322_, 0);
                    v_arg_384_ = lean_ctor_get(v_e_322_, 1);
                    lean_inc(v_offset_323_);
                    lean_inc_ref(v_fn_383_);
                    lean_inc_ref(v_p_318_);
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
                    if lean_obj_tag(v___x_385_) == 0 {
                        v_a_386_ = lean_ctor_get(v___x_385_, 0);
                        lean_inc(v_a_386_);
                        lean_dec_ref_known(v___x_385_, 1);
                        lean_inc_ref(v_arg_384_);
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
                        if lean_obj_tag(v___x_387_) == 0 {
                            v_a_388_ = lean_ctor_get(v___x_387_, 0);
                            lean_inc(v_a_388_);
                            lean_dec_ref_known(v___x_387_, 1);
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
                            lean_dec(v_a_386_);
                            lean_dec_ref_known(v_e_322_, 2);
                            return v___x_387_;
                        }
                    } else {
                        lean_dec_ref_known(v_e_322_, 2);
                        lean_dec(v_offset_323_);
                        lean_dec_ref(v_p_318_);
                        return v___x_385_;
                    }
                }
                10 => {
                    v_data_395_ = lean_ctor_get(v_e_322_, 0);
                    v_expr_396_ = lean_ctor_get(v_e_322_, 1);
                    lean_inc_ref(v_expr_396_);
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
                    if lean_obj_tag(v___x_397_) == 0 {
                        v_a_398_ = lean_ctor_get(v___x_397_, 0);
                        v_isSharedCheck_412_ = (!lean_is_exclusive(v___x_397_)) as u8;
                        if v_isSharedCheck_412_ == 0 {
                            v___x_400_ = v___x_397_;
                            v_isShared_401_ = v_isSharedCheck_412_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_398_);
                            lean_dec(v___x_397_);
                            v___x_400_ = lean_box(0);
                            v_isShared_401_ = v_isSharedCheck_412_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_e_322_, 2);
                        return v___x_397_;
                    }
                }
                11 => {
                    v_typeName_413_ = lean_ctor_get(v_e_322_, 0);
                    v_idx_414_ = lean_ctor_get(v_e_322_, 1);
                    v_struct_415_ = lean_ctor_get(v_e_322_, 2);
                    lean_inc_ref(v_struct_415_);
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
                    if lean_obj_tag(v___x_416_) == 0 {
                        v_a_417_ = lean_ctor_get(v___x_416_, 0);
                        v_isSharedCheck_431_ = (!lean_is_exclusive(v___x_416_)) as u8;
                        if v_isSharedCheck_431_ == 0 {
                            v___x_419_ = v___x_416_;
                            v_isShared_420_ = v_isSharedCheck_431_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_417_);
                            lean_dec(v___x_416_);
                            v___x_419_ = lean_box(0);
                            v_isShared_420_ = v_isSharedCheck_431_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_e_322_, 3);
                        return v___x_416_;
                    }
                }
                8 => {
                    v_declName_432_ = lean_ctor_get(v_e_322_, 0);
                    v_type_433_ = lean_ctor_get(v_e_322_, 1);
                    v_value_434_ = lean_ctor_get(v_e_322_, 2);
                    v_body_435_ = lean_ctor_get(v_e_322_, 3);
                    v_nondep_436_ = lean_ctor_get_uint8(
                        v_e_322_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc(v_offset_323_);
                    lean_inc_ref(v_type_433_);
                    lean_inc_ref(v_p_318_);
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
                    if lean_obj_tag(v___x_437_) == 0 {
                        v_a_438_ = lean_ctor_get(v___x_437_, 0);
                        lean_inc(v_a_438_);
                        lean_dec_ref_known(v___x_437_, 1);
                        lean_inc(v_offset_323_);
                        lean_inc_ref(v_value_434_);
                        lean_inc_ref(v_p_318_);
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
                        if lean_obj_tag(v___x_439_) == 0 {
                            v_a_440_ = lean_ctor_get(v___x_439_, 0);
                            lean_inc(v_a_440_);
                            lean_dec_ref_known(v___x_439_, 1);
                            v___x_441_ = lean_unsigned_to_nat(1);
                            v___x_442_ = lean_nat_add(v_offset_323_, v___x_441_);
                            lean_dec(v_offset_323_);
                            lean_inc_ref(v_body_435_);
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
                            if lean_obj_tag(v___x_443_) == 0 {
                                v_a_444_ = lean_ctor_get(v___x_443_, 0);
                                lean_inc(v_a_444_);
                                lean_dec_ref_known(v___x_443_, 1);
                                v___x_445_ = lean_ptr_addr(v_type_433_);
                                v___x_446_ = lean_ptr_addr(v_a_438_);
                                v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
                                if v___x_447_ == 0 {
                                    lean_inc(v_declName_432_);
                                    lean_inc_ref(v_body_435_);
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
                                    lean_inc(v_declName_432_);
                                    lean_inc_ref(v_body_435_);
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
                                lean_dec(v_a_440_);
                                lean_dec(v_a_438_);
                                lean_dec_ref_known(v_e_322_, 4);
                                return v___x_443_;
                            }
                        } else {
                            lean_dec(v_a_438_);
                            lean_dec_ref_known(v_e_322_, 4);
                            lean_dec(v_offset_323_);
                            lean_dec_ref(v_p_318_);
                            return v___x_439_;
                        }
                    } else {
                        lean_dec_ref_known(v_e_322_, 4);
                        lean_dec(v_offset_323_);
                        lean_dec_ref(v_p_318_);
                        return v___x_437_;
                    }
                }
                6 => {
                    v_binderName_451_ = lean_ctor_get(v_e_322_, 0);
                    v_binderType_452_ = lean_ctor_get(v_e_322_, 1);
                    v_body_453_ = lean_ctor_get(v_e_322_, 2);
                    v_binderInfo_454_ = lean_ctor_get_uint8(
                        v_e_322_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_323_);
                    lean_inc_ref(v_binderType_452_);
                    lean_inc_ref(v_p_318_);
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
                    if lean_obj_tag(v___x_455_) == 0 {
                        v_a_456_ = lean_ctor_get(v___x_455_, 0);
                        lean_inc(v_a_456_);
                        lean_dec_ref_known(v___x_455_, 1);
                        v___x_457_ = lean_unsigned_to_nat(1);
                        v___x_458_ = lean_nat_add(v_offset_323_, v___x_457_);
                        lean_dec(v_offset_323_);
                        lean_inc_ref(v_body_453_);
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
                        if lean_obj_tag(v___x_459_) == 0 {
                            v_a_460_ = lean_ctor_get(v___x_459_, 0);
                            lean_inc(v_a_460_);
                            lean_dec_ref_known(v___x_459_, 1);
                            v___x_461_ = lean_ptr_addr(v_binderType_452_);
                            v___x_462_ = lean_ptr_addr(v_a_456_);
                            v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
                            if v___x_463_ == 0 {
                                lean_inc(v_binderName_451_);
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
                                lean_inc(v_binderName_451_);
                                v___y_354_ = v_binderName_451_;
                                v___y_355_ = v_a_456_;
                                v___y_356_ = v_binderInfo_454_;
                                v___y_357_ = v_a_460_;
                                v___y_358_ = v___x_466_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_456_);
                            lean_dec_ref_known(v_e_322_, 3);
                            return v___x_459_;
                        }
                    } else {
                        lean_dec_ref_known(v_e_322_, 3);
                        lean_dec(v_offset_323_);
                        lean_dec_ref(v_p_318_);
                        return v___x_455_;
                    }
                }
                7 => {
                    v_binderName_467_ = lean_ctor_get(v_e_322_, 0);
                    v_binderType_468_ = lean_ctor_get(v_e_322_, 1);
                    v_body_469_ = lean_ctor_get(v_e_322_, 2);
                    v_binderInfo_470_ = lean_ctor_get_uint8(
                        v_e_322_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_323_);
                    lean_inc_ref(v_binderType_468_);
                    lean_inc_ref(v_p_318_);
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
                    if lean_obj_tag(v___x_471_) == 0 {
                        v_a_472_ = lean_ctor_get(v___x_471_, 0);
                        lean_inc(v_a_472_);
                        lean_dec_ref_known(v___x_471_, 1);
                        v___x_473_ = lean_unsigned_to_nat(1);
                        v___x_474_ = lean_nat_add(v_offset_323_, v___x_473_);
                        lean_dec(v_offset_323_);
                        lean_inc_ref(v_body_469_);
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
                        if lean_obj_tag(v___x_475_) == 0 {
                            v_a_476_ = lean_ctor_get(v___x_475_, 0);
                            lean_inc(v_a_476_);
                            lean_dec_ref_known(v___x_475_, 1);
                            v___x_477_ = lean_ptr_addr(v_binderType_468_);
                            v___x_478_ = lean_ptr_addr(v_a_472_);
                            v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
                            if v___x_479_ == 0 {
                                lean_inc(v_binderName_467_);
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
                                lean_inc(v_binderName_467_);
                                v___y_366_ = v_a_472_;
                                v___y_367_ = v_a_476_;
                                v___y_368_ = v_binderName_467_;
                                v___y_369_ = v_binderInfo_470_;
                                v___y_370_ = v___x_482_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_472_);
                            lean_dec_ref_known(v_e_322_, 3);
                            return v___x_475_;
                        }
                    } else {
                        lean_dec_ref_known(v_e_322_, 3);
                        lean_dec(v_offset_323_);
                        lean_dec_ref(v_p_318_);
                        return v___x_471_;
                    }
                }
                _ => {
                    lean_dec(v_offset_323_);
                    lean_dec_ref(v_p_318_);
                    v___x_483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_483_, 0, v_e_322_);
                    return v___x_483_;
                }
            },
            6 => {
                v___x_402_ = lean_ptr_addr(v_expr_396_);
                v___x_403_ = lean_ptr_addr(v_a_398_);
                v___x_404_ = lean_usize_dec_eq(v___x_402_, v___x_403_);
                if v___x_404_ == 0 {
                    lean_inc(v_data_395_);
                    lean_dec_ref_known(v_e_322_, 2);
                    v___x_405_ = l_Lean_Expr_mdata___override(v_data_395_, v_a_398_);
                    if v_isShared_401_ == 0 {
                        lean_ctor_set(v___x_400_, 0, v___x_405_);
                        v___x_407_ = v___x_400_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
                        v___x_407_ = v_reuseFailAlloc_408_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_a_398_);
                    if v_isShared_401_ == 0 {
                        lean_ctor_set(v___x_400_, 0, v_e_322_);
                        v___x_410_ = v___x_400_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_411_, 0, v_e_322_);
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
                    lean_inc(v_idx_414_);
                    lean_inc(v_typeName_413_);
                    lean_dec_ref_known(v_e_322_, 3);
                    v___x_424_ = l_Lean_Expr_proj___override(v_typeName_413_, v_idx_414_, v_a_417_);
                    if v_isShared_420_ == 0 {
                        lean_ctor_set(v___x_419_, 0, v___x_424_);
                        v___x_426_ = v___x_419_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
                        v___x_426_ = v_reuseFailAlloc_427_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v_a_417_);
                    if v_isShared_420_ == 0 {
                        lean_ctor_set(v___x_419_, 0, v_e_322_);
                        v___x_429_ = v___x_419_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_430_, 0, v_e_322_);
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
                v___x_495_ = (lean_unbox(v_a_491_) as u8);
                lean_dec(v_a_491_);
                if v___x_495_ == 0 {
                    lean_del_object(v___x_493_);
                    lean_dec(v___x_489_);
                    v___y_378_ = v_a_324_;
                    v___y_379_ = v_a_325_;
                    v___y_380_ = v_a_326_;
                    v___y_381_ = v_a_327_;
                    v___y_382_ = v_a_328_;
                    state = 5;
                    continue;
                } else {
                    v___x_496_ = lean_st_ref_get(v_a_324_);
                    v___x_497_ = lean_unsigned_to_nat(1);
                    v___x_498_ = lean_nat_add(v___x_496_, v___x_497_);
                    v___x_499_ = lean_st_ref_set(v_a_324_, v___x_498_);
                    v___x_500_ = l_Lean_Meta_Occurrences_contains(v_occs_319_, v___x_496_);
                    lean_dec(v___x_496_);
                    if v___x_500_ == 0 {
                        lean_del_object(v___x_493_);
                        v___x_501_ = lean_st_ref_take(v_a_326_);
                        v_mctx_502_ = lean_ctor_get(v___x_489_, 0);
                        lean_inc_ref(v_mctx_502_);
                        lean_dec(v___x_489_);
                        v_cache_503_ = lean_ctor_get(v___x_501_, 1);
                        v_zetaDeltaFVarIds_504_ = lean_ctor_get(v___x_501_, 2);
                        v_postponed_505_ = lean_ctor_get(v___x_501_, 3);
                        v_diag_506_ = lean_ctor_get(v___x_501_, 4);
                        v_isSharedCheck_514_ = (!lean_is_exclusive(v___x_501_)) as u8;
                        if v_isSharedCheck_514_ == 0 {
                            v_unused_515_ = lean_ctor_get(v___x_501_, 0);
                            lean_dec(v_unused_515_);
                            v___x_508_ = v___x_501_;
                            v_isShared_509_ = v_isSharedCheck_514_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_diag_506_);
                            lean_inc(v_postponed_505_);
                            lean_inc(v_zetaDeltaFVarIds_504_);
                            lean_inc(v_cache_503_);
                            lean_dec(v___x_501_);
                            v___x_508_ = lean_box(0);
                            v_isShared_509_ = v_isSharedCheck_514_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_489_);
                        lean_dec_ref(v_e_322_);
                        lean_dec_ref(v_p_318_);
                        v___x_516_ = l_Lean_mkBVar(v_offset_323_);
                        if v_isShared_494_ == 0 {
                            lean_ctor_set(v___x_493_, 0, v___x_516_);
                            v___x_518_ = v___x_493_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
                            v___x_518_ = v_reuseFailAlloc_519_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if v_isShared_509_ == 0 {
                    lean_ctor_set(v___x_508_, 0, v_mctx_502_);
                    v___x_511_ = v___x_508_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_513_, 0, v_mctx_502_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 1, v_cache_503_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 2, v_zetaDeltaFVarIds_504_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 3, v_postponed_505_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 4, v_diag_506_);
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
                    v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
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
    mut v_p_529_: *mut LeanObject,
    mut v_occs_530_: *mut LeanObject,
    mut v_pHeadIdx_531_: *mut LeanObject,
    mut v_pNumArgs_532_: *mut LeanObject,
    mut v_e_533_: *mut LeanObject,
    mut v_offset_534_: *mut LeanObject,
    mut v_a_535_: *mut LeanObject,
    mut v_a_536_: *mut LeanObject,
    mut v_a_537_: *mut LeanObject,
    mut v_a_538_: *mut LeanObject,
    mut v_a_539_: *mut LeanObject,
    mut v_a_540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_541_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_539_);
    lean_dec_ref(v_a_538_);
    lean_dec(v_a_537_);
    lean_dec_ref(v_a_536_);
    lean_dec(v_a_535_);
    lean_dec(v_pNumArgs_532_);
    lean_dec(v_pHeadIdx_531_);
    lean_dec(v_occs_530_);
    return v_res_541_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(
    mut v_e_542_: *mut LeanObject,
    mut v___y_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_unused_566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_545_ = l_Lean_Expr_hasMVar(v_e_542_);
                if v___x_545_ == 0 {
                    v___x_546_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_546_, 0, v_e_542_);
                    return v___x_546_;
                } else {
                    v___x_547_ = lean_st_ref_get(v___y_543_);
                    v_mctx_548_ = lean_ctor_get(v___x_547_, 0);
                    lean_inc_ref(v_mctx_548_);
                    lean_dec(v___x_547_);
                    v___x_549_ = l_Lean_instantiateMVarsCore(v_mctx_548_, v_e_542_);
                    v_fst_550_ = lean_ctor_get(v___x_549_, 0);
                    lean_inc(v_fst_550_);
                    v_snd_551_ = lean_ctor_get(v___x_549_, 1);
                    lean_inc(v_snd_551_);
                    lean_dec_ref(v___x_549_);
                    v___x_552_ = lean_st_ref_take(v___y_543_);
                    v_cache_553_ = lean_ctor_get(v___x_552_, 1);
                    v_zetaDeltaFVarIds_554_ = lean_ctor_get(v___x_552_, 2);
                    v_postponed_555_ = lean_ctor_get(v___x_552_, 3);
                    v_diag_556_ = lean_ctor_get(v___x_552_, 4);
                    v_isSharedCheck_565_ = (!lean_is_exclusive(v___x_552_)) as u8;
                    if v_isSharedCheck_565_ == 0 {
                        v_unused_566_ = lean_ctor_get(v___x_552_, 0);
                        lean_dec(v_unused_566_);
                        v___x_558_ = v___x_552_;
                        v_isShared_559_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_556_);
                        lean_inc(v_postponed_555_);
                        lean_inc(v_zetaDeltaFVarIds_554_);
                        lean_inc(v_cache_553_);
                        lean_dec(v___x_552_);
                        v___x_558_ = lean_box(0);
                        v_isShared_559_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_559_ == 0 {
                    lean_ctor_set(v___x_558_, 0, v_snd_551_);
                    v___x_561_ = v___x_558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_564_, 0, v_snd_551_);
                    lean_ctor_set(v_reuseFailAlloc_564_, 1, v_cache_553_);
                    lean_ctor_set(v_reuseFailAlloc_564_, 2, v_zetaDeltaFVarIds_554_);
                    lean_ctor_set(v_reuseFailAlloc_564_, 3, v_postponed_555_);
                    lean_ctor_set(v_reuseFailAlloc_564_, 4, v_diag_556_);
                    v___x_561_ = v_reuseFailAlloc_564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_562_ = lean_st_ref_set(v___y_543_, v___x_561_);
                v___x_563_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_563_, 0, v_fst_550_);
                return v___x_563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(
    mut v_e_567_: *mut LeanObject,
    mut v___y_568_: *mut LeanObject,
    mut v___y_569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_570_: *mut LeanObject = core::ptr::null_mut();
    v_res_570_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_567_, v___y_568_);
    lean_dec(v___y_568_);
    return v_res_570_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(
    mut v_e_571_: *mut LeanObject,
    mut v___y_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
    mut v___y_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    v___x_577_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_571_, v___y_573_);
    return v___x_577_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(
    mut v_e_578_: *mut LeanObject,
    mut v___y_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(
        v_e_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_,
    );
    lean_dec(v___y_582_);
    lean_dec_ref(v___y_581_);
    lean_dec(v___y_580_);
    lean_dec_ref(v___y_579_);
    return v_res_584_;
}
pub unsafe fn l_Lean_Meta_kabstract(
    mut v_e_585_: *mut LeanObject,
    mut v_p_586_: *mut LeanObject,
    mut v_occs_587_: *mut LeanObject,
    mut v_a_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
    mut v_a_590_: *mut LeanObject,
    mut v_a_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_597_: u8 = 0;
    let mut v___y_599_: u8 = 0;
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_609_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: u8 = 0;
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_593_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(
                    v_e_585_, v_a_589_,
                );
                v_a_594_ = lean_ctor_get(v___x_593_, 0);
                v_isSharedCheck_625_ = (!lean_is_exclusive(v___x_593_)) as u8;
                if v_isSharedCheck_625_ == 0 {
                    v___x_596_ = v___x_593_;
                    v_isShared_597_ = v_isSharedCheck_625_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_594_);
                    lean_dec(v___x_593_);
                    v___x_596_ = lean_box(0);
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
                    v___x_623_ = lean_box(0);
                    lean_inc(v_occs_587_);
                    v___x_624_ = l_Lean_Meta_instBEqOccurrences_beq(v_occs_587_, v___x_623_);
                    v___y_599_ = v___x_624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_599_ == 0 {
                    lean_del_object(v___x_596_);
                    v___x_600_ = lean_unsigned_to_nat(1);
                    v___x_601_ = lean_st_mk_ref(v___x_600_);
                    lean_inc_ref(v_p_586_);
                    v___x_602_ = l_Lean_Expr_toHeadIndex(v_p_586_);
                    v___x_603_ = l_Lean_Expr_headNumArgs(v_p_586_);
                    v___x_604_ = lean_unsigned_to_nat(0);
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
                    lean_dec(v___x_603_);
                    lean_dec(v___x_602_);
                    lean_dec(v_occs_587_);
                    if lean_obj_tag(v___x_605_) == 0 {
                        v_a_606_ = lean_ctor_get(v___x_605_, 0);
                        v_isSharedCheck_614_ = (!lean_is_exclusive(v___x_605_)) as u8;
                        if v_isSharedCheck_614_ == 0 {
                            v___x_608_ = v___x_605_;
                            v_isShared_609_ = v_isSharedCheck_614_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_606_);
                            lean_dec(v___x_605_);
                            v___x_608_ = lean_box(0);
                            v_isShared_609_ = v_isSharedCheck_614_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_601_);
                        return v___x_605_;
                    }
                } else {
                    lean_dec(v_occs_587_);
                    v___x_615_ = lean_unsigned_to_nat(1);
                    v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
                    v___x_617_ = lean_array_push(v___x_616_, v_p_586_);
                    v___x_618_ = lean_expr_abstract(v_a_594_, v___x_617_);
                    lean_dec_ref(v___x_617_);
                    lean_dec(v_a_594_);
                    if v_isShared_597_ == 0 {
                        lean_ctor_set(v___x_596_, 0, v___x_618_);
                        v___x_620_ = v___x_596_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
                        v___x_620_ = v_reuseFailAlloc_621_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_610_ = lean_st_ref_get(v___x_601_);
                lean_dec(v___x_601_);
                lean_dec(v___x_610_);
                if v_isShared_609_ == 0 {
                    v___x_612_ = v___x_608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
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
    mut v_e_626_: *mut LeanObject,
    mut v_p_627_: *mut LeanObject,
    mut v_occs_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
    mut v_a_630_: *mut LeanObject,
    mut v_a_631_: *mut LeanObject,
    mut v_a_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_634_: *mut LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Lean_Meta_kabstract(
        v_e_626_,
        v_p_627_,
        v_occs_628_,
        v_a_629_,
        v_a_630_,
        v_a_631_,
        v_a_632_,
    );
    lean_dec(v_a_632_);
    lean_dec_ref(v_a_631_);
    lean_dec(v_a_630_);
    lean_dec_ref(v_a_629_);
    return v_res_634_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_KAbstract(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_KAbstract(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_KAbstract(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_HeadIndex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KAbstract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_KAbstract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_KAbstract(builtin);
}
