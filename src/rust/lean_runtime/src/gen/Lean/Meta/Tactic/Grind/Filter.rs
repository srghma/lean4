// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Filter
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_isFVar, l_Lean_instBEqFVarId_beq,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_alreadyInternalized___redArg,
    l_Lean_Meta_Grind_getGeneration___redArg, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_le;
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorIdx(mut v_x_375_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_375_) {
        0 => {
            let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
            v___x_376_ = lean_unsigned_to_nat(0);
            return v___x_376_;
        }
        1 => {
            let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
            v___x_377_ = lean_unsigned_to_nat(1);
            return v___x_377_;
        }
        2 => {
            let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
            v___x_378_ = lean_unsigned_to_nat(2);
            return v___x_378_;
        }
        3 => {
            let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
            v___x_379_ = lean_unsigned_to_nat(3);
            return v___x_379_;
        }
        4 => {
            let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
            v___x_380_ = lean_unsigned_to_nat(4);
            return v___x_380_;
        }
        5 => {
            let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
            v___x_381_ = lean_unsigned_to_nat(5);
            return v___x_381_;
        }
        _ => {
            let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
            v___x_382_ = lean_unsigned_to_nat(6);
            return v___x_382_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorIdx___boxed(
    mut v_x_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Lean_Meta_Grind_Filter_ctorIdx(v_x_383_);
    lean_dec(v_x_383_);
    return v_res_384_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorElim___redArg(
    mut v_t_385_: *mut LeanObject,
    mut v_k_386_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_385_) {
        0 => {
            return v_k_386_;
        }
        3 => {
            let mut v_pred_387_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
            v_pred_387_ = lean_ctor_get(v_t_385_, 0);
            lean_inc_ref(v_pred_387_);
            lean_dec_ref_known(v_t_385_, 1);
            v___x_388_ = lean_apply_1(v_k_386_, v_pred_387_);
            return v___x_388_;
        }
        4 => {
            let mut v_a_389_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_390_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
            v_a_389_ = lean_ctor_get(v_t_385_, 0);
            lean_inc(v_a_389_);
            v_b_390_ = lean_ctor_get(v_t_385_, 1);
            lean_inc(v_b_390_);
            lean_dec_ref_known(v_t_385_, 2);
            v___x_391_ = lean_apply_2(v_k_386_, v_a_389_, v_b_390_);
            return v___x_391_;
        }
        5 => {
            let mut v_a_392_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
            v_a_392_ = lean_ctor_get(v_t_385_, 0);
            lean_inc(v_a_392_);
            v_b_393_ = lean_ctor_get(v_t_385_, 1);
            lean_inc(v_b_393_);
            lean_dec_ref_known(v_t_385_, 2);
            v___x_394_ = lean_apply_2(v_k_386_, v_a_392_, v_b_393_);
            return v___x_394_;
        }
        _ => {
            let mut v_declName_395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
            v_declName_395_ = lean_ctor_get(v_t_385_, 0);
            lean_inc(v_declName_395_);
            lean_dec(v_t_385_);
            v___x_396_ = lean_apply_1(v_k_386_, v_declName_395_);
            return v___x_396_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorElim(
    mut v_motive_397_: *mut LeanObject,
    mut v_ctorIdx_398_: *mut LeanObject,
    mut v_t_399_: *mut LeanObject,
    mut v_h_400_: *mut LeanObject,
    mut v_k_401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_399_, v_k_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorElim___boxed(
    mut v_motive_403_: *mut LeanObject,
    mut v_ctorIdx_404_: *mut LeanObject,
    mut v_t_405_: *mut LeanObject,
    mut v_h_406_: *mut LeanObject,
    mut v_k_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_408_: *mut LeanObject = core::ptr::null_mut();
    v_res_408_ = l_Lean_Meta_Grind_Filter_ctorElim(
        v_motive_403_,
        v_ctorIdx_404_,
        v_t_405_,
        v_h_406_,
        v_k_407_,
    );
    lean_dec(v_ctorIdx_404_);
    return v_res_408_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_true_elim___redArg(
    mut v_t_409_: *mut LeanObject,
    mut v_true_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_409_, v_true_410_);
    return v___x_411_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_true_elim(
    mut v_motive_412_: *mut LeanObject,
    mut v_t_413_: *mut LeanObject,
    mut v_h_414_: *mut LeanObject,
    mut v_true_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_413_, v_true_415_);
    return v___x_416_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_const_elim___redArg(
    mut v_t_417_: *mut LeanObject,
    mut v_const_418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_417_, v_const_418_);
    return v___x_419_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_const_elim(
    mut v_motive_420_: *mut LeanObject,
    mut v_t_421_: *mut LeanObject,
    mut v_h_422_: *mut LeanObject,
    mut v_const_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_421_, v_const_423_);
    return v___x_424_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_fvar_elim___redArg(
    mut v_t_425_: *mut LeanObject,
    mut v_fvar_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_425_, v_fvar_426_);
    return v___x_427_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_fvar_elim(
    mut v_motive_428_: *mut LeanObject,
    mut v_t_429_: *mut LeanObject,
    mut v_h_430_: *mut LeanObject,
    mut v_fvar_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    v___x_432_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_429_, v_fvar_431_);
    return v___x_432_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_gen_elim___redArg(
    mut v_t_433_: *mut LeanObject,
    mut v_gen_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_433_, v_gen_434_);
    return v___x_435_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_gen_elim(
    mut v_motive_436_: *mut LeanObject,
    mut v_t_437_: *mut LeanObject,
    mut v_h_438_: *mut LeanObject,
    mut v_gen_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_437_, v_gen_439_);
    return v___x_440_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_or_elim___redArg(
    mut v_t_441_: *mut LeanObject,
    mut v_or_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_443_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_441_, v_or_442_);
    return v___x_443_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_or_elim(
    mut v_motive_444_: *mut LeanObject,
    mut v_t_445_: *mut LeanObject,
    mut v_h_446_: *mut LeanObject,
    mut v_or_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_445_, v_or_447_);
    return v___x_448_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_and_elim___redArg(
    mut v_t_449_: *mut LeanObject,
    mut v_and_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    v___x_451_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_449_, v_and_450_);
    return v___x_451_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_and_elim(
    mut v_motive_452_: *mut LeanObject,
    mut v_t_453_: *mut LeanObject,
    mut v_h_454_: *mut LeanObject,
    mut v_and_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_453_, v_and_455_);
    return v___x_456_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_not_elim___redArg(
    mut v_t_457_: *mut LeanObject,
    mut v_not_458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    v___x_459_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_457_, v_not_458_);
    return v___x_459_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_not_elim(
    mut v_motive_460_: *mut LeanObject,
    mut v_t_461_: *mut LeanObject,
    mut v_h_462_: *mut LeanObject,
    mut v_not_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    v___x_464_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_461_, v_not_463_);
    return v___x_464_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(
    mut v_e_468_: *mut LeanObject,
    mut v_a_469_: *mut LeanObject,
    mut v_a_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: u8 = 0;
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_479_: u8 = 0;
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u8 = 0;
    let mut v_arg_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: u8 = 0;
    let mut v_arg_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_507_: u8 = 0;
    let mut v_unused_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_509_: u8 = 0;
    let mut v_a_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_522_: u8 = 0;
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_472_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_468_, v_a_469_);
                if lean_obj_tag(v___x_472_) == 0 {
                    v_a_473_ = lean_ctor_get(v___x_472_, 0);
                    lean_inc(v_a_473_);
                    lean_dec_ref_known(v___x_472_, 1);
                    v___x_474_ = (lean_unbox(v_a_473_) as u8);
                    lean_dec(v_a_473_);
                    if v___x_474_ == 0 {
                        v___x_475_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_468_, v_a_470_);
                        if lean_obj_tag(v___x_475_) == 0 {
                            v_a_476_ = lean_ctor_get(v___x_475_, 0);
                            v_isSharedCheck_509_ = (!lean_is_exclusive(v___x_475_)) as u8;
                            if v_isSharedCheck_509_ == 0 {
                                v___x_478_ = v___x_475_;
                                v_isShared_479_ = v_isSharedCheck_509_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_476_);
                                lean_dec(v___x_475_);
                                v___x_478_ = lean_box(0);
                                v_isShared_479_ = v_isSharedCheck_509_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_510_ = lean_ctor_get(v___x_475_, 0);
                            v_isSharedCheck_517_ = (!lean_is_exclusive(v___x_475_)) as u8;
                            if v_isSharedCheck_517_ == 0 {
                                v___x_512_ = v___x_475_;
                                v_isShared_513_ = v_isSharedCheck_517_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_510_);
                                lean_dec(v___x_475_);
                                v___x_512_ = lean_box(0);
                                v_isShared_513_ = v_isSharedCheck_517_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_518_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_468_, v_a_469_);
                        lean_dec_ref(v_e_468_);
                        return v___x_518_;
                    }
                } else {
                    lean_dec_ref(v_e_468_);
                    v_a_519_ = lean_ctor_get(v___x_472_, 0);
                    v_isSharedCheck_526_ = (!lean_is_exclusive(v___x_472_)) as u8;
                    if v_isSharedCheck_526_ == 0 {
                        v___x_521_ = v___x_472_;
                        v_isShared_522_ = v_isSharedCheck_526_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_519_);
                        lean_dec(v___x_472_);
                        v___x_521_ = lean_box(0);
                        v_isShared_522_ = v_isSharedCheck_526_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_485_ = l_Lean_Expr_cleanupAnnotations(v_a_476_);
                v___x_486_ = l_Lean_Expr_isApp(v___x_485_);
                if v___x_486_ == 0 {
                    lean_dec_ref(v___x_485_);
                    state = 2;
                    continue;
                } else {
                    v_arg_487_ = lean_ctor_get(v___x_485_, 1);
                    lean_inc_ref(v_arg_487_);
                    v___x_488_ = l_Lean_Expr_appFnCleanup___redArg(v___x_485_);
                    v___x_489_ = l_Lean_Expr_isApp(v___x_488_);
                    if v___x_489_ == 0 {
                        lean_dec_ref(v___x_488_);
                        lean_dec_ref(v_arg_487_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_490_ = lean_ctor_get(v___x_488_, 1);
                        lean_inc_ref(v_arg_490_);
                        v___x_491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_488_);
                        v___x_492_ = l_Lean_Expr_isApp(v___x_491_);
                        if v___x_492_ == 0 {
                            lean_dec_ref(v___x_491_);
                            lean_dec_ref(v_arg_490_);
                            lean_dec_ref(v_arg_487_);
                            state = 2;
                            continue;
                        } else {
                            v___x_493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_491_);
                            v___x_494_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1;
                            v___x_495_ = l_Lean_Expr_isConstOf(v___x_493_, v___x_494_);
                            lean_dec_ref(v___x_493_);
                            if v___x_495_ == 0 {
                                lean_dec_ref(v_arg_490_);
                                lean_dec_ref(v_arg_487_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_478_);
                                v___x_496_ =
                                    l_Lean_Meta_Grind_getGeneration___redArg(v_arg_490_, v_a_469_);
                                lean_dec_ref(v_arg_490_);
                                if lean_obj_tag(v___x_496_) == 0 {
                                    v_a_497_ = lean_ctor_get(v___x_496_, 0);
                                    lean_inc(v_a_497_);
                                    lean_dec_ref_known(v___x_496_, 1);
                                    v___x_498_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                        v_arg_487_, v_a_469_,
                                    );
                                    lean_dec_ref(v_arg_487_);
                                    if lean_obj_tag(v___x_498_) == 0 {
                                        v_a_499_ = lean_ctor_get(v___x_498_, 0);
                                        lean_inc(v_a_499_);
                                        v___x_500_ = lean_nat_dec_le(v_a_497_, v_a_499_);
                                        lean_dec(v_a_499_);
                                        if v___x_500_ == 0 {
                                            v_isSharedCheck_507_ =
                                                (!lean_is_exclusive(v___x_498_)) as u8;
                                            if v_isSharedCheck_507_ == 0 {
                                                v_unused_508_ = lean_ctor_get(v___x_498_, 0);
                                                lean_dec(v_unused_508_);
                                                v___x_502_ = v___x_498_;
                                                v_isShared_503_ = v_isSharedCheck_507_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_dec(v___x_498_);
                                                v___x_502_ = lean_box(0);
                                                v_isShared_503_ = v_isSharedCheck_507_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_497_);
                                            return v___x_498_;
                                        }
                                    } else {
                                        lean_dec(v_a_497_);
                                        return v___x_498_;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_487_);
                                    return v___x_496_;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_481_ = lean_unsigned_to_nat(0);
                if v_isShared_479_ == 0 {
                    lean_ctor_set(v___x_478_, 0, v___x_481_);
                    v___x_483_ = v___x_478_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
                    v___x_483_ = v_reuseFailAlloc_484_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_483_;
            }
            4 => {
                if v_isShared_503_ == 0 {
                    lean_ctor_set(v___x_502_, 0, v_a_497_);
                    v___x_505_ = v___x_502_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_497_);
                    v___x_505_ = v_reuseFailAlloc_506_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_505_;
            }
            6 => {
                if v_isShared_513_ == 0 {
                    v___x_515_ = v___x_512_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
                    v___x_515_ = v_reuseFailAlloc_516_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_515_;
            }
            8 => {
                if v_isShared_522_ == 0 {
                    v___x_524_ = v___x_521_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
                    v___x_524_ = v_reuseFailAlloc_525_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___boxed(
    mut v_e_527_: *mut LeanObject,
    mut v_a_528_: *mut LeanObject,
    mut v_a_529_: *mut LeanObject,
    mut v_a_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_531_: *mut LeanObject = core::ptr::null_mut();
    v_res_531_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(
        v_e_527_, v_a_528_, v_a_529_,
    );
    lean_dec(v_a_529_);
    lean_dec(v_a_528_);
    return v_res_531_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(
    mut v_e_532_: *mut LeanObject,
    mut v_a_533_: *mut LeanObject,
    mut v_a_534_: *mut LeanObject,
    mut v_a_535_: *mut LeanObject,
    mut v_a_536_: *mut LeanObject,
    mut v_a_537_: *mut LeanObject,
    mut v_a_538_: *mut LeanObject,
    mut v_a_539_: *mut LeanObject,
    mut v_a_540_: *mut LeanObject,
    mut v_a_541_: *mut LeanObject,
    mut v_a_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(
        v_e_532_, v_a_533_, v_a_540_,
    );
    return v___x_544_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___boxed(
    mut v_e_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
    mut v_a_547_: *mut LeanObject,
    mut v_a_548_: *mut LeanObject,
    mut v_a_549_: *mut LeanObject,
    mut v_a_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
    mut v_a_552_: *mut LeanObject,
    mut v_a_553_: *mut LeanObject,
    mut v_a_554_: *mut LeanObject,
    mut v_a_555_: *mut LeanObject,
    mut v_a_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(
        v_e_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_,
        v_a_554_, v_a_555_,
    );
    lean_dec(v_a_555_);
    lean_dec_ref(v_a_554_);
    lean_dec(v_a_553_);
    lean_dec_ref(v_a_552_);
    lean_dec(v_a_551_);
    lean_dec_ref(v_a_550_);
    lean_dec(v_a_549_);
    lean_dec_ref(v_a_548_);
    lean_dec(v_a_547_);
    lean_dec(v_a_546_);
    return v_res_557_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(
    mut v_declName_558_: *mut LeanObject,
    mut v_e_559_: *mut LeanObject,
) -> u8 {
    let mut v___x_560_: u8 = 0;
    v___x_560_ = l_Lean_Expr_isConstOf(v_e_559_, v_declName_558_);
    return v___x_560_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed(
    mut v_declName_561_: *mut LeanObject,
    mut v_e_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_563_: u8 = 0;
    let mut v_r_564_: *mut LeanObject = core::ptr::null_mut();
    v_res_563_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(v_declName_561_, v_e_562_);
    lean_dec_ref(v_e_562_);
    lean_dec(v_declName_561_);
    v_r_564_ = lean_box((v_res_563_) as usize);
    return v_r_564_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(
    mut v_fvarId_565_: *mut LeanObject,
    mut v_e_566_: *mut LeanObject,
) -> u8 {
    let mut v___x_567_: u8 = 0;
    v___x_567_ = l_Lean_Expr_isFVar(v_e_566_);
    if v___x_567_ == 0 {
        return v___x_567_;
    } else {
        let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_569_: u8 = 0;
        v___x_568_ = l_Lean_Expr_fvarId_x21(v_e_566_);
        v___x_569_ = l_Lean_instBEqFVarId_beq(v___x_568_, v_fvarId_565_);
        lean_dec(v___x_568_);
        return v___x_569_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed(
    mut v_fvarId_570_: *mut LeanObject,
    mut v_e_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_572_: u8 = 0;
    let mut v_r_573_: *mut LeanObject = core::ptr::null_mut();
    v_res_572_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(v_fvarId_570_, v_e_571_);
    lean_dec_ref(v_e_571_);
    lean_dec(v_fvarId_570_);
    v_r_573_ = lean_box((v_res_572_) as usize);
    return v_r_573_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
    mut v_e_574_: *mut LeanObject,
    mut v_filter_575_: *mut LeanObject,
    mut v_a_576_: *mut LeanObject,
    mut v_a_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v___f_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___x_596_: u8 = 0;
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_601_: u8 = 0;
    let mut v_unused_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_603_: u8 = 0;
    let mut v_fvarId_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___f_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: u8 = 0;
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut v_unused_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_pred_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_636_: u8 = 0;
    let mut v_a_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v_a_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v_a_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v_a_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_663_: u8 = 0;
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_filter_575_) {
                0 => {
                    lean_dec_ref(v_e_574_);
                    v___x_579_ = 1;
                    v___x_580_ = lean_box((v___x_579_) as usize);
                    v___x_581_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_581_, 0, v___x_580_);
                    return v___x_581_;
                }
                1 => {
                    v_declName_582_ = lean_ctor_get(v_filter_575_, 0);
                    v_isSharedCheck_603_ = (!lean_is_exclusive(v_filter_575_)) as u8;
                    if v_isSharedCheck_603_ == 0 {
                        v___x_584_ = v_filter_575_;
                        v_isShared_585_ = v_isSharedCheck_603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_declName_582_);
                        lean_dec(v_filter_575_);
                        v___x_584_ = lean_box(0);
                        v_isShared_585_ = v_isSharedCheck_603_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_fvarId_604_ = lean_ctor_get(v_filter_575_, 0);
                    v_isSharedCheck_625_ = (!lean_is_exclusive(v_filter_575_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_606_ = v_filter_575_;
                        v_isShared_607_ = v_isSharedCheck_625_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_fvarId_604_);
                        lean_dec(v_filter_575_);
                        v___x_606_ = lean_box(0);
                        v_isShared_607_ = v_isSharedCheck_625_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_pred_626_ = lean_ctor_get(v_filter_575_, 0);
                    lean_inc_ref(v_pred_626_);
                    lean_dec_ref_known(v_filter_575_, 1);
                    v___x_627_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_574_, v_a_576_, v_a_577_);
                    if lean_obj_tag(v___x_627_) == 0 {
                        v_a_628_ = lean_ctor_get(v___x_627_, 0);
                        v_isSharedCheck_636_ = (!lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_636_ == 0 {
                            v___x_630_ = v___x_627_;
                            v_isShared_631_ = v_isSharedCheck_636_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_628_);
                            lean_dec(v___x_627_);
                            v___x_630_ = lean_box(0);
                            v_isShared_631_ = v_isSharedCheck_636_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_pred_626_);
                        v_a_637_ = lean_ctor_get(v___x_627_, 0);
                        v_isSharedCheck_644_ = (!lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_644_ == 0 {
                            v___x_639_ = v___x_627_;
                            v_isShared_640_ = v_isSharedCheck_644_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_637_);
                            lean_dec(v___x_627_);
                            v___x_639_ = lean_box(0);
                            v_isShared_640_ = v_isSharedCheck_644_;
                            state = 11;
                            continue;
                        }
                    }
                }
                4 => {
                    v_a_645_ = lean_ctor_get(v_filter_575_, 0);
                    lean_inc(v_a_645_);
                    v_b_646_ = lean_ctor_get(v_filter_575_, 1);
                    lean_inc(v_b_646_);
                    lean_dec_ref_known(v_filter_575_, 2);
                    lean_inc_ref(v_e_574_);
                    v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_574_, v_a_645_, v_a_576_, v_a_577_);
                    if lean_obj_tag(v___x_647_) == 0 {
                        v_a_648_ = lean_ctor_get(v___x_647_, 0);
                        lean_inc(v_a_648_);
                        v___x_649_ = (lean_unbox(v_a_648_) as u8);
                        lean_dec(v_a_648_);
                        if v___x_649_ == 0 {
                            lean_dec_ref_known(v___x_647_, 1);
                            v_filter_575_ = v_b_646_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_b_646_);
                            lean_dec_ref(v_e_574_);
                            return v___x_647_;
                        }
                    } else {
                        lean_dec(v_b_646_);
                        lean_dec_ref(v_e_574_);
                        return v___x_647_;
                    }
                }
                5 => {
                    v_a_651_ = lean_ctor_get(v_filter_575_, 0);
                    lean_inc(v_a_651_);
                    v_b_652_ = lean_ctor_get(v_filter_575_, 1);
                    lean_inc(v_b_652_);
                    lean_dec_ref_known(v_filter_575_, 2);
                    lean_inc_ref(v_e_574_);
                    v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_574_, v_a_651_, v_a_576_, v_a_577_);
                    if lean_obj_tag(v___x_653_) == 0 {
                        v_a_654_ = lean_ctor_get(v___x_653_, 0);
                        lean_inc(v_a_654_);
                        v___x_655_ = (lean_unbox(v_a_654_) as u8);
                        lean_dec(v_a_654_);
                        if v___x_655_ == 0 {
                            lean_dec(v_b_652_);
                            lean_dec_ref(v_e_574_);
                            return v___x_653_;
                        } else {
                            lean_dec_ref_known(v___x_653_, 1);
                            v_filter_575_ = v_b_652_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_b_652_);
                        lean_dec_ref(v_e_574_);
                        return v___x_653_;
                    }
                }
                _ => {
                    v_a_657_ = lean_ctor_get(v_filter_575_, 0);
                    lean_inc(v_a_657_);
                    lean_dec_ref_known(v_filter_575_, 1);
                    v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_574_, v_a_657_, v_a_576_, v_a_577_);
                    if lean_obj_tag(v___x_658_) == 0 {
                        v_a_659_ = lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_674_ = (!lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_674_ == 0 {
                            v___x_661_ = v___x_658_;
                            v_isShared_662_ = v_isSharedCheck_674_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_659_);
                            lean_dec(v___x_658_);
                            v___x_661_ = lean_box(0);
                            v_isShared_662_ = v_isSharedCheck_674_;
                            state = 13;
                            continue;
                        }
                    } else {
                        return v___x_658_;
                    }
                }
            },
            1 => {
                v___f_586_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_586_, 0, v_declName_582_);
                v___x_587_ = lean_find_expr(v___f_586_, v_e_574_);
                lean_dec_ref(v_e_574_);
                lean_dec_ref(v___f_586_);
                if lean_obj_tag(v___x_587_) == 0 {
                    v___x_588_ = 0;
                    v___x_589_ = lean_box((v___x_588_) as usize);
                    if v_isShared_585_ == 0 {
                        lean_ctor_set_tag(v___x_584_, 0);
                        lean_ctor_set(v___x_584_, 0, v___x_589_);
                        v___x_591_ = v___x_584_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
                        v___x_591_ = v_reuseFailAlloc_592_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_584_);
                    v_isSharedCheck_601_ = (!lean_is_exclusive(v___x_587_)) as u8;
                    if v_isSharedCheck_601_ == 0 {
                        v_unused_602_ = lean_ctor_get(v___x_587_, 0);
                        lean_dec(v_unused_602_);
                        v___x_594_ = v___x_587_;
                        v_isShared_595_ = v_isSharedCheck_601_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_587_);
                        v___x_594_ = lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_601_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_591_;
            }
            3 => {
                v___x_596_ = 1;
                v___x_597_ = lean_box((v___x_596_) as usize);
                if v_isShared_595_ == 0 {
                    lean_ctor_set_tag(v___x_594_, 0);
                    lean_ctor_set(v___x_594_, 0, v___x_597_);
                    v___x_599_ = v___x_594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
                    v___x_599_ = v_reuseFailAlloc_600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_599_;
            }
            5 => {
                v___f_608_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_608_, 0, v_fvarId_604_);
                v___x_609_ = lean_find_expr(v___f_608_, v_e_574_);
                lean_dec_ref(v_e_574_);
                lean_dec_ref(v___f_608_);
                if lean_obj_tag(v___x_609_) == 0 {
                    v___x_610_ = 0;
                    v___x_611_ = lean_box((v___x_610_) as usize);
                    if v_isShared_607_ == 0 {
                        lean_ctor_set_tag(v___x_606_, 0);
                        lean_ctor_set(v___x_606_, 0, v___x_611_);
                        v___x_613_ = v___x_606_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
                        v___x_613_ = v_reuseFailAlloc_614_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_606_);
                    v_isSharedCheck_623_ = (!lean_is_exclusive(v___x_609_)) as u8;
                    if v_isSharedCheck_623_ == 0 {
                        v_unused_624_ = lean_ctor_get(v___x_609_, 0);
                        lean_dec(v_unused_624_);
                        v___x_616_ = v___x_609_;
                        v_isShared_617_ = v_isSharedCheck_623_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_609_);
                        v___x_616_ = lean_box(0);
                        v_isShared_617_ = v_isSharedCheck_623_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_613_;
            }
            7 => {
                v___x_618_ = 1;
                v___x_619_ = lean_box((v___x_618_) as usize);
                if v_isShared_617_ == 0 {
                    lean_ctor_set_tag(v___x_616_, 0);
                    lean_ctor_set(v___x_616_, 0, v___x_619_);
                    v___x_621_ = v___x_616_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
                    v___x_621_ = v_reuseFailAlloc_622_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_621_;
            }
            9 => {
                v___x_632_ = lean_apply_1(v_pred_626_, v_a_628_);
                if v_isShared_631_ == 0 {
                    lean_ctor_set(v___x_630_, 0, v___x_632_);
                    v___x_634_ = v___x_630_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
                    v___x_634_ = v_reuseFailAlloc_635_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_634_;
            }
            11 => {
                if v_isShared_640_ == 0 {
                    v___x_642_ = v___x_639_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_642_;
            }
            13 => {
                v___x_663_ = (lean_unbox(v_a_659_) as u8);
                lean_dec(v_a_659_);
                if v___x_663_ == 0 {
                    v___x_664_ = 1;
                    v___x_665_ = lean_box((v___x_664_) as usize);
                    if v_isShared_662_ == 0 {
                        lean_ctor_set(v___x_661_, 0, v___x_665_);
                        v___x_667_ = v___x_661_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
                        v___x_667_ = v_reuseFailAlloc_668_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_669_ = 0;
                    v___x_670_ = lean_box((v___x_669_) as usize);
                    if v_isShared_662_ == 0 {
                        lean_ctor_set(v___x_661_, 0, v___x_670_);
                        v___x_672_ = v___x_661_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
                        v___x_672_ = v_reuseFailAlloc_673_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_667_;
            }
            15 => {
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___boxed(
    mut v_e_675_: *mut LeanObject,
    mut v_filter_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
    mut v_a_678_: *mut LeanObject,
    mut v_a_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ =
        l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
            v_e_675_,
            v_filter_676_,
            v_a_677_,
            v_a_678_,
        );
    lean_dec(v_a_678_);
    lean_dec(v_a_677_);
    return v_res_680_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(
    mut v_e_681_: *mut LeanObject,
    mut v_filter_682_: *mut LeanObject,
    mut v_a_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
    mut v_a_689_: *mut LeanObject,
    mut v_a_690_: *mut LeanObject,
    mut v_a_691_: *mut LeanObject,
    mut v_a_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    v___x_694_ =
        l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
            v_e_681_,
            v_filter_682_,
            v_a_683_,
            v_a_690_,
        );
    return v___x_694_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___boxed(
    mut v_e_695_: *mut LeanObject,
    mut v_filter_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
    mut v_a_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_708_: *mut LeanObject = core::ptr::null_mut();
    v_res_708_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(
        v_e_695_,
        v_filter_696_,
        v_a_697_,
        v_a_698_,
        v_a_699_,
        v_a_700_,
        v_a_701_,
        v_a_702_,
        v_a_703_,
        v_a_704_,
        v_a_705_,
        v_a_706_,
    );
    lean_dec(v_a_706_);
    lean_dec_ref(v_a_705_);
    lean_dec(v_a_704_);
    lean_dec_ref(v_a_703_);
    lean_dec(v_a_702_);
    lean_dec_ref(v_a_701_);
    lean_dec(v_a_700_);
    lean_dec_ref(v_a_699_);
    lean_dec(v_a_698_);
    lean_dec(v_a_697_);
    return v_res_708_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_eval___redArg(
    mut v_filter_709_: *mut LeanObject,
    mut v_e_710_: *mut LeanObject,
    mut v_a_711_: *mut LeanObject,
    mut v_a_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_714_ =
        l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
            v_e_710_,
            v_filter_709_,
            v_a_711_,
            v_a_712_,
        );
    return v___x_714_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_eval___redArg___boxed(
    mut v_filter_715_: *mut LeanObject,
    mut v_e_716_: *mut LeanObject,
    mut v_a_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ =
        l_Lean_Meta_Grind_Filter_eval___redArg(v_filter_715_, v_e_716_, v_a_717_, v_a_718_);
    lean_dec(v_a_718_);
    lean_dec(v_a_717_);
    return v_res_720_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_eval(
    mut v_filter_721_: *mut LeanObject,
    mut v_e_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ =
        l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
            v_e_722_,
            v_filter_721_,
            v_a_723_,
            v_a_730_,
        );
    return v___x_734_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_eval___boxed(
    mut v_filter_735_: *mut LeanObject,
    mut v_e_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
    mut v_a_745_: *mut LeanObject,
    mut v_a_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_748_: *mut LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Meta_Grind_Filter_eval(
        v_filter_735_,
        v_e_736_,
        v_a_737_,
        v_a_738_,
        v_a_739_,
        v_a_740_,
        v_a_741_,
        v_a_742_,
        v_a_743_,
        v_a_744_,
        v_a_745_,
        v_a_746_,
    );
    lean_dec(v_a_746_);
    lean_dec_ref(v_a_745_);
    lean_dec(v_a_744_);
    lean_dec_ref(v_a_743_);
    lean_dec(v_a_742_);
    lean_dec_ref(v_a_741_);
    lean_dec(v_a_740_);
    lean_dec_ref(v_a_739_);
    lean_dec(v_a_738_);
    lean_dec(v_a_737_);
    return v_res_748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Filter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Filter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
}
