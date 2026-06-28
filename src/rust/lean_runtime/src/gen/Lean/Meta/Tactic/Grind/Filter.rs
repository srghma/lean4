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
pub static l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorIdx(
    mut v_x_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_375_) {
        0 => {
            let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_376_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_376_;
        }
        1 => {
            let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_377_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_377_;
        }
        2 => {
            let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_378_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_378_;
        }
        3 => {
            let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_379_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_379_;
        }
        4 => {
            let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_380_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_380_;
        }
        5 => {
            let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_381_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_381_;
        }
        _ => {
            let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_382_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_382_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorIdx___boxed(
    mut v_x_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Lean_Meta_Grind_Filter_ctorIdx(v_x_383_);
    crate::leanh::lean_dec(v_x_383_);
    return v_res_384_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorElim___redArg(
    mut v_t_385_: *mut crate::leanh::LeanObject,
    mut v_k_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_385_) {
        0 => {
            return v_k_386_;
        }
        3 => {
            let mut v_pred_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pred_387_ = crate::leanh::lean_ctor_get(v_t_385_, 0);
            crate::leanh::lean_inc_ref(v_pred_387_);
            crate::leanh::lean_dec_ref_known(v_t_385_, 1);
            v___x_388_ = crate::leanh::lean_apply_1(v_k_386_, v_pred_387_);
            return v___x_388_;
        }
        4 => {
            let mut v_a_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_389_ = crate::leanh::lean_ctor_get(v_t_385_, 0);
            crate::leanh::lean_inc(v_a_389_);
            v_b_390_ = crate::leanh::lean_ctor_get(v_t_385_, 1);
            crate::leanh::lean_inc(v_b_390_);
            crate::leanh::lean_dec_ref_known(v_t_385_, 2);
            v___x_391_ = crate::leanh::lean_apply_2(v_k_386_, v_a_389_, v_b_390_);
            return v___x_391_;
        }
        5 => {
            let mut v_a_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_392_ = crate::leanh::lean_ctor_get(v_t_385_, 0);
            crate::leanh::lean_inc(v_a_392_);
            v_b_393_ = crate::leanh::lean_ctor_get(v_t_385_, 1);
            crate::leanh::lean_inc(v_b_393_);
            crate::leanh::lean_dec_ref_known(v_t_385_, 2);
            v___x_394_ = crate::leanh::lean_apply_2(v_k_386_, v_a_392_, v_b_393_);
            return v___x_394_;
        }
        _ => {
            let mut v_declName_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_declName_395_ = crate::leanh::lean_ctor_get(v_t_385_, 0);
            crate::leanh::lean_inc(v_declName_395_);
            crate::leanh::lean_dec(v_t_385_);
            v___x_396_ = crate::leanh::lean_apply_1(v_k_386_, v_declName_395_);
            return v___x_396_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorElim(
    mut v_motive_397_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_398_: *mut crate::leanh::LeanObject,
    mut v_t_399_: *mut crate::leanh::LeanObject,
    mut v_h_400_: *mut crate::leanh::LeanObject,
    mut v_k_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_399_, v_k_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_ctorElim___boxed(
    mut v_motive_403_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_404_: *mut crate::leanh::LeanObject,
    mut v_t_405_: *mut crate::leanh::LeanObject,
    mut v_h_406_: *mut crate::leanh::LeanObject,
    mut v_k_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_408_ = l_Lean_Meta_Grind_Filter_ctorElim(
        v_motive_403_,
        v_ctorIdx_404_,
        v_t_405_,
        v_h_406_,
        v_k_407_,
    );
    crate::leanh::lean_dec(v_ctorIdx_404_);
    return v_res_408_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_true_elim___redArg(
    mut v_t_409_: *mut crate::leanh::LeanObject,
    mut v_true_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_409_, v_true_410_);
    return v___x_411_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_true_elim(
    mut v_motive_412_: *mut crate::leanh::LeanObject,
    mut v_t_413_: *mut crate::leanh::LeanObject,
    mut v_h_414_: *mut crate::leanh::LeanObject,
    mut v_true_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_413_, v_true_415_);
    return v___x_416_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_const_elim___redArg(
    mut v_t_417_: *mut crate::leanh::LeanObject,
    mut v_const_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_417_, v_const_418_);
    return v___x_419_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_const_elim(
    mut v_motive_420_: *mut crate::leanh::LeanObject,
    mut v_t_421_: *mut crate::leanh::LeanObject,
    mut v_h_422_: *mut crate::leanh::LeanObject,
    mut v_const_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_421_, v_const_423_);
    return v___x_424_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_fvar_elim___redArg(
    mut v_t_425_: *mut crate::leanh::LeanObject,
    mut v_fvar_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_425_, v_fvar_426_);
    return v___x_427_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_fvar_elim(
    mut v_motive_428_: *mut crate::leanh::LeanObject,
    mut v_t_429_: *mut crate::leanh::LeanObject,
    mut v_h_430_: *mut crate::leanh::LeanObject,
    mut v_fvar_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_429_, v_fvar_431_);
    return v___x_432_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_gen_elim___redArg(
    mut v_t_433_: *mut crate::leanh::LeanObject,
    mut v_gen_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_433_, v_gen_434_);
    return v___x_435_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_gen_elim(
    mut v_motive_436_: *mut crate::leanh::LeanObject,
    mut v_t_437_: *mut crate::leanh::LeanObject,
    mut v_h_438_: *mut crate::leanh::LeanObject,
    mut v_gen_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_437_, v_gen_439_);
    return v___x_440_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_or_elim___redArg(
    mut v_t_441_: *mut crate::leanh::LeanObject,
    mut v_or_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_441_, v_or_442_);
    return v___x_443_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_or_elim(
    mut v_motive_444_: *mut crate::leanh::LeanObject,
    mut v_t_445_: *mut crate::leanh::LeanObject,
    mut v_h_446_: *mut crate::leanh::LeanObject,
    mut v_or_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_445_, v_or_447_);
    return v___x_448_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_and_elim___redArg(
    mut v_t_449_: *mut crate::leanh::LeanObject,
    mut v_and_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_451_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_449_, v_and_450_);
    return v___x_451_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_and_elim(
    mut v_motive_452_: *mut crate::leanh::LeanObject,
    mut v_t_453_: *mut crate::leanh::LeanObject,
    mut v_h_454_: *mut crate::leanh::LeanObject,
    mut v_and_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_453_, v_and_455_);
    return v___x_456_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_not_elim___redArg(
    mut v_t_457_: *mut crate::leanh::LeanObject,
    mut v_not_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_457_, v_not_458_);
    return v___x_459_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_not_elim(
    mut v_motive_460_: *mut crate::leanh::LeanObject,
    mut v_t_461_: *mut crate::leanh::LeanObject,
    mut v_h_462_: *mut crate::leanh::LeanObject,
    mut v_not_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = l_Lean_Meta_Grind_Filter_ctorElim___redArg(v_t_461_, v_not_463_);
    return v___x_464_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(
    mut v_e_468_: *mut crate::leanh::LeanObject,
    mut v_a_469_: *mut crate::leanh::LeanObject,
    mut v_a_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: u8 = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_479_: u8 = 0;
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u8 = 0;
    let mut v_arg_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: u8 = 0;
    let mut v_arg_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_507_: u8 = 0;
    let mut v_unused_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_509_: u8 = 0;
    let mut v_a_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_522_: u8 = 0;
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_472_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_468_, v_a_469_);
                if crate::leanh::lean_obj_tag(v___x_472_) == 0 {
                    v_a_473_ = crate::leanh::lean_ctor_get(v___x_472_, 0);
                    crate::leanh::lean_inc(v_a_473_);
                    crate::leanh::lean_dec_ref_known(v___x_472_, 1);
                    v___x_474_ = (crate::leanh::lean_unbox(v_a_473_) as u8);
                    crate::leanh::lean_dec(v_a_473_);
                    if v___x_474_ == 0 {
                        v___x_475_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_468_, v_a_470_);
                        if crate::leanh::lean_obj_tag(v___x_475_) == 0 {
                            v_a_476_ = crate::leanh::lean_ctor_get(v___x_475_, 0);
                            v_isSharedCheck_509_ =
                                (!crate::leanh::lean_is_exclusive(v___x_475_)) as u8;
                            if v_isSharedCheck_509_ == 0 {
                                v___x_478_ = v___x_475_;
                                v_isShared_479_ = v_isSharedCheck_509_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_476_);
                                crate::leanh::lean_dec(v___x_475_);
                                v___x_478_ = crate::leanh::lean_box(0);
                                v_isShared_479_ = v_isSharedCheck_509_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_510_ = crate::leanh::lean_ctor_get(v___x_475_, 0);
                            v_isSharedCheck_517_ =
                                (!crate::leanh::lean_is_exclusive(v___x_475_)) as u8;
                            if v_isSharedCheck_517_ == 0 {
                                v___x_512_ = v___x_475_;
                                v_isShared_513_ = v_isSharedCheck_517_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_510_);
                                crate::leanh::lean_dec(v___x_475_);
                                v___x_512_ = crate::leanh::lean_box(0);
                                v_isShared_513_ = v_isSharedCheck_517_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_518_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_468_, v_a_469_);
                        crate::leanh::lean_dec_ref(v_e_468_);
                        return v___x_518_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_468_);
                    v_a_519_ = crate::leanh::lean_ctor_get(v___x_472_, 0);
                    v_isSharedCheck_526_ = (!crate::leanh::lean_is_exclusive(v___x_472_)) as u8;
                    if v_isSharedCheck_526_ == 0 {
                        v___x_521_ = v___x_472_;
                        v_isShared_522_ = v_isSharedCheck_526_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_519_);
                        crate::leanh::lean_dec(v___x_472_);
                        v___x_521_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec_ref(v___x_485_);
                    state = 2;
                    continue;
                } else {
                    v_arg_487_ = crate::leanh::lean_ctor_get(v___x_485_, 1);
                    crate::leanh::lean_inc_ref(v_arg_487_);
                    v___x_488_ = l_Lean_Expr_appFnCleanup___redArg(v___x_485_);
                    v___x_489_ = l_Lean_Expr_isApp(v___x_488_);
                    if v___x_489_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_488_);
                        crate::leanh::lean_dec_ref(v_arg_487_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_490_ = crate::leanh::lean_ctor_get(v___x_488_, 1);
                        crate::leanh::lean_inc_ref(v_arg_490_);
                        v___x_491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_488_);
                        v___x_492_ = l_Lean_Expr_isApp(v___x_491_);
                        if v___x_492_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_491_);
                            crate::leanh::lean_dec_ref(v_arg_490_);
                            crate::leanh::lean_dec_ref(v_arg_487_);
                            state = 2;
                            continue;
                        } else {
                            v___x_493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_491_);
                            v___x_494_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg___closed__1;
                            v___x_495_ = l_Lean_Expr_isConstOf(v___x_493_, v___x_494_);
                            crate::leanh::lean_dec_ref(v___x_493_);
                            if v___x_495_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_490_);
                                crate::leanh::lean_dec_ref(v_arg_487_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_478_);
                                v___x_496_ =
                                    l_Lean_Meta_Grind_getGeneration___redArg(v_arg_490_, v_a_469_);
                                crate::leanh::lean_dec_ref(v_arg_490_);
                                if crate::leanh::lean_obj_tag(v___x_496_) == 0 {
                                    v_a_497_ = crate::leanh::lean_ctor_get(v___x_496_, 0);
                                    crate::leanh::lean_inc(v_a_497_);
                                    crate::leanh::lean_dec_ref_known(v___x_496_, 1);
                                    v___x_498_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                        v_arg_487_, v_a_469_,
                                    );
                                    crate::leanh::lean_dec_ref(v_arg_487_);
                                    if crate::leanh::lean_obj_tag(v___x_498_) == 0 {
                                        v_a_499_ = crate::leanh::lean_ctor_get(v___x_498_, 0);
                                        crate::leanh::lean_inc(v_a_499_);
                                        v___x_500_ = lean_nat_dec_le(v_a_497_, v_a_499_);
                                        crate::leanh::lean_dec(v_a_499_);
                                        if v___x_500_ == 0 {
                                            v_isSharedCheck_507_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_498_))
                                                    as u8;
                                            if v_isSharedCheck_507_ == 0 {
                                                v_unused_508_ =
                                                    crate::leanh::lean_ctor_get(v___x_498_, 0);
                                                crate::leanh::lean_dec(v_unused_508_);
                                                v___x_502_ = v___x_498_;
                                                v_isShared_503_ = v_isSharedCheck_507_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_498_);
                                                v___x_502_ = crate::leanh::lean_box(0);
                                                v_isShared_503_ = v_isSharedCheck_507_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_497_);
                                            return v___x_498_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_497_);
                                        return v___x_498_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_487_);
                                    return v___x_496_;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_481_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_478_, 0, v___x_481_);
                    v___x_483_ = v___x_478_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
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
                    crate::leanh::lean_ctor_set(v___x_502_, 0, v_a_497_);
                    v___x_505_ = v___x_502_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_497_);
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
                    v_reuseFailAlloc_516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
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
                    v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
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
    mut v_e_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
    mut v_a_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(
        v_e_527_, v_a_528_, v_a_529_,
    );
    crate::leanh::lean_dec(v_a_529_);
    crate::leanh::lean_dec(v_a_528_);
    return v_res_531_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(
    mut v_e_532_: *mut crate::leanh::LeanObject,
    mut v_a_533_: *mut crate::leanh::LeanObject,
    mut v_a_534_: *mut crate::leanh::LeanObject,
    mut v_a_535_: *mut crate::leanh::LeanObject,
    mut v_a_536_: *mut crate::leanh::LeanObject,
    mut v_a_537_: *mut crate::leanh::LeanObject,
    mut v_a_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
    mut v_a_540_: *mut crate::leanh::LeanObject,
    mut v_a_541_: *mut crate::leanh::LeanObject,
    mut v_a_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(
        v_e_532_, v_a_533_, v_a_540_,
    );
    return v___x_544_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___boxed(
    mut v_e_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_a_548_: *mut crate::leanh::LeanObject,
    mut v_a_549_: *mut crate::leanh::LeanObject,
    mut v_a_550_: *mut crate::leanh::LeanObject,
    mut v_a_551_: *mut crate::leanh::LeanObject,
    mut v_a_552_: *mut crate::leanh::LeanObject,
    mut v_a_553_: *mut crate::leanh::LeanObject,
    mut v_a_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
    mut v_a_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_557_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen(
        v_e_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_,
        v_a_554_, v_a_555_,
    );
    crate::leanh::lean_dec(v_a_555_);
    crate::leanh::lean_dec_ref(v_a_554_);
    crate::leanh::lean_dec(v_a_553_);
    crate::leanh::lean_dec_ref(v_a_552_);
    crate::leanh::lean_dec(v_a_551_);
    crate::leanh::lean_dec_ref(v_a_550_);
    crate::leanh::lean_dec(v_a_549_);
    crate::leanh::lean_dec_ref(v_a_548_);
    crate::leanh::lean_dec(v_a_547_);
    crate::leanh::lean_dec(v_a_546_);
    return v_res_557_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(
    mut v_declName_558_: *mut crate::leanh::LeanObject,
    mut v_e_559_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_560_: u8 = 0;
    v___x_560_ = l_Lean_Expr_isConstOf(v_e_559_, v_declName_558_);
    return v___x_560_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed(
    mut v_declName_561_: *mut crate::leanh::LeanObject,
    mut v_e_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_563_: u8 = 0;
    let mut v_r_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0(v_declName_561_, v_e_562_);
    crate::leanh::lean_dec_ref(v_e_562_);
    crate::leanh::lean_dec(v_declName_561_);
    v_r_564_ = crate::leanh::lean_box((v_res_563_) as usize);
    return v_r_564_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(
    mut v_fvarId_565_: *mut crate::leanh::LeanObject,
    mut v_e_566_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_567_: u8 = 0;
    v___x_567_ = l_Lean_Expr_isFVar(v_e_566_);
    if v___x_567_ == 0 {
        return v___x_567_;
    } else {
        let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_569_: u8 = 0;
        v___x_568_ = l_Lean_Expr_fvarId_x21(v_e_566_);
        v___x_569_ = l_Lean_instBEqFVarId_beq(v___x_568_, v_fvarId_565_);
        crate::leanh::lean_dec(v___x_568_);
        return v___x_569_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed(
    mut v_fvarId_570_: *mut crate::leanh::LeanObject,
    mut v_e_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_572_: u8 = 0;
    let mut v_r_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1(v_fvarId_570_, v_e_571_);
    crate::leanh::lean_dec_ref(v_e_571_);
    crate::leanh::lean_dec(v_fvarId_570_);
    v_r_573_ = crate::leanh::lean_box((v_res_572_) as usize);
    return v_r_573_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
    mut v_e_574_: *mut crate::leanh::LeanObject,
    mut v_filter_575_: *mut crate::leanh::LeanObject,
    mut v_a_576_: *mut crate::leanh::LeanObject,
    mut v_a_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v___f_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___x_596_: u8 = 0;
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_601_: u8 = 0;
    let mut v_unused_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_603_: u8 = 0;
    let mut v_fvarId_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___f_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: u8 = 0;
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut v_unused_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_pred_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_636_: u8 = 0;
    let mut v_a_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v_a_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v_a_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v_a_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_663_: u8 = 0;
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_filter_575_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_574_);
                    v___x_579_ = 1;
                    v___x_580_ = crate::leanh::lean_box((v___x_579_) as usize);
                    v___x_581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_581_, 0, v___x_580_);
                    return v___x_581_;
                }
                1 => {
                    v_declName_582_ = crate::leanh::lean_ctor_get(v_filter_575_, 0);
                    v_isSharedCheck_603_ = (!crate::leanh::lean_is_exclusive(v_filter_575_)) as u8;
                    if v_isSharedCheck_603_ == 0 {
                        v___x_584_ = v_filter_575_;
                        v_isShared_585_ = v_isSharedCheck_603_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_582_);
                        crate::leanh::lean_dec(v_filter_575_);
                        v___x_584_ = crate::leanh::lean_box(0);
                        v_isShared_585_ = v_isSharedCheck_603_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_fvarId_604_ = crate::leanh::lean_ctor_get(v_filter_575_, 0);
                    v_isSharedCheck_625_ = (!crate::leanh::lean_is_exclusive(v_filter_575_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_606_ = v_filter_575_;
                        v_isShared_607_ = v_isSharedCheck_625_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_604_);
                        crate::leanh::lean_dec(v_filter_575_);
                        v___x_606_ = crate::leanh::lean_box(0);
                        v_isShared_607_ = v_isSharedCheck_625_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_pred_626_ = crate::leanh::lean_ctor_get(v_filter_575_, 0);
                    crate::leanh::lean_inc_ref(v_pred_626_);
                    crate::leanh::lean_dec_ref_known(v_filter_575_, 1);
                    v___x_627_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_getGen___redArg(v_e_574_, v_a_576_, v_a_577_);
                    if crate::leanh::lean_obj_tag(v___x_627_) == 0 {
                        v_a_628_ = crate::leanh::lean_ctor_get(v___x_627_, 0);
                        v_isSharedCheck_636_ = (!crate::leanh::lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_636_ == 0 {
                            v___x_630_ = v___x_627_;
                            v_isShared_631_ = v_isSharedCheck_636_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_628_);
                            crate::leanh::lean_dec(v___x_627_);
                            v___x_630_ = crate::leanh::lean_box(0);
                            v_isShared_631_ = v_isSharedCheck_636_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_pred_626_);
                        v_a_637_ = crate::leanh::lean_ctor_get(v___x_627_, 0);
                        v_isSharedCheck_644_ = (!crate::leanh::lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_644_ == 0 {
                            v___x_639_ = v___x_627_;
                            v_isShared_640_ = v_isSharedCheck_644_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_637_);
                            crate::leanh::lean_dec(v___x_627_);
                            v___x_639_ = crate::leanh::lean_box(0);
                            v_isShared_640_ = v_isSharedCheck_644_;
                            state = 11;
                            continue;
                        }
                    }
                }
                4 => {
                    v_a_645_ = crate::leanh::lean_ctor_get(v_filter_575_, 0);
                    crate::leanh::lean_inc(v_a_645_);
                    v_b_646_ = crate::leanh::lean_ctor_get(v_filter_575_, 1);
                    crate::leanh::lean_inc(v_b_646_);
                    crate::leanh::lean_dec_ref_known(v_filter_575_, 2);
                    crate::leanh::lean_inc_ref(v_e_574_);
                    v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_574_, v_a_645_, v_a_576_, v_a_577_);
                    if crate::leanh::lean_obj_tag(v___x_647_) == 0 {
                        v_a_648_ = crate::leanh::lean_ctor_get(v___x_647_, 0);
                        crate::leanh::lean_inc(v_a_648_);
                        v___x_649_ = (crate::leanh::lean_unbox(v_a_648_) as u8);
                        crate::leanh::lean_dec(v_a_648_);
                        if v___x_649_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_647_, 1);
                            v_filter_575_ = v_b_646_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_646_);
                            crate::leanh::lean_dec_ref(v_e_574_);
                            return v___x_647_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_646_);
                        crate::leanh::lean_dec_ref(v_e_574_);
                        return v___x_647_;
                    }
                }
                5 => {
                    v_a_651_ = crate::leanh::lean_ctor_get(v_filter_575_, 0);
                    crate::leanh::lean_inc(v_a_651_);
                    v_b_652_ = crate::leanh::lean_ctor_get(v_filter_575_, 1);
                    crate::leanh::lean_inc(v_b_652_);
                    crate::leanh::lean_dec_ref_known(v_filter_575_, 2);
                    crate::leanh::lean_inc_ref(v_e_574_);
                    v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_574_, v_a_651_, v_a_576_, v_a_577_);
                    if crate::leanh::lean_obj_tag(v___x_653_) == 0 {
                        v_a_654_ = crate::leanh::lean_ctor_get(v___x_653_, 0);
                        crate::leanh::lean_inc(v_a_654_);
                        v___x_655_ = (crate::leanh::lean_unbox(v_a_654_) as u8);
                        crate::leanh::lean_dec(v_a_654_);
                        if v___x_655_ == 0 {
                            crate::leanh::lean_dec(v_b_652_);
                            crate::leanh::lean_dec_ref(v_e_574_);
                            return v___x_653_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_653_, 1);
                            v_filter_575_ = v_b_652_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_652_);
                        crate::leanh::lean_dec_ref(v_e_574_);
                        return v___x_653_;
                    }
                }
                _ => {
                    v_a_657_ = crate::leanh::lean_ctor_get(v_filter_575_, 0);
                    crate::leanh::lean_inc(v_a_657_);
                    crate::leanh::lean_dec_ref_known(v_filter_575_, 1);
                    v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_e_574_, v_a_657_, v_a_576_, v_a_577_);
                    if crate::leanh::lean_obj_tag(v___x_658_) == 0 {
                        v_a_659_ = crate::leanh::lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_674_ = (!crate::leanh::lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_674_ == 0 {
                            v___x_661_ = v___x_658_;
                            v_isShared_662_ = v_isSharedCheck_674_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_659_);
                            crate::leanh::lean_dec(v___x_658_);
                            v___x_661_ = crate::leanh::lean_box(0);
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
                v___f_586_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_586_, 0, v_declName_582_);
                v___x_587_ = lean_find_expr(v___f_586_, v_e_574_);
                crate::leanh::lean_dec_ref(v_e_574_);
                crate::leanh::lean_dec_ref(v___f_586_);
                if crate::leanh::lean_obj_tag(v___x_587_) == 0 {
                    v___x_588_ = 0;
                    v___x_589_ = crate::leanh::lean_box((v___x_588_) as usize);
                    if v_isShared_585_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_584_, 0);
                        crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_589_);
                        v___x_591_ = v___x_584_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
                        v___x_591_ = v_reuseFailAlloc_592_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_584_);
                    v_isSharedCheck_601_ = (!crate::leanh::lean_is_exclusive(v___x_587_)) as u8;
                    if v_isSharedCheck_601_ == 0 {
                        v_unused_602_ = crate::leanh::lean_ctor_get(v___x_587_, 0);
                        crate::leanh::lean_dec(v_unused_602_);
                        v___x_594_ = v___x_587_;
                        v_isShared_595_ = v_isSharedCheck_601_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_587_);
                        v___x_594_ = crate::leanh::lean_box(0);
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
                v___x_597_ = crate::leanh::lean_box((v___x_596_) as usize);
                if v_isShared_595_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_594_, 0);
                    crate::leanh::lean_ctor_set(v___x_594_, 0, v___x_597_);
                    v___x_599_ = v___x_594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
                    v___x_599_ = v_reuseFailAlloc_600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_599_;
            }
            5 => {
                v___f_608_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_608_, 0, v_fvarId_604_);
                v___x_609_ = lean_find_expr(v___f_608_, v_e_574_);
                crate::leanh::lean_dec_ref(v_e_574_);
                crate::leanh::lean_dec_ref(v___f_608_);
                if crate::leanh::lean_obj_tag(v___x_609_) == 0 {
                    v___x_610_ = 0;
                    v___x_611_ = crate::leanh::lean_box((v___x_610_) as usize);
                    if v_isShared_607_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_606_, 0);
                        crate::leanh::lean_ctor_set(v___x_606_, 0, v___x_611_);
                        v___x_613_ = v___x_606_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
                        v___x_613_ = v_reuseFailAlloc_614_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_606_);
                    v_isSharedCheck_623_ = (!crate::leanh::lean_is_exclusive(v___x_609_)) as u8;
                    if v_isSharedCheck_623_ == 0 {
                        v_unused_624_ = crate::leanh::lean_ctor_get(v___x_609_, 0);
                        crate::leanh::lean_dec(v_unused_624_);
                        v___x_616_ = v___x_609_;
                        v_isShared_617_ = v_isSharedCheck_623_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_609_);
                        v___x_616_ = crate::leanh::lean_box(0);
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
                v___x_619_ = crate::leanh::lean_box((v___x_618_) as usize);
                if v_isShared_617_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_616_, 0);
                    crate::leanh::lean_ctor_set(v___x_616_, 0, v___x_619_);
                    v___x_621_ = v___x_616_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
                    v___x_621_ = v_reuseFailAlloc_622_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_621_;
            }
            9 => {
                v___x_632_ = crate::leanh::lean_apply_1(v_pred_626_, v_a_628_);
                if v_isShared_631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_630_, 0, v___x_632_);
                    v___x_634_ = v___x_630_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_635_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
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
                    v_reuseFailAlloc_643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_642_;
            }
            13 => {
                v___x_663_ = (crate::leanh::lean_unbox(v_a_659_) as u8);
                crate::leanh::lean_dec(v_a_659_);
                if v___x_663_ == 0 {
                    v___x_664_ = 1;
                    v___x_665_ = crate::leanh::lean_box((v___x_664_) as usize);
                    if v_isShared_662_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_661_, 0, v___x_665_);
                        v___x_667_ = v___x_661_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_668_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
                        v___x_667_ = v_reuseFailAlloc_668_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_669_ = 0;
                    v___x_670_ = crate::leanh::lean_box((v___x_669_) as usize);
                    if v_isShared_662_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_661_, 0, v___x_670_);
                        v___x_672_ = v___x_661_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
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
    mut v_e_675_: *mut crate::leanh::LeanObject,
    mut v_filter_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
    mut v_a_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ =
        l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(
            v_e_675_,
            v_filter_676_,
            v_a_677_,
            v_a_678_,
        );
    crate::leanh::lean_dec(v_a_678_);
    crate::leanh::lean_dec(v_a_677_);
    return v_res_680_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go(
    mut v_e_681_: *mut crate::leanh::LeanObject,
    mut v_filter_682_: *mut crate::leanh::LeanObject,
    mut v_a_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
    mut v_a_685_: *mut crate::leanh::LeanObject,
    mut v_a_686_: *mut crate::leanh::LeanObject,
    mut v_a_687_: *mut crate::leanh::LeanObject,
    mut v_a_688_: *mut crate::leanh::LeanObject,
    mut v_a_689_: *mut crate::leanh::LeanObject,
    mut v_a_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_695_: *mut crate::leanh::LeanObject,
    mut v_filter_696_: *mut crate::leanh::LeanObject,
    mut v_a_697_: *mut crate::leanh::LeanObject,
    mut v_a_698_: *mut crate::leanh::LeanObject,
    mut v_a_699_: *mut crate::leanh::LeanObject,
    mut v_a_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_a_705_: *mut crate::leanh::LeanObject,
    mut v_a_706_: *mut crate::leanh::LeanObject,
    mut v_a_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_706_);
    crate::leanh::lean_dec_ref(v_a_705_);
    crate::leanh::lean_dec(v_a_704_);
    crate::leanh::lean_dec_ref(v_a_703_);
    crate::leanh::lean_dec(v_a_702_);
    crate::leanh::lean_dec_ref(v_a_701_);
    crate::leanh::lean_dec(v_a_700_);
    crate::leanh::lean_dec_ref(v_a_699_);
    crate::leanh::lean_dec(v_a_698_);
    crate::leanh::lean_dec(v_a_697_);
    return v_res_708_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_eval___redArg(
    mut v_filter_709_: *mut crate::leanh::LeanObject,
    mut v_e_710_: *mut crate::leanh::LeanObject,
    mut v_a_711_: *mut crate::leanh::LeanObject,
    mut v_a_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_filter_715_: *mut crate::leanh::LeanObject,
    mut v_e_716_: *mut crate::leanh::LeanObject,
    mut v_a_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
    mut v_a_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ =
        l_Lean_Meta_Grind_Filter_eval___redArg(v_filter_715_, v_e_716_, v_a_717_, v_a_718_);
    crate::leanh::lean_dec(v_a_718_);
    crate::leanh::lean_dec(v_a_717_);
    return v_res_720_;
}
pub unsafe fn l_Lean_Meta_Grind_Filter_eval(
    mut v_filter_721_: *mut crate::leanh::LeanObject,
    mut v_e_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
    mut v_a_724_: *mut crate::leanh::LeanObject,
    mut v_a_725_: *mut crate::leanh::LeanObject,
    mut v_a_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
    mut v_a_728_: *mut crate::leanh::LeanObject,
    mut v_a_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_filter_735_: *mut crate::leanh::LeanObject,
    mut v_e_736_: *mut crate::leanh::LeanObject,
    mut v_a_737_: *mut crate::leanh::LeanObject,
    mut v_a_738_: *mut crate::leanh::LeanObject,
    mut v_a_739_: *mut crate::leanh::LeanObject,
    mut v_a_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
    mut v_a_745_: *mut crate::leanh::LeanObject,
    mut v_a_746_: *mut crate::leanh::LeanObject,
    mut v_a_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_746_);
    crate::leanh::lean_dec_ref(v_a_745_);
    crate::leanh::lean_dec(v_a_744_);
    crate::leanh::lean_dec_ref(v_a_743_);
    crate::leanh::lean_dec(v_a_742_);
    crate::leanh::lean_dec_ref(v_a_741_);
    crate::leanh::lean_dec(v_a_740_);
    crate::leanh::lean_dec_ref(v_a_739_);
    crate::leanh::lean_dec(v_a_738_);
    crate::leanh::lean_dec(v_a_737_);
    return v_res_748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Filter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Filter(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Filter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
}
