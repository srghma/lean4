// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: Lean.Compiler.LCNF.InferType
use crate::ffi::{
    lean_expr_eqv, lean_expr_instantiate1, lean_name_eq, lean_nat_add, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_num___override;
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    initialize_Lean_Compiler_LCNF_InferType, l_Lean_Compiler_LCNF_InferType_Pure_inferType,
    runtime_initialize_Lean_Compiler_LCNF_InferType,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Expr_isErased;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_bvar___override, l_Lean_Expr_fvar___override,
    l_Lean_Expr_headBeta, l_Lean_Expr_isLambda, l_Lean_Expr_lam___override,
};
use crate::r#gen::Lean::Level::l_Lean_Level_isEquiv;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_mkLocalDecl;
static mut l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(
    mut v_x_369_: *mut leanh::LeanObject,
    mut v_x_370_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_371_: u8 = 0;
    let mut v___x_372_: u8 = 0;
    let mut v___x_373_: u8 = 0;
    let mut v_head_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_369_) == 0 {
                    if leanh::lean_obj_tag(v_x_370_) == 0 {
                        v___x_371_ = 1;
                        return v___x_371_;
                    } else {
                        v___x_372_ = 0;
                        return v___x_372_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_370_) == 0 {
                        v___x_373_ = 0;
                        return v___x_373_;
                    } else {
                        v_head_374_ = leanh::lean_ctor_get(v_x_369_, 0);
                        v_tail_375_ = leanh::lean_ctor_get(v_x_369_, 1);
                        v_head_376_ = leanh::lean_ctor_get(v_x_370_, 0);
                        v_tail_377_ = leanh::lean_ctor_get(v_x_370_, 1);
                        v___x_378_ = l_Lean_Level_isEquiv(v_head_374_, v_head_376_);
                        if v___x_378_ == 0 {
                            return v___x_378_;
                        } else {
                            v_x_369_ = v_tail_375_;
                            v_x_370_ = v_tail_377_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(
    mut v_x_380_: *mut leanh::LeanObject,
    mut v_x_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_382_: u8 = 0;
    let mut v_r_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ =
        l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_x_380_, v_x_381_);
    leanh::lean_dec(v_x_381_);
    leanh::lean_dec(v_x_380_);
    v_r_383_ = leanh::lean_box((v_res_382_) as usize);
    return v_r_383_;
}
pub unsafe fn l_Lean_Compiler_LCNF_compatibleTypesQuick(
    mut v_a_384_: *mut leanh::LeanObject,
    mut v_b_385_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_d_u2081_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_u2081_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_u2082_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_u2082_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: u8 = 0;
    let mut v___y_394_: u8 = 0;
    let mut v___x_395_: u8 = 0;
    let mut v_a_x27_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_x27_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: u8 = 0;
    let mut v___x_400_: u8 = 0;
    let mut v___x_402_: u8 = 0;
    let mut v_fn_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: u8 = 0;
    let mut v_binderType_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: u8 = 0;
    let mut v_declName_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: u8 = 0;
    let mut v___x_425_: u8 = 0;
    let mut v___x_426_: u8 = 0;
    let mut v___x_427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_426_ = l_Lean_Expr_isErased(v_a_384_);
                if v___x_426_ == 0 {
                    v___x_427_ = l_Lean_Expr_isErased(v_b_385_);
                    v___y_394_ = v___x_427_;
                    state = 2;
                    continue;
                } else {
                    v___y_394_ = v___x_426_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_391_ =
                    l_Lean_Compiler_LCNF_compatibleTypesQuick(v_d_u2081_387_, v_d_u2082_389_);
                if v___x_391_ == 0 {
                    leanh::lean_dec_ref(v_b_u2082_390_);
                    leanh::lean_dec_ref(v_b_u2081_388_);
                    return v___x_391_;
                } else {
                    v_a_384_ = v_b_u2081_388_;
                    v_b_385_ = v_b_u2082_390_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_395_ = 1;
                if v___y_394_ == 0 {
                    leanh::lean_inc_ref(v_a_384_);
                    v_a_x27_396_ = l_Lean_Expr_headBeta(v_a_384_);
                    leanh::lean_inc_ref(v_b_385_);
                    v_b_x27_397_ = l_Lean_Expr_headBeta(v_b_385_);
                    v___x_398_ = lean_expr_eqv(v_a_384_, v_a_x27_396_);
                    if v___x_398_ == 0 {
                        leanh::lean_dec_ref(v_b_385_);
                        leanh::lean_dec_ref(v_a_384_);
                        v_a_384_ = v_a_x27_396_;
                        v_b_385_ = v_b_x27_397_;
                        state = 0;
                        continue;
                    } else {
                        v___x_400_ = lean_expr_eqv(v_b_385_, v_b_x27_397_);
                        if v___x_400_ == 0 {
                            leanh::lean_dec_ref(v_b_385_);
                            leanh::lean_dec_ref(v_a_384_);
                            v_a_384_ = v_a_x27_396_;
                            v_b_385_ = v_b_x27_397_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_x27_397_);
                            leanh::lean_dec_ref(v_a_x27_396_);
                            v___x_402_ = lean_expr_eqv(v_a_384_, v_b_385_);
                            if v___x_402_ == 0 {
                                match leanh::lean_obj_tag(v_a_384_) {
                                    5 => {
                                        if leanh::lean_obj_tag(v_b_385_) == 5 {
                                            v_fn_403_ = leanh::lean_ctor_get(v_a_384_, 0);
                                            leanh::lean_inc_ref(v_fn_403_);
                                            v_arg_404_ = leanh::lean_ctor_get(v_a_384_, 1);
                                            leanh::lean_inc_ref(v_arg_404_);
                                            leanh::lean_dec_ref_known(v_a_384_, 2);
                                            v_fn_405_ = leanh::lean_ctor_get(v_b_385_, 0);
                                            leanh::lean_inc_ref(v_fn_405_);
                                            v_arg_406_ = leanh::lean_ctor_get(v_b_385_, 1);
                                            leanh::lean_inc_ref(v_arg_406_);
                                            leanh::lean_dec_ref_known(v_b_385_, 2);
                                            v___x_407_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(
                                                v_fn_403_, v_fn_405_,
                                            );
                                            if v___x_407_ == 0 {
                                                leanh::lean_dec_ref(v_arg_406_);
                                                leanh::lean_dec_ref(v_arg_404_);
                                                return v___x_407_;
                                            } else {
                                                v_a_384_ = v_arg_404_;
                                                v_b_385_ = v_arg_406_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_a_384_, 2);
                                            leanh::lean_dec_ref(v_b_385_);
                                            return v___x_402_;
                                        }
                                    }
                                    7 => {
                                        if leanh::lean_obj_tag(v_b_385_) == 7 {
                                            v_binderType_409_ =
                                                leanh::lean_ctor_get(v_a_384_, 1);
                                            leanh::lean_inc_ref(v_binderType_409_);
                                            v_body_410_ = leanh::lean_ctor_get(v_a_384_, 2);
                                            leanh::lean_inc_ref(v_body_410_);
                                            leanh::lean_dec_ref_known(v_a_384_, 3);
                                            v_binderType_411_ =
                                                leanh::lean_ctor_get(v_b_385_, 1);
                                            leanh::lean_inc_ref(v_binderType_411_);
                                            v_body_412_ = leanh::lean_ctor_get(v_b_385_, 2);
                                            leanh::lean_inc_ref(v_body_412_);
                                            leanh::lean_dec_ref_known(v_b_385_, 3);
                                            v_d_u2081_387_ = v_binderType_409_;
                                            v_b_u2081_388_ = v_body_410_;
                                            v_d_u2082_389_ = v_binderType_411_;
                                            v_b_u2082_390_ = v_body_412_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref_known(v_a_384_, 3);
                                            leanh::lean_dec_ref(v_b_385_);
                                            return v___x_402_;
                                        }
                                    }
                                    6 => {
                                        if leanh::lean_obj_tag(v_b_385_) == 6 {
                                            v_binderType_413_ =
                                                leanh::lean_ctor_get(v_a_384_, 1);
                                            leanh::lean_inc_ref(v_binderType_413_);
                                            v_body_414_ = leanh::lean_ctor_get(v_a_384_, 2);
                                            leanh::lean_inc_ref(v_body_414_);
                                            leanh::lean_dec_ref_known(v_a_384_, 3);
                                            v_binderType_415_ =
                                                leanh::lean_ctor_get(v_b_385_, 1);
                                            leanh::lean_inc_ref(v_binderType_415_);
                                            v_body_416_ = leanh::lean_ctor_get(v_b_385_, 2);
                                            leanh::lean_inc_ref(v_body_416_);
                                            leanh::lean_dec_ref_known(v_b_385_, 3);
                                            v_d_u2081_387_ = v_binderType_413_;
                                            v_b_u2081_388_ = v_body_414_;
                                            v_d_u2082_389_ = v_binderType_415_;
                                            v_b_u2082_390_ = v_body_416_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref_known(v_a_384_, 3);
                                            leanh::lean_dec_ref(v_b_385_);
                                            return v___x_402_;
                                        }
                                    }
                                    3 => {
                                        if leanh::lean_obj_tag(v_b_385_) == 3 {
                                            v_u_417_ = leanh::lean_ctor_get(v_a_384_, 0);
                                            leanh::lean_inc(v_u_417_);
                                            leanh::lean_dec_ref_known(v_a_384_, 1);
                                            v_u_418_ = leanh::lean_ctor_get(v_b_385_, 0);
                                            leanh::lean_inc(v_u_418_);
                                            leanh::lean_dec_ref_known(v_b_385_, 1);
                                            v___x_419_ = l_Lean_Level_isEquiv(v_u_417_, v_u_418_);
                                            leanh::lean_dec(v_u_418_);
                                            leanh::lean_dec(v_u_417_);
                                            return v___x_419_;
                                        } else {
                                            leanh::lean_dec_ref_known(v_a_384_, 1);
                                            leanh::lean_dec_ref(v_b_385_);
                                            return v___x_402_;
                                        }
                                    }
                                    4 => {
                                        if leanh::lean_obj_tag(v_b_385_) == 4 {
                                            v_declName_420_ =
                                                leanh::lean_ctor_get(v_a_384_, 0);
                                            leanh::lean_inc(v_declName_420_);
                                            v_us_421_ = leanh::lean_ctor_get(v_a_384_, 1);
                                            leanh::lean_inc(v_us_421_);
                                            leanh::lean_dec_ref_known(v_a_384_, 2);
                                            v_declName_422_ =
                                                leanh::lean_ctor_get(v_b_385_, 0);
                                            leanh::lean_inc(v_declName_422_);
                                            v_us_423_ = leanh::lean_ctor_get(v_b_385_, 1);
                                            leanh::lean_inc(v_us_423_);
                                            leanh::lean_dec_ref_known(v_b_385_, 2);
                                            v___x_424_ =
                                                lean_name_eq(v_declName_420_, v_declName_422_);
                                            leanh::lean_dec(v_declName_422_);
                                            leanh::lean_dec(v_declName_420_);
                                            if v___x_424_ == 0 {
                                                leanh::lean_dec(v_us_423_);
                                                leanh::lean_dec(v_us_421_);
                                                return v___x_424_;
                                            } else {
                                                v___x_425_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_421_, v_us_423_);
                                                leanh::lean_dec(v_us_423_);
                                                leanh::lean_dec(v_us_421_);
                                                return v___x_425_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_a_384_, 2);
                                            leanh::lean_dec_ref(v_b_385_);
                                            return v___x_402_;
                                        }
                                    }
                                    _ => {
                                        leanh::lean_dec_ref(v_b_385_);
                                        leanh::lean_dec_ref(v_a_384_);
                                        return v___x_402_;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_385_);
                                leanh::lean_dec_ref(v_a_384_);
                                return v___x_395_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_385_);
                    leanh::lean_dec_ref(v_a_384_);
                    return v___x_395_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(
    mut v_a_428_: *mut leanh::LeanObject,
    mut v_b_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_428_, v_b_429_);
    v_r_431_ = leanh::lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = leanh::lean_unsigned_to_nat(0);
    v___x_433_ = l_Lean_Expr_bvar___override(v___x_432_);
    return v___x_433_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(
    mut v_e_434_: *mut leanh::LeanObject,
    mut v_a_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_a_437_: *mut leanh::LeanObject,
    mut v_a_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_449_: u8 = 0;
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_461_: u8 = 0;
    let mut v_a_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_465_: u8 = 0;
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_434_);
                v___x_441_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
                    v_e_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_,
                );
                if leanh::lean_obj_tag(v___x_441_) == 0 {
                    v_a_442_ = leanh::lean_ctor_get(v___x_441_, 0);
                    v_isSharedCheck_461_ = (!leanh::lean_is_exclusive(v___x_441_)) as u8;
                    if v_isSharedCheck_461_ == 0 {
                        v___x_444_ = v___x_441_;
                        v_isShared_445_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_442_);
                        leanh::lean_dec(v___x_441_);
                        v___x_444_ = leanh::lean_box(0);
                        v_isShared_445_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_434_);
                    v_a_462_ = leanh::lean_ctor_get(v___x_441_, 0);
                    v_isSharedCheck_469_ = (!leanh::lean_is_exclusive(v___x_441_)) as u8;
                    if v_isSharedCheck_469_ == 0 {
                        v___x_464_ = v___x_441_;
                        v_isShared_465_ = v_isSharedCheck_469_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_462_);
                        leanh::lean_dec(v___x_441_);
                        v___x_464_ = leanh::lean_box(0);
                        v_isShared_465_ = v_isSharedCheck_469_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_446_ = l_Lean_Expr_headBeta(v_a_442_);
                if leanh::lean_obj_tag(v___x_446_) == 7 {
                    v_binderName_447_ = leanh::lean_ctor_get(v___x_446_, 0);
                    leanh::lean_inc(v_binderName_447_);
                    v_binderType_448_ = leanh::lean_ctor_get(v___x_446_, 1);
                    leanh::lean_inc_ref(v_binderType_448_);
                    v_binderInfo_449_ = leanh::lean_ctor_get_uint8(
                        v___x_446_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v___x_446_, 3);
                    v___x_450_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once), _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
                    v___x_451_ = l_Lean_Expr_app___override(v_e_434_, v___x_450_);
                    v___x_452_ = l_Lean_Expr_lam___override(
                        v_binderName_447_,
                        v_binderType_448_,
                        v___x_451_,
                        v_binderInfo_449_,
                    );
                    v___x_453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_453_, 0, v___x_452_);
                    if v_isShared_445_ == 0 {
                        leanh::lean_ctor_set(v___x_444_, 0, v___x_453_);
                        v___x_455_ = v___x_444_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_456_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
                        v___x_455_ = v_reuseFailAlloc_456_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_446_);
                    leanh::lean_dec_ref(v_e_434_);
                    v___x_457_ = leanh::lean_box(0);
                    if v_isShared_445_ == 0 {
                        leanh::lean_ctor_set(v___x_444_, 0, v___x_457_);
                        v___x_459_ = v___x_444_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_460_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
                        v___x_459_ = v_reuseFailAlloc_460_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_455_;
            }
            3 => {
                return v___x_459_;
            }
            4 => {
                if v_isShared_465_ == 0 {
                    v___x_467_ = v___x_464_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
                    v___x_467_ = v_reuseFailAlloc_468_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(
    mut v_e_470_: *mut leanh::LeanObject,
    mut v_a_471_: *mut leanh::LeanObject,
    mut v_a_472_: *mut leanh::LeanObject,
    mut v_a_473_: *mut leanh::LeanObject,
    mut v_a_474_: *mut leanh::LeanObject,
    mut v_a_475_: *mut leanh::LeanObject,
    mut v_a_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
    leanh::lean_dec(v_a_475_);
    leanh::lean_dec_ref(v_a_474_);
    leanh::lean_dec(v_a_473_);
    leanh::lean_dec_ref(v_a_472_);
    leanh::lean_dec_ref(v_a_471_);
    return v_res_477_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(
    mut v___y_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_486_: u8 = 0;
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v_r_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut v_unused_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_480_ = lean_st_ref_get(v___y_478_);
                v_ngen_481_ = leanh::lean_ctor_get(v___x_480_, 2);
                leanh::lean_inc_ref(v_ngen_481_);
                leanh::lean_dec(v___x_480_);
                v_namePrefix_482_ = leanh::lean_ctor_get(v_ngen_481_, 0);
                v_idx_483_ = leanh::lean_ctor_get(v_ngen_481_, 1);
                v_isSharedCheck_512_ = (!leanh::lean_is_exclusive(v_ngen_481_)) as u8;
                if v_isSharedCheck_512_ == 0 {
                    v___x_485_ = v_ngen_481_;
                    v_isShared_486_ = v_isSharedCheck_512_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_483_);
                    leanh::lean_inc(v_namePrefix_482_);
                    leanh::lean_dec(v_ngen_481_);
                    v___x_485_ = leanh::lean_box(0);
                    v_isShared_486_ = v_isSharedCheck_512_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_487_ = lean_st_ref_take(v___y_478_);
                v_env_488_ = leanh::lean_ctor_get(v___x_487_, 0);
                v_nextMacroScope_489_ = leanh::lean_ctor_get(v___x_487_, 1);
                v_auxDeclNGen_490_ = leanh::lean_ctor_get(v___x_487_, 3);
                v_traceState_491_ = leanh::lean_ctor_get(v___x_487_, 4);
                v_cache_492_ = leanh::lean_ctor_get(v___x_487_, 5);
                v_messages_493_ = leanh::lean_ctor_get(v___x_487_, 6);
                v_infoState_494_ = leanh::lean_ctor_get(v___x_487_, 7);
                v_snapshotTasks_495_ = leanh::lean_ctor_get(v___x_487_, 8);
                v_isSharedCheck_510_ = (!leanh::lean_is_exclusive(v___x_487_)) as u8;
                if v_isSharedCheck_510_ == 0 {
                    v_unused_511_ = leanh::lean_ctor_get(v___x_487_, 2);
                    leanh::lean_dec(v_unused_511_);
                    v___x_497_ = v___x_487_;
                    v_isShared_498_ = v_isSharedCheck_510_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_495_);
                    leanh::lean_inc(v_infoState_494_);
                    leanh::lean_inc(v_messages_493_);
                    leanh::lean_inc(v_cache_492_);
                    leanh::lean_inc(v_traceState_491_);
                    leanh::lean_inc(v_auxDeclNGen_490_);
                    leanh::lean_inc(v_nextMacroScope_489_);
                    leanh::lean_inc(v_env_488_);
                    leanh::lean_dec(v___x_487_);
                    v___x_497_ = leanh::lean_box(0);
                    v_isShared_498_ = v_isSharedCheck_510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_483_);
                leanh::lean_inc(v_namePrefix_482_);
                v_r_499_ = l_Lean_Name_num___override(v_namePrefix_482_, v_idx_483_);
                v___x_500_ = leanh::lean_unsigned_to_nat(1);
                v___x_501_ = lean_nat_add(v_idx_483_, v___x_500_);
                leanh::lean_dec(v_idx_483_);
                if v_isShared_486_ == 0 {
                    leanh::lean_ctor_set(v___x_485_, 1, v___x_501_);
                    v___x_503_ = v___x_485_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v_namePrefix_482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_501_);
                    v___x_503_ = v_reuseFailAlloc_509_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_498_ == 0 {
                    leanh::lean_ctor_set(v___x_497_, 2, v___x_503_);
                    v___x_505_ = v___x_497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_508_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 0, v_env_488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nextMacroScope_489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 2, v___x_503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 3, v_auxDeclNGen_490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 4, v_traceState_491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 5, v_cache_492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 6, v_messages_493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 7, v_infoState_494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_508_, 8, v_snapshotTasks_495_);
                    v___x_505_ = v_reuseFailAlloc_508_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_506_ = lean_st_ref_set(v___y_478_, v___x_505_);
                v___x_507_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_507_, 0, v_r_499_);
                return v___x_507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(
    mut v___y_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_513_);
    leanh::lean_dec(v___y_513_);
    return v_res_515_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(
    mut v___y_516_: *mut leanh::LeanObject,
    mut v___y_517_: *mut leanh::LeanObject,
    mut v___y_518_: *mut leanh::LeanObject,
    mut v___y_519_: *mut leanh::LeanObject,
    mut v___y_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_526_: u8 = 0;
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_522_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_520_);
                v_a_523_ = leanh::lean_ctor_get(v___x_522_, 0);
                v_isSharedCheck_530_ = (!leanh::lean_is_exclusive(v___x_522_)) as u8;
                if v_isSharedCheck_530_ == 0 {
                    v___x_525_ = v___x_522_;
                    v_isShared_526_ = v_isSharedCheck_530_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_523_);
                    leanh::lean_dec(v___x_522_);
                    v___x_525_ = leanh::lean_box(0);
                    v_isShared_526_ = v_isSharedCheck_530_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_526_ == 0 {
                    v___x_528_ = v___x_525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
                    v___x_528_ = v_reuseFailAlloc_529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(
    mut v___y_531_: *mut leanh::LeanObject,
    mut v___y_532_: *mut leanh::LeanObject,
    mut v___y_533_: *mut leanh::LeanObject,
    mut v___y_534_: *mut leanh::LeanObject,
    mut v___y_535_: *mut leanh::LeanObject,
    mut v___y_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_537_ =
        l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(
            v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_,
        );
    leanh::lean_dec(v___y_535_);
    leanh::lean_dec_ref(v___y_534_);
    leanh::lean_dec(v___y_533_);
    leanh::lean_dec_ref(v___y_532_);
    leanh::lean_dec_ref(v___y_531_);
    return v_res_537_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(
    mut v_a_538_: *mut leanh::LeanObject,
    mut v_b_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
    mut v_a_541_: *mut leanh::LeanObject,
    mut v_a_542_: *mut leanh::LeanObject,
    mut v_a_543_: *mut leanh::LeanObject,
    mut v_a_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_u2081_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_u2081_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_550_: u8 = 0;
    let mut v_d_u2082_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_u2082_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: u8 = 0;
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_576_: u8 = 0;
    let mut v___y_578_: u8 = 0;
    let mut v___y_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_592_: u8 = 0;
    let mut v_val_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_a_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_607_: u8 = 0;
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v_val_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v___y_629_: u8 = 0;
    let mut v___x_630_: u8 = 0;
    let mut v_a_x27_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_x27_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: u8 = 0;
    let mut v___x_635_: u8 = 0;
    let mut v___x_637_: u8 = 0;
    let mut v_fn_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v_expr_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_651_: u8 = 0;
    let mut v_binderType_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_659_: u8 = 0;
    let mut v_binderType_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_691_ = l_Lean_Expr_isErased(v_a_538_);
                if v___x_691_ == 0 {
                    v___x_692_ = l_Lean_Expr_isErased(v_b_539_);
                    v___y_629_ = v___x_692_;
                    state = 13;
                    continue;
                } else {
                    v___y_629_ = v___x_691_;
                    state = 13;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_553_);
                leanh::lean_inc_ref(v_d_u2081_548_);
                v___x_558_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(
                    v_d_u2081_548_,
                    v_d_u2082_551_,
                    v___y_553_,
                    v___y_554_,
                    v___y_555_,
                    v___y_556_,
                    v___y_557_,
                );
                if leanh::lean_obj_tag(v___x_558_) == 0 {
                    v_a_559_ = leanh::lean_ctor_get(v___x_558_, 0);
                    leanh::lean_inc(v_a_559_);
                    v___x_560_ = (leanh::lean_unbox(v_a_559_) as u8);
                    leanh::lean_dec(v_a_559_);
                    if v___x_560_ == 0 {
                        leanh::lean_dec_ref(v___y_553_);
                        leanh::lean_dec_ref(v_b_u2082_552_);
                        leanh::lean_dec_ref(v_b_u2081_549_);
                        leanh::lean_dec_ref(v_d_u2081_548_);
                        leanh::lean_dec(v_n_547_);
                        return v___x_558_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_558_, 1);
                        v___x_561_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
                        if leanh::lean_obj_tag(v___x_561_) == 0 {
                            v_a_562_ = leanh::lean_ctor_get(v___x_561_, 0);
                            leanh::lean_inc_n(v_a_562_, 2);
                            leanh::lean_dec_ref_known(v___x_561_, 1);
                            v___x_563_ = l_Lean_Expr_fvar___override(v_a_562_);
                            v___x_564_ = 0;
                            v___x_565_ = l_Lean_LocalContext_mkLocalDecl(
                                v___y_553_,
                                v_a_562_,
                                v_n_547_,
                                v_d_u2081_548_,
                                v_bi_550_,
                                v___x_564_,
                            );
                            v___x_566_ = lean_expr_instantiate1(v_b_u2081_549_, v___x_563_);
                            leanh::lean_dec_ref(v_b_u2081_549_);
                            v___x_567_ = lean_expr_instantiate1(v_b_u2082_552_, v___x_563_);
                            leanh::lean_dec_ref(v___x_563_);
                            leanh::lean_dec_ref(v_b_u2082_552_);
                            v_a_538_ = v___x_566_;
                            v_b_539_ = v___x_567_;
                            v_a_540_ = v___x_565_;
                            v_a_541_ = v___y_554_;
                            v_a_542_ = v___y_555_;
                            v_a_543_ = v___y_556_;
                            v_a_544_ = v___y_557_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___y_553_);
                            leanh::lean_dec_ref(v_b_u2082_552_);
                            leanh::lean_dec_ref(v_b_u2081_549_);
                            leanh::lean_dec_ref(v_d_u2081_548_);
                            leanh::lean_dec(v_n_547_);
                            v_a_569_ = leanh::lean_ctor_get(v___x_561_, 0);
                            v_isSharedCheck_576_ =
                                (!leanh::lean_is_exclusive(v___x_561_)) as u8;
                            if v_isSharedCheck_576_ == 0 {
                                v___x_571_ = v___x_561_;
                                v_isShared_572_ = v_isSharedCheck_576_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_569_);
                                leanh::lean_dec(v___x_561_);
                                v___x_571_ = leanh::lean_box(0);
                                v_isShared_572_ = v_isSharedCheck_576_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_553_);
                    leanh::lean_dec_ref(v_b_u2082_552_);
                    leanh::lean_dec_ref(v_b_u2081_549_);
                    leanh::lean_dec_ref(v_d_u2081_548_);
                    leanh::lean_dec(v_n_547_);
                    return v___x_558_;
                }
            }
            2 => {
                if v_isShared_572_ == 0 {
                    v___x_574_ = v___x_571_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
                    v___x_574_ = v_reuseFailAlloc_575_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_574_;
            }
            4 => {
                v___x_584_ = l_Lean_Expr_isLambda(v_a_538_);
                if v___x_584_ == 0 {
                    v___x_585_ = l_Lean_Expr_isLambda(v_b_539_);
                    if v___x_585_ == 0 {
                        leanh::lean_dec_ref(v___y_579_);
                        leanh::lean_dec_ref(v_b_539_);
                        leanh::lean_dec_ref(v_a_538_);
                        v___x_586_ = leanh::lean_box((v___x_585_) as usize);
                        v___x_587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_587_, 0, v___x_586_);
                        return v___x_587_;
                    } else {
                        v___x_588_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_a_538_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
                        if leanh::lean_obj_tag(v___x_588_) == 0 {
                            v_a_589_ = leanh::lean_ctor_get(v___x_588_, 0);
                            v_isSharedCheck_599_ =
                                (!leanh::lean_is_exclusive(v___x_588_)) as u8;
                            if v_isSharedCheck_599_ == 0 {
                                v___x_591_ = v___x_588_;
                                v_isShared_592_ = v_isSharedCheck_599_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_589_);
                                leanh::lean_dec(v___x_588_);
                                v___x_591_ = leanh::lean_box(0);
                                v_isShared_592_ = v_isSharedCheck_599_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___y_579_);
                            leanh::lean_dec_ref(v_b_539_);
                            v_a_600_ = leanh::lean_ctor_get(v___x_588_, 0);
                            v_isSharedCheck_607_ =
                                (!leanh::lean_is_exclusive(v___x_588_)) as u8;
                            if v_isSharedCheck_607_ == 0 {
                                v___x_602_ = v___x_588_;
                                v_isShared_603_ = v_isSharedCheck_607_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_600_);
                                leanh::lean_dec(v___x_588_);
                                v___x_602_ = leanh::lean_box(0);
                                v_isShared_603_ = v_isSharedCheck_607_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_608_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_b_539_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
                    if leanh::lean_obj_tag(v___x_608_) == 0 {
                        v_a_609_ = leanh::lean_ctor_get(v___x_608_, 0);
                        v_isSharedCheck_619_ = (!leanh::lean_is_exclusive(v___x_608_)) as u8;
                        if v_isSharedCheck_619_ == 0 {
                            v___x_611_ = v___x_608_;
                            v_isShared_612_ = v_isSharedCheck_619_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_609_);
                            leanh::lean_dec(v___x_608_);
                            v___x_611_ = leanh::lean_box(0);
                            v_isShared_612_ = v_isSharedCheck_619_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_579_);
                        leanh::lean_dec_ref(v_a_538_);
                        v_a_620_ = leanh::lean_ctor_get(v___x_608_, 0);
                        v_isSharedCheck_627_ = (!leanh::lean_is_exclusive(v___x_608_)) as u8;
                        if v_isSharedCheck_627_ == 0 {
                            v___x_622_ = v___x_608_;
                            v_isShared_623_ = v_isSharedCheck_627_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_620_);
                            leanh::lean_dec(v___x_608_);
                            v___x_622_ = leanh::lean_box(0);
                            v_isShared_623_ = v_isSharedCheck_627_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_589_) == 1 {
                    leanh::lean_del_object(v___x_591_);
                    v_val_593_ = leanh::lean_ctor_get(v_a_589_, 0);
                    leanh::lean_inc(v_val_593_);
                    leanh::lean_dec_ref_known(v_a_589_, 1);
                    v_a_538_ = v_val_593_;
                    v_a_540_ = v___y_579_;
                    v_a_541_ = v___y_580_;
                    v_a_542_ = v___y_581_;
                    v_a_543_ = v___y_582_;
                    v_a_544_ = v___y_583_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_589_);
                    leanh::lean_dec_ref(v___y_579_);
                    leanh::lean_dec_ref(v_b_539_);
                    v___x_595_ = leanh::lean_box((v___x_584_) as usize);
                    if v_isShared_592_ == 0 {
                        leanh::lean_ctor_set(v___x_591_, 0, v___x_595_);
                        v___x_597_ = v___x_591_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
                        v___x_597_ = v_reuseFailAlloc_598_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_597_;
            }
            7 => {
                if v_isShared_603_ == 0 {
                    v___x_605_ = v___x_602_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
                    v___x_605_ = v_reuseFailAlloc_606_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_605_;
            }
            9 => {
                if leanh::lean_obj_tag(v_a_609_) == 1 {
                    leanh::lean_del_object(v___x_611_);
                    v_val_613_ = leanh::lean_ctor_get(v_a_609_, 0);
                    leanh::lean_inc(v_val_613_);
                    leanh::lean_dec_ref_known(v_a_609_, 1);
                    v_b_539_ = v_val_613_;
                    v_a_540_ = v___y_579_;
                    v_a_541_ = v___y_580_;
                    v_a_542_ = v___y_581_;
                    v_a_543_ = v___y_582_;
                    v_a_544_ = v___y_583_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_609_);
                    leanh::lean_dec_ref(v___y_579_);
                    leanh::lean_dec_ref(v_a_538_);
                    v___x_615_ = leanh::lean_box((v___y_578_) as usize);
                    if v_isShared_612_ == 0 {
                        leanh::lean_ctor_set(v___x_611_, 0, v___x_615_);
                        v___x_617_ = v___x_611_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_618_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
                        v___x_617_ = v_reuseFailAlloc_618_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_617_;
            }
            11 => {
                if v_isShared_623_ == 0 {
                    v___x_625_ = v___x_622_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
                    v___x_625_ = v_reuseFailAlloc_626_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_625_;
            }
            13 => {
                v___x_630_ = 1;
                if v___y_629_ == 0 {
                    leanh::lean_inc_ref(v_a_538_);
                    v_a_x27_631_ = l_Lean_Expr_headBeta(v_a_538_);
                    leanh::lean_inc_ref(v_b_539_);
                    v_b_x27_632_ = l_Lean_Expr_headBeta(v_b_539_);
                    v___x_633_ = lean_expr_eqv(v_a_538_, v_a_x27_631_);
                    if v___x_633_ == 0 {
                        leanh::lean_dec_ref(v_b_539_);
                        leanh::lean_dec_ref(v_a_538_);
                        v_a_538_ = v_a_x27_631_;
                        v_b_539_ = v_b_x27_632_;
                        state = 0;
                        continue;
                    } else {
                        v___x_635_ = lean_expr_eqv(v_b_539_, v_b_x27_632_);
                        if v___x_635_ == 0 {
                            leanh::lean_dec_ref(v_b_539_);
                            leanh::lean_dec_ref(v_a_538_);
                            v_a_538_ = v_a_x27_631_;
                            v_b_539_ = v_b_x27_632_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_x27_632_);
                            leanh::lean_dec_ref(v_a_x27_631_);
                            v___x_637_ = lean_expr_eqv(v_a_538_, v_b_539_);
                            if v___x_637_ == 0 {
                                match leanh::lean_obj_tag(v_a_538_) {
                                    5 => match leanh::lean_obj_tag(v_b_539_) {
                                        5 => {
                                            v_fn_638_ = leanh::lean_ctor_get(v_a_538_, 0);
                                            leanh::lean_inc_ref(v_fn_638_);
                                            v_arg_639_ = leanh::lean_ctor_get(v_a_538_, 1);
                                            leanh::lean_inc_ref(v_arg_639_);
                                            leanh::lean_dec_ref_known(v_a_538_, 2);
                                            v_fn_640_ = leanh::lean_ctor_get(v_b_539_, 0);
                                            leanh::lean_inc_ref(v_fn_640_);
                                            v_arg_641_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_arg_641_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            leanh::lean_inc_ref(v_a_540_);
                                            v___x_642_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_fn_638_, v_fn_640_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
                                            if leanh::lean_obj_tag(v___x_642_) == 0 {
                                                v_a_643_ =
                                                    leanh::lean_ctor_get(v___x_642_, 0);
                                                leanh::lean_inc(v_a_643_);
                                                v___x_644_ =
                                                    (leanh::lean_unbox(v_a_643_) as u8);
                                                leanh::lean_dec(v_a_643_);
                                                if v___x_644_ == 0 {
                                                    leanh::lean_dec_ref(v_arg_641_);
                                                    leanh::lean_dec_ref(v_arg_639_);
                                                    leanh::lean_dec_ref(v_a_540_);
                                                    return v___x_642_;
                                                } else {
                                                    leanh::lean_dec_ref_known(v___x_642_, 1);
                                                    v_a_538_ = v_arg_639_;
                                                    v_b_539_ = v_arg_641_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_arg_641_);
                                                leanh::lean_dec_ref(v_arg_639_);
                                                leanh::lean_dec_ref(v_a_540_);
                                                return v___x_642_;
                                            }
                                        }
                                        10 => {
                                            v_expr_646_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_expr_646_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v_b_539_ = v_expr_646_;
                                            state = 0;
                                            continue;
                                        }
                                        _ => {
                                            v___y_578_ = v___x_637_;
                                            v___y_579_ = v_a_540_;
                                            v___y_580_ = v_a_541_;
                                            v___y_581_ = v_a_542_;
                                            v___y_582_ = v_a_543_;
                                            v___y_583_ = v_a_544_;
                                            state = 4;
                                            continue;
                                        }
                                    },
                                    7 => match leanh::lean_obj_tag(v_b_539_) {
                                        7 => {
                                            v_binderName_648_ =
                                                leanh::lean_ctor_get(v_a_538_, 0);
                                            leanh::lean_inc(v_binderName_648_);
                                            v_binderType_649_ =
                                                leanh::lean_ctor_get(v_a_538_, 1);
                                            leanh::lean_inc_ref(v_binderType_649_);
                                            v_body_650_ = leanh::lean_ctor_get(v_a_538_, 2);
                                            leanh::lean_inc_ref(v_body_650_);
                                            v_binderInfo_651_ = leanh::lean_ctor_get_uint8(
                                                v_a_538_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 3
                                                    + 8)
                                                    as u32,
                                            );
                                            leanh::lean_dec_ref_known(v_a_538_, 3);
                                            v_binderType_652_ =
                                                leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_binderType_652_);
                                            v_body_653_ = leanh::lean_ctor_get(v_b_539_, 2);
                                            leanh::lean_inc_ref(v_body_653_);
                                            leanh::lean_dec_ref_known(v_b_539_, 3);
                                            v_n_547_ = v_binderName_648_;
                                            v_d_u2081_548_ = v_binderType_649_;
                                            v_b_u2081_549_ = v_body_650_;
                                            v_bi_550_ = v_binderInfo_651_;
                                            v_d_u2082_551_ = v_binderType_652_;
                                            v_b_u2082_552_ = v_body_653_;
                                            v___y_553_ = v_a_540_;
                                            v___y_554_ = v_a_541_;
                                            v___y_555_ = v_a_542_;
                                            v___y_556_ = v_a_543_;
                                            v___y_557_ = v_a_544_;
                                            state = 1;
                                            continue;
                                        }
                                        10 => {
                                            v_expr_654_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_expr_654_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v_b_539_ = v_expr_654_;
                                            state = 0;
                                            continue;
                                        }
                                        _ => {
                                            v___y_578_ = v___x_637_;
                                            v___y_579_ = v_a_540_;
                                            v___y_580_ = v_a_541_;
                                            v___y_581_ = v_a_542_;
                                            v___y_582_ = v_a_543_;
                                            v___y_583_ = v_a_544_;
                                            state = 4;
                                            continue;
                                        }
                                    },
                                    6 => match leanh::lean_obj_tag(v_b_539_) {
                                        6 => {
                                            v_binderName_656_ =
                                                leanh::lean_ctor_get(v_a_538_, 0);
                                            leanh::lean_inc(v_binderName_656_);
                                            v_binderType_657_ =
                                                leanh::lean_ctor_get(v_a_538_, 1);
                                            leanh::lean_inc_ref(v_binderType_657_);
                                            v_body_658_ = leanh::lean_ctor_get(v_a_538_, 2);
                                            leanh::lean_inc_ref(v_body_658_);
                                            v_binderInfo_659_ = leanh::lean_ctor_get_uint8(
                                                v_a_538_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 3
                                                    + 8)
                                                    as u32,
                                            );
                                            leanh::lean_dec_ref_known(v_a_538_, 3);
                                            v_binderType_660_ =
                                                leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_binderType_660_);
                                            v_body_661_ = leanh::lean_ctor_get(v_b_539_, 2);
                                            leanh::lean_inc_ref(v_body_661_);
                                            leanh::lean_dec_ref_known(v_b_539_, 3);
                                            v_n_547_ = v_binderName_656_;
                                            v_d_u2081_548_ = v_binderType_657_;
                                            v_b_u2081_549_ = v_body_658_;
                                            v_bi_550_ = v_binderInfo_659_;
                                            v_d_u2082_551_ = v_binderType_660_;
                                            v_b_u2082_552_ = v_body_661_;
                                            v___y_553_ = v_a_540_;
                                            v___y_554_ = v_a_541_;
                                            v___y_555_ = v_a_542_;
                                            v___y_556_ = v_a_543_;
                                            v___y_557_ = v_a_544_;
                                            state = 1;
                                            continue;
                                        }
                                        10 => {
                                            v_expr_662_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_expr_662_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v_b_539_ = v_expr_662_;
                                            state = 0;
                                            continue;
                                        }
                                        _ => {
                                            v___y_578_ = v___x_637_;
                                            v___y_579_ = v_a_540_;
                                            v___y_580_ = v_a_541_;
                                            v___y_581_ = v_a_542_;
                                            v___y_582_ = v_a_543_;
                                            v___y_583_ = v_a_544_;
                                            state = 4;
                                            continue;
                                        }
                                    },
                                    3 => match leanh::lean_obj_tag(v_b_539_) {
                                        3 => {
                                            leanh::lean_dec_ref(v_a_540_);
                                            v_u_664_ = leanh::lean_ctor_get(v_a_538_, 0);
                                            leanh::lean_inc(v_u_664_);
                                            leanh::lean_dec_ref_known(v_a_538_, 1);
                                            v_u_665_ = leanh::lean_ctor_get(v_b_539_, 0);
                                            leanh::lean_inc(v_u_665_);
                                            leanh::lean_dec_ref_known(v_b_539_, 1);
                                            v___x_666_ = l_Lean_Level_isEquiv(v_u_664_, v_u_665_);
                                            leanh::lean_dec(v_u_665_);
                                            leanh::lean_dec(v_u_664_);
                                            v___x_667_ =
                                                leanh::lean_box((v___x_666_) as usize);
                                            v___x_668_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
                                            return v___x_668_;
                                        }
                                        10 => {
                                            v_expr_669_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_expr_669_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v_b_539_ = v_expr_669_;
                                            state = 0;
                                            continue;
                                        }
                                        _ => {
                                            v___y_578_ = v___x_637_;
                                            v___y_579_ = v_a_540_;
                                            v___y_580_ = v_a_541_;
                                            v___y_581_ = v_a_542_;
                                            v___y_582_ = v_a_543_;
                                            v___y_583_ = v_a_544_;
                                            state = 4;
                                            continue;
                                        }
                                    },
                                    4 => match leanh::lean_obj_tag(v_b_539_) {
                                        4 => {
                                            leanh::lean_dec_ref(v_a_540_);
                                            v_declName_671_ =
                                                leanh::lean_ctor_get(v_a_538_, 0);
                                            leanh::lean_inc(v_declName_671_);
                                            v_us_672_ = leanh::lean_ctor_get(v_a_538_, 1);
                                            leanh::lean_inc(v_us_672_);
                                            leanh::lean_dec_ref_known(v_a_538_, 2);
                                            v_declName_673_ =
                                                leanh::lean_ctor_get(v_b_539_, 0);
                                            leanh::lean_inc(v_declName_673_);
                                            v_us_674_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc(v_us_674_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v___x_675_ =
                                                lean_name_eq(v_declName_671_, v_declName_673_);
                                            leanh::lean_dec(v_declName_673_);
                                            leanh::lean_dec(v_declName_671_);
                                            if v___x_675_ == 0 {
                                                leanh::lean_dec(v_us_674_);
                                                leanh::lean_dec(v_us_672_);
                                                v___x_676_ =
                                                    leanh::lean_box((v___x_675_) as usize);
                                                v___x_677_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_677_, 0, v___x_676_,
                                                );
                                                return v___x_677_;
                                            } else {
                                                v___x_678_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_672_, v_us_674_);
                                                leanh::lean_dec(v_us_674_);
                                                leanh::lean_dec(v_us_672_);
                                                v___x_679_ =
                                                    leanh::lean_box((v___x_678_) as usize);
                                                v___x_680_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_680_, 0, v___x_679_,
                                                );
                                                return v___x_680_;
                                            }
                                        }
                                        10 => {
                                            v_expr_681_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_expr_681_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v_b_539_ = v_expr_681_;
                                            state = 0;
                                            continue;
                                        }
                                        _ => {
                                            v___y_578_ = v___x_637_;
                                            v___y_579_ = v_a_540_;
                                            v___y_580_ = v_a_541_;
                                            v___y_581_ = v_a_542_;
                                            v___y_582_ = v_a_543_;
                                            v___y_583_ = v_a_544_;
                                            state = 4;
                                            continue;
                                        }
                                    },
                                    10 => {
                                        v_expr_683_ = leanh::lean_ctor_get(v_a_538_, 1);
                                        leanh::lean_inc_ref(v_expr_683_);
                                        leanh::lean_dec_ref_known(v_a_538_, 2);
                                        v_a_538_ = v_expr_683_;
                                        state = 0;
                                        continue;
                                    }
                                    _ => {
                                        if leanh::lean_obj_tag(v_b_539_) == 10 {
                                            v_expr_685_ = leanh::lean_ctor_get(v_b_539_, 1);
                                            leanh::lean_inc_ref(v_expr_685_);
                                            leanh::lean_dec_ref_known(v_b_539_, 2);
                                            v_b_539_ = v_expr_685_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v___y_578_ = v___x_637_;
                                            v___y_579_ = v_a_540_;
                                            v___y_580_ = v_a_541_;
                                            v___y_581_ = v_a_542_;
                                            v___y_582_ = v_a_543_;
                                            v___y_583_ = v_a_544_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_a_540_);
                                leanh::lean_dec_ref(v_b_539_);
                                leanh::lean_dec_ref(v_a_538_);
                                v___x_687_ = leanh::lean_box((v___x_630_) as usize);
                                v___x_688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_688_, 0, v___x_687_);
                                return v___x_688_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_540_);
                    leanh::lean_dec_ref(v_b_539_);
                    leanh::lean_dec_ref(v_a_538_);
                    v___x_689_ = leanh::lean_box((v___x_630_) as usize);
                    v___x_690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_690_, 0, v___x_689_);
                    return v___x_690_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(
    mut v_a_693_: *mut leanh::LeanObject,
    mut v_b_694_: *mut leanh::LeanObject,
    mut v_a_695_: *mut leanh::LeanObject,
    mut v_a_696_: *mut leanh::LeanObject,
    mut v_a_697_: *mut leanh::LeanObject,
    mut v_a_698_: *mut leanh::LeanObject,
    mut v_a_699_: *mut leanh::LeanObject,
    mut v_a_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(
        v_a_693_, v_b_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_,
    );
    leanh::lean_dec(v_a_699_);
    leanh::lean_dec_ref(v_a_698_);
    leanh::lean_dec(v_a_697_);
    leanh::lean_dec_ref(v_a_696_);
    return v_res_701_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(
    mut v___y_702_: *mut leanh::LeanObject,
    mut v___y_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
    mut v___y_705_: *mut leanh::LeanObject,
    mut v___y_706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_706_);
    return v___x_708_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(
    mut v___y_709_: *mut leanh::LeanObject,
    mut v___y_710_: *mut leanh::LeanObject,
    mut v___y_711_: *mut leanh::LeanObject,
    mut v___y_712_: *mut leanh::LeanObject,
    mut v___y_713_: *mut leanh::LeanObject,
    mut v___y_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
    leanh::lean_dec(v___y_713_);
    leanh::lean_dec_ref(v___y_712_);
    leanh::lean_dec(v___y_711_);
    leanh::lean_dec_ref(v___y_710_);
    leanh::lean_dec_ref(v___y_709_);
    return v_res_715_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
    mut v_a_716_: *mut leanh::LeanObject,
    mut v_b_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_724_: u8 = 0;
    leanh::lean_inc_ref(v_b_717_);
    leanh::lean_inc_ref(v_a_716_);
    v___x_724_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_716_, v_b_717_);
    if v___x_724_ == 0 {
        let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_a_718_);
        v___x_725_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(
            v_a_716_, v_b_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_,
        );
        return v___x_725_;
    } else {
        let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_b_717_);
        leanh::lean_dec_ref(v_a_716_);
        v___x_726_ = leanh::lean_box((v___x_724_) as usize);
        v___x_727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_727_, 0, v___x_726_);
        return v___x_727_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(
    mut v_a_728_: *mut leanh::LeanObject,
    mut v_b_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
    mut v_a_734_: *mut leanh::LeanObject,
    mut v_a_735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_736_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(
        v_a_728_, v_b_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_,
    );
    leanh::lean_dec(v_a_734_);
    leanh::lean_dec_ref(v_a_733_);
    leanh::lean_dec(v_a_732_);
    leanh::lean_dec_ref(v_a_731_);
    leanh::lean_dec_ref(v_a_730_);
    return v_res_736_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_CompatibleTypes(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_CompatibleTypes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
}