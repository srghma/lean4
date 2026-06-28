// Lean compiler output
// Module: Init.Data.Nat.SOM
// Imports: Init.Data.Nat.Linear Init.ByCases Init.Data.List.BasicAux Init.Data.Prod Init.Meta
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_decidableLex___redArg,
};
use crate::r#gen::Init::Data::List::BasicAux::{
    initialize_Init_Data_List_BasicAux, runtime_initialize_Init_Data_List_BasicAux,
};
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Prelude::{l_Nat_decLt___boxed, l_instDecidableEqNat___boxed};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_mul, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_6, lean_box, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Nat_SOM_instInhabitedExpr_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Nat_SOM_instInhabitedExpr_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_SOM_instInhabitedExpr_default___closed__0_value) as *mut LeanObject;
pub static mut l_Nat_SOM_instInhabitedExpr_default: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_SOM_instInhabitedExpr_default___closed__0_value) as *mut LeanObject;
pub static mut l_Nat_SOM_instInhabitedExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_SOM_instInhabitedExpr_default___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0_value:
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
    m_fun: l_Nat_decLt___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Nat_SOM_Expr_ctorIdx(mut v_x_343_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_343_) {
        0 => {
            let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
            v___x_344_ = lean_unsigned_to_nat(0);
            return v___x_344_;
        }
        1 => {
            let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
            v___x_345_ = lean_unsigned_to_nat(1);
            return v___x_345_;
        }
        2 => {
            let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
            v___x_346_ = lean_unsigned_to_nat(2);
            return v___x_346_;
        }
        _ => {
            let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
            v___x_347_ = lean_unsigned_to_nat(3);
            return v___x_347_;
        }
    }
}
pub unsafe fn l_Nat_SOM_Expr_ctorIdx___boxed(mut v_x_348_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_349_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Nat_SOM_Expr_ctorIdx(v_x_348_);
    lean_dec_ref(v_x_348_);
    return v_res_349_;
}
pub unsafe fn l_Nat_SOM_Expr_ctorElim___redArg(
    mut v_t_350_: *mut LeanObject,
    mut v_k_351_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_350_) {
        2 => {
            let mut v_a_352_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_353_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
            v_a_352_ = lean_ctor_get(v_t_350_, 0);
            lean_inc_ref(v_a_352_);
            v_b_353_ = lean_ctor_get(v_t_350_, 1);
            lean_inc_ref(v_b_353_);
            lean_dec_ref_known(v_t_350_, 2);
            v___x_354_ = lean_apply_2(v_k_351_, v_a_352_, v_b_353_);
            return v___x_354_;
        }
        3 => {
            let mut v_a_355_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_356_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
            v_a_355_ = lean_ctor_get(v_t_350_, 0);
            lean_inc_ref(v_a_355_);
            v_b_356_ = lean_ctor_get(v_t_350_, 1);
            lean_inc_ref(v_b_356_);
            lean_dec_ref_known(v_t_350_, 2);
            v___x_357_ = lean_apply_2(v_k_351_, v_a_355_, v_b_356_);
            return v___x_357_;
        }
        _ => {
            let mut v_i_358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            v_i_358_ = lean_ctor_get(v_t_350_, 0);
            lean_inc(v_i_358_);
            lean_dec_ref(v_t_350_);
            v___x_359_ = lean_apply_1(v_k_351_, v_i_358_);
            return v___x_359_;
        }
    }
}
pub unsafe fn l_Nat_SOM_Expr_ctorElim(
    mut v_motive_360_: *mut LeanObject,
    mut v_ctorIdx_361_: *mut LeanObject,
    mut v_t_362_: *mut LeanObject,
    mut v_h_363_: *mut LeanObject,
    mut v_k_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    v___x_365_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_362_, v_k_364_);
    return v___x_365_;
}
pub unsafe fn l_Nat_SOM_Expr_ctorElim___boxed(
    mut v_motive_366_: *mut LeanObject,
    mut v_ctorIdx_367_: *mut LeanObject,
    mut v_t_368_: *mut LeanObject,
    mut v_h_369_: *mut LeanObject,
    mut v_k_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_371_: *mut LeanObject = core::ptr::null_mut();
    v_res_371_ =
        l_Nat_SOM_Expr_ctorElim(v_motive_366_, v_ctorIdx_367_, v_t_368_, v_h_369_, v_k_370_);
    lean_dec(v_ctorIdx_367_);
    return v_res_371_;
}
pub unsafe fn l_Nat_SOM_Expr_num_elim___redArg(
    mut v_t_372_: *mut LeanObject,
    mut v_num_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    v___x_374_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_372_, v_num_373_);
    return v___x_374_;
}
pub unsafe fn l_Nat_SOM_Expr_num_elim(
    mut v_motive_375_: *mut LeanObject,
    mut v_t_376_: *mut LeanObject,
    mut v_h_377_: *mut LeanObject,
    mut v_num_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_379_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_376_, v_num_378_);
    return v___x_379_;
}
pub unsafe fn l_Nat_SOM_Expr_var_elim___redArg(
    mut v_t_380_: *mut LeanObject,
    mut v_var_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    v___x_382_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_380_, v_var_381_);
    return v___x_382_;
}
pub unsafe fn l_Nat_SOM_Expr_var_elim(
    mut v_motive_383_: *mut LeanObject,
    mut v_t_384_: *mut LeanObject,
    mut v_h_385_: *mut LeanObject,
    mut v_var_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_384_, v_var_386_);
    return v___x_387_;
}
pub unsafe fn l_Nat_SOM_Expr_add_elim___redArg(
    mut v_t_388_: *mut LeanObject,
    mut v_add_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_388_, v_add_389_);
    return v___x_390_;
}
pub unsafe fn l_Nat_SOM_Expr_add_elim(
    mut v_motive_391_: *mut LeanObject,
    mut v_t_392_: *mut LeanObject,
    mut v_h_393_: *mut LeanObject,
    mut v_add_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_392_, v_add_394_);
    return v___x_395_;
}
pub unsafe fn l_Nat_SOM_Expr_mul_elim___redArg(
    mut v_t_396_: *mut LeanObject,
    mut v_mul_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_396_, v_mul_397_);
    return v___x_398_;
}
pub unsafe fn l_Nat_SOM_Expr_mul_elim(
    mut v_motive_399_: *mut LeanObject,
    mut v_t_400_: *mut LeanObject,
    mut v_h_401_: *mut LeanObject,
    mut v_mul_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    v___x_403_ = l_Nat_SOM_Expr_ctorElim___redArg(v_t_400_, v_mul_402_);
    return v___x_403_;
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(
    mut v_fuel_408_: *mut LeanObject,
    mut v_m_u2081_409_: *mut LeanObject,
    mut v_m_u2082_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_412_: u8 = 0;
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: u8 = 0;
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_423_: u8 = 0;
    let mut v___x_424_: u8 = 0;
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_unused_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut v_unused_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_447_: u8 = 0;
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_452_: u8 = 0;
    let mut v_unused_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_454_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_411_ = lean_unsigned_to_nat(0);
                v_isZero_412_ = lean_nat_dec_eq(v_fuel_408_, v_zero_411_);
                if v_isZero_412_ == 1 {
                    v___x_413_ = l_List_appendTR___redArg(v_m_u2081_409_, v_m_u2082_410_);
                    return v___x_413_;
                } else {
                    if lean_obj_tag(v_m_u2082_410_) == 0 {
                        return v_m_u2081_409_;
                    } else {
                        if lean_obj_tag(v_m_u2081_409_) == 0 {
                            return v_m_u2082_410_;
                        } else {
                            v_head_414_ = lean_ctor_get(v_m_u2082_410_, 0);
                            v_tail_415_ = lean_ctor_get(v_m_u2082_410_, 1);
                            v_head_416_ = lean_ctor_get(v_m_u2081_409_, 0);
                            v_tail_417_ = lean_ctor_get(v_m_u2081_409_, 1);
                            v_one_418_ = lean_unsigned_to_nat(1);
                            v_n_419_ = lean_nat_sub(v_fuel_408_, v_one_418_);
                            v___x_420_ = l_Nat_blt(v_head_416_, v_head_414_);
                            if v___x_420_ == 0 {
                                lean_inc(v_tail_415_);
                                lean_inc(v_head_414_);
                                v_isSharedCheck_442_ = (!lean_is_exclusive(v_m_u2082_410_)) as u8;
                                if v_isSharedCheck_442_ == 0 {
                                    v_unused_443_ = lean_ctor_get(v_m_u2082_410_, 1);
                                    lean_dec(v_unused_443_);
                                    v_unused_444_ = lean_ctor_get(v_m_u2082_410_, 0);
                                    lean_dec(v_unused_444_);
                                    v___x_422_ = v_m_u2082_410_;
                                    v_isShared_423_ = v_isSharedCheck_442_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_m_u2082_410_);
                                    v___x_422_ = lean_box(0);
                                    v_isShared_423_ = v_isSharedCheck_442_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_inc(v_tail_417_);
                                lean_inc(v_head_416_);
                                v_isSharedCheck_452_ = (!lean_is_exclusive(v_m_u2081_409_)) as u8;
                                if v_isSharedCheck_452_ == 0 {
                                    v_unused_453_ = lean_ctor_get(v_m_u2081_409_, 1);
                                    lean_dec(v_unused_453_);
                                    v_unused_454_ = lean_ctor_get(v_m_u2081_409_, 0);
                                    lean_dec(v_unused_454_);
                                    v___x_446_ = v_m_u2081_409_;
                                    v_isShared_447_ = v_isSharedCheck_452_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_dec(v_m_u2081_409_);
                                    v___x_446_ = lean_box(0);
                                    v_isShared_447_ = v_isSharedCheck_452_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_424_ = l_Nat_blt(v_head_414_, v_head_416_);
                if v___x_424_ == 0 {
                    lean_inc(v_tail_417_);
                    lean_inc(v_head_416_);
                    v_isSharedCheck_435_ = (!lean_is_exclusive(v_m_u2081_409_)) as u8;
                    if v_isSharedCheck_435_ == 0 {
                        v_unused_436_ = lean_ctor_get(v_m_u2081_409_, 1);
                        lean_dec(v_unused_436_);
                        v_unused_437_ = lean_ctor_get(v_m_u2081_409_, 0);
                        lean_dec(v_unused_437_);
                        v___x_426_ = v_m_u2081_409_;
                        v_isShared_427_ = v_isSharedCheck_435_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_u2081_409_);
                        v___x_426_ = lean_box(0);
                        v_isShared_427_ = v_isSharedCheck_435_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_438_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(
                        v_n_419_,
                        v_m_u2081_409_,
                        v_tail_415_,
                    );
                    lean_dec(v_n_419_);
                    if v_isShared_423_ == 0 {
                        lean_ctor_set(v___x_422_, 1, v___x_438_);
                        v___x_440_ = v___x_422_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_441_, 0, v_head_414_);
                        lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
                        v___x_440_ = v_reuseFailAlloc_441_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_428_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(
                    v_n_419_,
                    v_tail_417_,
                    v_tail_415_,
                );
                lean_dec(v_n_419_);
                if v_isShared_427_ == 0 {
                    lean_ctor_set(v___x_426_, 1, v___x_428_);
                    lean_ctor_set(v___x_426_, 0, v_head_414_);
                    v___x_430_ = v___x_426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_434_, 0, v_head_414_);
                    lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_428_);
                    v___x_430_ = v_reuseFailAlloc_434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_423_ == 0 {
                    lean_ctor_set(v___x_422_, 1, v___x_430_);
                    lean_ctor_set(v___x_422_, 0, v_head_416_);
                    v___x_432_ = v___x_422_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_433_, 0, v_head_416_);
                    lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_430_);
                    v___x_432_ = v_reuseFailAlloc_433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_432_;
            }
            5 => {
                return v___x_440_;
            }
            6 => {
                v___x_448_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(
                    v_n_419_,
                    v_tail_417_,
                    v_m_u2082_410_,
                );
                lean_dec(v_n_419_);
                if v_isShared_447_ == 0 {
                    lean_ctor_set(v___x_446_, 1, v___x_448_);
                    v___x_450_ = v___x_446_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_451_, 0, v_head_416_);
                    lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
                    v___x_450_ = v_reuseFailAlloc_451_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go___boxed(
    mut v_fuel_455_: *mut LeanObject,
    mut v_m_u2081_456_: *mut LeanObject,
    mut v_m_u2082_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_458_: *mut LeanObject = core::ptr::null_mut();
    v_res_458_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(
        v_fuel_455_,
        v_m_u2081_456_,
        v_m_u2082_457_,
    );
    lean_dec(v_fuel_455_);
    return v_res_458_;
}
pub unsafe fn l_Nat_SOM_Mon_mul(
    mut v_m_u2081_459_: *mut LeanObject,
    mut v_m_u2082_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = lean_unsigned_to_nat(1000000);
    v___x_462_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(
        v___x_461_,
        v_m_u2081_459_,
        v_m_u2082_460_,
    );
    return v___x_462_;
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(
    mut v_fuel_464_: *mut LeanObject,
    mut v_p_u2081_465_: *mut LeanObject,
    mut v_p_u2082_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_468_: u8 = 0;
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: u8 = 0;
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_485_: u8 = 0;
    let mut v___x_486_: u8 = 0;
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_489_: u8 = 0;
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_503_: u8 = 0;
    let mut v_unused_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_506_: u8 = 0;
    let mut v_unused_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_513_: u8 = 0;
    let mut v_unused_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_523_: u8 = 0;
    let mut v_unused_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_525_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_467_ = lean_unsigned_to_nat(0);
                v_isZero_468_ = lean_nat_dec_eq(v_fuel_464_, v_zero_467_);
                if v_isZero_468_ == 1 {
                    lean_dec(v_fuel_464_);
                    v___x_469_ = l_List_appendTR___redArg(v_p_u2081_465_, v_p_u2082_466_);
                    return v___x_469_;
                } else {
                    if lean_obj_tag(v_p_u2082_466_) == 0 {
                        lean_dec(v_fuel_464_);
                        return v_p_u2081_465_;
                    } else {
                        if lean_obj_tag(v_p_u2081_465_) == 0 {
                            lean_dec(v_fuel_464_);
                            return v_p_u2082_466_;
                        } else {
                            v_head_470_ = lean_ctor_get(v_p_u2081_465_, 0);
                            v_head_471_ = lean_ctor_get(v_p_u2082_466_, 0);
                            lean_inc(v_head_471_);
                            v_tail_472_ = lean_ctor_get(v_p_u2082_466_, 1);
                            v_tail_473_ = lean_ctor_get(v_p_u2081_465_, 1);
                            v_fst_474_ = lean_ctor_get(v_head_470_, 0);
                            v_snd_475_ = lean_ctor_get(v_head_470_, 1);
                            v_fst_476_ = lean_ctor_get(v_head_471_, 0);
                            v_snd_477_ = lean_ctor_get(v_head_471_, 1);
                            v_one_478_ = lean_unsigned_to_nat(1);
                            v_n_479_ = lean_nat_sub(v_fuel_464_, v_one_478_);
                            lean_dec(v_fuel_464_);
                            v___x_480_ = lean_alloc_closure(
                                l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
                                2,
                                0,
                            );
                            v___x_481_ =
                                l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0;
                            lean_inc(v_snd_477_);
                            lean_inc(v_snd_475_);
                            lean_inc_ref(v___x_480_);
                            v___x_482_ = l_List_decidableLex___redArg(
                                v___x_480_, v___x_481_, v_snd_475_, v_snd_477_,
                            );
                            if v___x_482_ == 0 {
                                lean_inc(v_tail_472_);
                                v_isSharedCheck_513_ = (!lean_is_exclusive(v_p_u2082_466_)) as u8;
                                if v_isSharedCheck_513_ == 0 {
                                    v_unused_514_ = lean_ctor_get(v_p_u2082_466_, 1);
                                    lean_dec(v_unused_514_);
                                    v_unused_515_ = lean_ctor_get(v_p_u2082_466_, 0);
                                    lean_dec(v_unused_515_);
                                    v___x_484_ = v_p_u2082_466_;
                                    v_isShared_485_ = v_isSharedCheck_513_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2082_466_);
                                    v___x_484_ = lean_box(0);
                                    v_isShared_485_ = v_isSharedCheck_513_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_inc(v_tail_473_);
                                lean_inc(v_head_470_);
                                lean_dec_ref(v___x_480_);
                                lean_dec(v_head_471_);
                                v_isSharedCheck_523_ = (!lean_is_exclusive(v_p_u2081_465_)) as u8;
                                if v_isSharedCheck_523_ == 0 {
                                    v_unused_524_ = lean_ctor_get(v_p_u2081_465_, 1);
                                    lean_dec(v_unused_524_);
                                    v_unused_525_ = lean_ctor_get(v_p_u2081_465_, 0);
                                    lean_dec(v_unused_525_);
                                    v___x_517_ = v_p_u2081_465_;
                                    v_isShared_518_ = v_isSharedCheck_523_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2081_465_);
                                    v___x_517_ = lean_box(0);
                                    v_isShared_518_ = v_isSharedCheck_523_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_snd_475_);
                lean_inc(v_snd_477_);
                v___x_486_ =
                    l_List_decidableLex___redArg(v___x_480_, v___x_481_, v_snd_477_, v_snd_475_);
                if v___x_486_ == 0 {
                    lean_inc(v_fst_476_);
                    lean_inc(v_snd_475_);
                    lean_inc(v_fst_474_);
                    lean_inc(v_tail_473_);
                    lean_del_object(v___x_484_);
                    v_isSharedCheck_506_ = (!lean_is_exclusive(v_p_u2081_465_)) as u8;
                    if v_isSharedCheck_506_ == 0 {
                        v_unused_507_ = lean_ctor_get(v_p_u2081_465_, 1);
                        lean_dec(v_unused_507_);
                        v_unused_508_ = lean_ctor_get(v_p_u2081_465_, 0);
                        lean_dec(v_unused_508_);
                        v___x_488_ = v_p_u2081_465_;
                        v_isShared_489_ = v_isSharedCheck_506_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_p_u2081_465_);
                        v___x_488_ = lean_box(0);
                        v_isShared_489_ = v_isSharedCheck_506_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_509_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(
                        v_n_479_,
                        v_p_u2081_465_,
                        v_tail_472_,
                    );
                    if v_isShared_485_ == 0 {
                        lean_ctor_set(v___x_484_, 1, v___x_509_);
                        v___x_511_ = v___x_484_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_512_, 0, v_head_471_);
                        lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
                        v___x_511_ = v_reuseFailAlloc_512_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_isSharedCheck_503_ = (!lean_is_exclusive(v_head_471_)) as u8;
                if v_isSharedCheck_503_ == 0 {
                    v_unused_504_ = lean_ctor_get(v_head_471_, 1);
                    lean_dec(v_unused_504_);
                    v_unused_505_ = lean_ctor_get(v_head_471_, 0);
                    lean_dec(v_unused_505_);
                    v___x_491_ = v_head_471_;
                    v_isShared_492_ = v_isSharedCheck_503_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_head_471_);
                    v___x_491_ = lean_box(0);
                    v_isShared_492_ = v_isSharedCheck_503_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_493_ = lean_nat_add(v_fst_474_, v_fst_476_);
                lean_dec(v_fst_476_);
                lean_dec(v_fst_474_);
                v___x_494_ = lean_nat_dec_eq(v___x_493_, v_zero_467_);
                if v___x_494_ == 0 {
                    if v_isShared_492_ == 0 {
                        lean_ctor_set(v___x_491_, 1, v_snd_475_);
                        lean_ctor_set(v___x_491_, 0, v___x_493_);
                        v___x_496_ = v___x_491_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_493_);
                        lean_ctor_set(v_reuseFailAlloc_501_, 1, v_snd_475_);
                        v___x_496_ = v_reuseFailAlloc_501_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_493_);
                    lean_del_object(v___x_491_);
                    lean_del_object(v___x_488_);
                    lean_dec(v_snd_475_);
                    v_fuel_464_ = v_n_479_;
                    v_p_u2081_465_ = v_tail_473_;
                    v_p_u2082_466_ = v_tail_472_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                v___x_497_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(
                    v_n_479_,
                    v_tail_473_,
                    v_tail_472_,
                );
                if v_isShared_489_ == 0 {
                    lean_ctor_set(v___x_488_, 1, v___x_497_);
                    lean_ctor_set(v___x_488_, 0, v___x_496_);
                    v___x_499_ = v___x_488_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_496_);
                    lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_497_);
                    v___x_499_ = v_reuseFailAlloc_500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_499_;
            }
            6 => {
                return v___x_511_;
            }
            7 => {
                v___x_519_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(
                    v_n_479_,
                    v_tail_473_,
                    v_p_u2082_466_,
                );
                if v_isShared_518_ == 0 {
                    lean_ctor_set(v___x_517_, 1, v___x_519_);
                    v___x_521_ = v___x_517_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_522_, 0, v_head_470_);
                    lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
                    v___x_521_ = v_reuseFailAlloc_522_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_SOM_Poly_add(
    mut v_p_u2081_526_: *mut LeanObject,
    mut v_p_u2082_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = lean_unsigned_to_nat(1000000);
    v___x_529_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(
        v___x_528_,
        v_p_u2081_526_,
        v_p_u2082_527_,
    );
    return v___x_529_;
}
pub unsafe fn l_Nat_SOM_Poly_insertSorted(
    mut v_k_530_: *mut LeanObject,
    mut v_m_531_: *mut LeanObject,
    mut v_p_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_543_: u8 = 0;
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_548_: u8 = 0;
    let mut v_unused_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_553_: u8 = 0;
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut v_unused_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_560_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_532_) == 0 {
                    v___x_533_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_533_, 0, v_k_530_);
                    lean_ctor_set(v___x_533_, 1, v_m_531_);
                    v___x_534_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_534_, 0, v___x_533_);
                    lean_ctor_set(v___x_534_, 1, v_p_532_);
                    return v___x_534_;
                } else {
                    v_head_535_ = lean_ctor_get(v_p_532_, 0);
                    lean_inc(v_head_535_);
                    v_tail_536_ = lean_ctor_get(v_p_532_, 1);
                    v_snd_537_ = lean_ctor_get(v_head_535_, 1);
                    v___x_538_ = lean_alloc_closure(
                        l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    v___x_539_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0;
                    lean_inc(v_snd_537_);
                    lean_inc(v_m_531_);
                    v___x_540_ =
                        l_List_decidableLex___redArg(v___x_538_, v___x_539_, v_m_531_, v_snd_537_);
                    if v___x_540_ == 0 {
                        lean_inc(v_tail_536_);
                        v_isSharedCheck_548_ = (!lean_is_exclusive(v_p_532_)) as u8;
                        if v_isSharedCheck_548_ == 0 {
                            v_unused_549_ = lean_ctor_get(v_p_532_, 1);
                            lean_dec(v_unused_549_);
                            v_unused_550_ = lean_ctor_get(v_p_532_, 0);
                            lean_dec(v_unused_550_);
                            v___x_542_ = v_p_532_;
                            v_isShared_543_ = v_isSharedCheck_548_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_p_532_);
                            v___x_542_ = lean_box(0);
                            v_isShared_543_ = v_isSharedCheck_548_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_558_ = (!lean_is_exclusive(v_head_535_)) as u8;
                        if v_isSharedCheck_558_ == 0 {
                            v_unused_559_ = lean_ctor_get(v_head_535_, 1);
                            lean_dec(v_unused_559_);
                            v_unused_560_ = lean_ctor_get(v_head_535_, 0);
                            lean_dec(v_unused_560_);
                            v___x_552_ = v_head_535_;
                            v_isShared_553_ = v_isSharedCheck_558_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_head_535_);
                            v___x_552_ = lean_box(0);
                            v_isShared_553_ = v_isSharedCheck_558_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_544_ = l_Nat_SOM_Poly_insertSorted(v_k_530_, v_m_531_, v_tail_536_);
                if v_isShared_543_ == 0 {
                    lean_ctor_set(v___x_542_, 1, v___x_544_);
                    v___x_546_ = v___x_542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_547_, 0, v_head_535_);
                    lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
                    v___x_546_ = v_reuseFailAlloc_547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_546_;
            }
            3 => {
                if v_isShared_553_ == 0 {
                    lean_ctor_set(v___x_552_, 1, v_m_531_);
                    lean_ctor_set(v___x_552_, 0, v_k_530_);
                    v___x_555_ = v___x_552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_557_, 0, v_k_530_);
                    lean_ctor_set(v_reuseFailAlloc_557_, 1, v_m_531_);
                    v___x_555_ = v_reuseFailAlloc_557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_556_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_556_, 0, v___x_555_);
                lean_ctor_set(v___x_556_, 1, v_p_532_);
                return v___x_556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(
    mut v_k_561_: *mut LeanObject,
    mut v_m_562_: *mut LeanObject,
    mut v_p_563_: *mut LeanObject,
    mut v_acc_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_563_) == 0 {
                    lean_dec(v_m_562_);
                    return v_acc_564_;
                } else {
                    v_head_565_ = lean_ctor_get(v_p_563_, 0);
                    lean_inc(v_head_565_);
                    v_tail_566_ = lean_ctor_get(v_p_563_, 1);
                    lean_inc(v_tail_566_);
                    lean_dec_ref_known(v_p_563_, 2);
                    v_fst_567_ = lean_ctor_get(v_head_565_, 0);
                    lean_inc(v_fst_567_);
                    v_snd_568_ = lean_ctor_get(v_head_565_, 1);
                    lean_inc(v_snd_568_);
                    lean_dec(v_head_565_);
                    v___x_569_ = lean_nat_mul(v_k_561_, v_fst_567_);
                    lean_dec(v_fst_567_);
                    lean_inc(v_m_562_);
                    v___x_570_ = l_Nat_SOM_Mon_mul(v_m_562_, v_snd_568_);
                    v___x_571_ = l_Nat_SOM_Poly_insertSorted(v___x_569_, v___x_570_, v_acc_564_);
                    v_p_563_ = v_tail_566_;
                    v_acc_564_ = v___x_571_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go___boxed(
    mut v_k_573_: *mut LeanObject,
    mut v_m_574_: *mut LeanObject,
    mut v_p_575_: *mut LeanObject,
    mut v_acc_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_577_: *mut LeanObject = core::ptr::null_mut();
    v_res_577_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(
        v_k_573_, v_m_574_, v_p_575_, v_acc_576_,
    );
    lean_dec(v_k_573_);
    return v_res_577_;
}
pub unsafe fn l_Nat_SOM_Poly_mulMon(
    mut v_p_578_: *mut LeanObject,
    mut v_k_579_: *mut LeanObject,
    mut v_m_580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_581_ = lean_box(0);
    v___x_582_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(
        v_k_579_, v_m_580_, v_p_578_, v___x_581_,
    );
    return v___x_582_;
}
pub unsafe fn l_Nat_SOM_Poly_mulMon___boxed(
    mut v_p_583_: *mut LeanObject,
    mut v_k_584_: *mut LeanObject,
    mut v_m_585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_586_: *mut LeanObject = core::ptr::null_mut();
    v_res_586_ = l_Nat_SOM_Poly_mulMon(v_p_583_, v_k_584_, v_m_585_);
    lean_dec(v_k_584_);
    return v_res_586_;
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(
    mut v_p_u2082_587_: *mut LeanObject,
    mut v_p_u2081_588_: *mut LeanObject,
    mut v_acc_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_588_) == 0 {
                    lean_dec(v_p_u2082_587_);
                    return v_acc_589_;
                } else {
                    v_head_590_ = lean_ctor_get(v_p_u2081_588_, 0);
                    lean_inc(v_head_590_);
                    v_tail_591_ = lean_ctor_get(v_p_u2081_588_, 1);
                    lean_inc(v_tail_591_);
                    lean_dec_ref_known(v_p_u2081_588_, 2);
                    v_fst_592_ = lean_ctor_get(v_head_590_, 0);
                    lean_inc(v_fst_592_);
                    v_snd_593_ = lean_ctor_get(v_head_590_, 1);
                    lean_inc(v_snd_593_);
                    lean_dec(v_head_590_);
                    lean_inc(v_p_u2082_587_);
                    v___x_594_ = l_Nat_SOM_Poly_mulMon(v_p_u2082_587_, v_fst_592_, v_snd_593_);
                    lean_dec(v_fst_592_);
                    v___x_595_ = l_Nat_SOM_Poly_add(v_acc_589_, v___x_594_);
                    v_p_u2081_588_ = v_tail_591_;
                    v_acc_589_ = v___x_595_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_SOM_Poly_mul(
    mut v_p_u2081_597_: *mut LeanObject,
    mut v_p_u2082_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_599_ = lean_box(0);
    v___x_600_ = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(
        v_p_u2082_598_,
        v_p_u2081_597_,
        v___x_599_,
    );
    return v___x_600_;
}
pub unsafe fn l_Nat_SOM_Expr_toPoly(mut v_x_601_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_601_) {
        0 => {
            let mut v_i_602_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_604_: u8 = 0;
            v_i_602_ = lean_ctor_get(v_x_601_, 0);
            v___x_603_ = lean_unsigned_to_nat(0);
            v___x_604_ = lean_nat_dec_eq(v_i_602_, v___x_603_);
            if v___x_604_ == 0 {
                let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
                v___x_605_ = lean_box(0);
                lean_inc(v_i_602_);
                v___x_606_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_606_, 0, v_i_602_);
                lean_ctor_set(v___x_606_, 1, v___x_605_);
                v___x_607_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_607_, 0, v___x_606_);
                lean_ctor_set(v___x_607_, 1, v___x_605_);
                return v___x_607_;
            } else {
                let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
                v___x_608_ = lean_box(0);
                return v___x_608_;
            }
        }
        1 => {
            let mut v_v_609_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
            v_v_609_ = lean_ctor_get(v_x_601_, 0);
            v___x_610_ = lean_unsigned_to_nat(1);
            v___x_611_ = lean_box(0);
            lean_inc(v_v_609_);
            v___x_612_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_612_, 0, v_v_609_);
            lean_ctor_set(v___x_612_, 1, v___x_611_);
            v___x_613_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_613_, 0, v___x_610_);
            lean_ctor_set(v___x_613_, 1, v___x_612_);
            v___x_614_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_614_, 0, v___x_613_);
            lean_ctor_set(v___x_614_, 1, v___x_611_);
            return v___x_614_;
        }
        2 => {
            let mut v_a_615_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_616_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
            v_a_615_ = lean_ctor_get(v_x_601_, 0);
            v_b_616_ = lean_ctor_get(v_x_601_, 1);
            v___x_617_ = l_Nat_SOM_Expr_toPoly(v_a_615_);
            v___x_618_ = l_Nat_SOM_Expr_toPoly(v_b_616_);
            v___x_619_ = l_Nat_SOM_Poly_add(v___x_617_, v___x_618_);
            return v___x_619_;
        }
        _ => {
            let mut v_a_620_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_621_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
            v_a_620_ = lean_ctor_get(v_x_601_, 0);
            v_b_621_ = lean_ctor_get(v_x_601_, 1);
            v___x_622_ = l_Nat_SOM_Expr_toPoly(v_a_620_);
            v___x_623_ = l_Nat_SOM_Expr_toPoly(v_b_621_);
            v___x_624_ = l_Nat_SOM_Poly_mul(v___x_622_, v___x_623_);
            return v___x_624_;
        }
    }
}
pub unsafe fn l_Nat_SOM_Expr_toPoly___boxed(mut v_x_625_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_626_: *mut LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Nat_SOM_Expr_toPoly(v_x_625_);
    lean_dec_ref(v_x_625_);
    return v_res_626_;
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(
    mut v_m_u2081_627_: *mut LeanObject,
    mut v_m_u2082_628_: *mut LeanObject,
    mut v_h__1_629_: *mut LeanObject,
    mut v_h__2_630_: *mut LeanObject,
    mut v_h__3_631_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2082_628_) == 0 {
        let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_631_);
        lean_dec(v_h__2_630_);
        v___x_632_ = lean_apply_1(v_h__1_629_, v_m_u2081_627_);
        return v___x_632_;
    } else {
        lean_dec(v_h__1_629_);
        if lean_obj_tag(v_m_u2081_627_) == 0 {
            let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_631_);
            v___x_633_ = lean_apply_2(v_h__2_630_, v_m_u2082_628_, lean_box(0));
            return v___x_633_;
        } else {
            let mut v_head_634_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_635_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_636_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_637_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_630_);
            v_head_634_ = lean_ctor_get(v_m_u2082_628_, 0);
            lean_inc(v_head_634_);
            v_tail_635_ = lean_ctor_get(v_m_u2082_628_, 1);
            lean_inc(v_tail_635_);
            lean_dec_ref_known(v_m_u2082_628_, 2);
            v_head_636_ = lean_ctor_get(v_m_u2081_627_, 0);
            lean_inc(v_head_636_);
            v_tail_637_ = lean_ctor_get(v_m_u2081_627_, 1);
            lean_inc(v_tail_637_);
            lean_dec_ref_known(v_m_u2081_627_, 2);
            v___x_638_ = lean_apply_4(
                v_h__3_631_,
                v_head_636_,
                v_tail_637_,
                v_head_634_,
                v_tail_635_,
            );
            return v___x_638_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(
    mut v_motive_639_: *mut LeanObject,
    mut v_m_u2081_640_: *mut LeanObject,
    mut v_m_u2082_641_: *mut LeanObject,
    mut v_h__1_642_: *mut LeanObject,
    mut v_h__2_643_: *mut LeanObject,
    mut v_h__3_644_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_m_u2082_641_) == 0 {
        let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_644_);
        lean_dec(v_h__2_643_);
        v___x_645_ = lean_apply_1(v_h__1_642_, v_m_u2081_640_);
        return v___x_645_;
    } else {
        lean_dec(v_h__1_642_);
        if lean_obj_tag(v_m_u2081_640_) == 0 {
            let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_644_);
            v___x_646_ = lean_apply_2(v_h__2_643_, v_m_u2082_641_, lean_box(0));
            return v___x_646_;
        } else {
            let mut v_head_647_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_648_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_649_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_650_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_643_);
            v_head_647_ = lean_ctor_get(v_m_u2082_641_, 0);
            lean_inc(v_head_647_);
            v_tail_648_ = lean_ctor_get(v_m_u2082_641_, 1);
            lean_inc(v_tail_648_);
            lean_dec_ref_known(v_m_u2082_641_, 2);
            v_head_649_ = lean_ctor_get(v_m_u2081_640_, 0);
            lean_inc(v_head_649_);
            v_tail_650_ = lean_ctor_get(v_m_u2081_640_, 1);
            lean_inc(v_tail_650_);
            lean_dec_ref_known(v_m_u2081_640_, 2);
            v___x_651_ = lean_apply_4(
                v_h__3_644_,
                v_head_649_,
                v_tail_650_,
                v_head_647_,
                v_tail_648_,
            );
            return v___x_651_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(
    mut v_p_u2081_652_: *mut LeanObject,
    mut v_p_u2082_653_: *mut LeanObject,
    mut v_h__1_654_: *mut LeanObject,
    mut v_h__2_655_: *mut LeanObject,
    mut v_h__3_656_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2082_653_) == 0 {
        let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_656_);
        lean_dec(v_h__2_655_);
        v___x_657_ = lean_apply_1(v_h__1_654_, v_p_u2081_652_);
        return v___x_657_;
    } else {
        lean_dec(v_h__1_654_);
        if lean_obj_tag(v_p_u2081_652_) == 0 {
            let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_656_);
            v___x_658_ = lean_apply_2(v_h__2_655_, v_p_u2082_653_, lean_box(0));
            return v___x_658_;
        } else {
            let mut v_head_659_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_660_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_661_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_662_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_663_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_664_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_665_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_666_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_655_);
            v_head_659_ = lean_ctor_get(v_p_u2081_652_, 0);
            lean_inc(v_head_659_);
            v_head_660_ = lean_ctor_get(v_p_u2082_653_, 0);
            lean_inc(v_head_660_);
            v_tail_661_ = lean_ctor_get(v_p_u2082_653_, 1);
            lean_inc(v_tail_661_);
            lean_dec_ref_known(v_p_u2082_653_, 2);
            v_tail_662_ = lean_ctor_get(v_p_u2081_652_, 1);
            lean_inc(v_tail_662_);
            lean_dec_ref_known(v_p_u2081_652_, 2);
            v_fst_663_ = lean_ctor_get(v_head_659_, 0);
            lean_inc(v_fst_663_);
            v_snd_664_ = lean_ctor_get(v_head_659_, 1);
            lean_inc(v_snd_664_);
            lean_dec(v_head_659_);
            v_fst_665_ = lean_ctor_get(v_head_660_, 0);
            lean_inc(v_fst_665_);
            v_snd_666_ = lean_ctor_get(v_head_660_, 1);
            lean_inc(v_snd_666_);
            lean_dec(v_head_660_);
            v___x_667_ = lean_apply_6(
                v_h__3_656_,
                v_fst_663_,
                v_snd_664_,
                v_tail_662_,
                v_fst_665_,
                v_snd_666_,
                v_tail_661_,
            );
            return v___x_667_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(
    mut v_motive_668_: *mut LeanObject,
    mut v_p_u2081_669_: *mut LeanObject,
    mut v_p_u2082_670_: *mut LeanObject,
    mut v_h__1_671_: *mut LeanObject,
    mut v_h__2_672_: *mut LeanObject,
    mut v_h__3_673_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2082_670_) == 0 {
        let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_673_);
        lean_dec(v_h__2_672_);
        v___x_674_ = lean_apply_1(v_h__1_671_, v_p_u2081_669_);
        return v___x_674_;
    } else {
        lean_dec(v_h__1_671_);
        if lean_obj_tag(v_p_u2081_669_) == 0 {
            let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_673_);
            v___x_675_ = lean_apply_2(v_h__2_672_, v_p_u2082_670_, lean_box(0));
            return v___x_675_;
        } else {
            let mut v_head_676_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_677_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_678_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_679_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_680_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_681_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_682_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_683_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_672_);
            v_head_676_ = lean_ctor_get(v_p_u2081_669_, 0);
            lean_inc(v_head_676_);
            v_head_677_ = lean_ctor_get(v_p_u2082_670_, 0);
            lean_inc(v_head_677_);
            v_tail_678_ = lean_ctor_get(v_p_u2082_670_, 1);
            lean_inc(v_tail_678_);
            lean_dec_ref_known(v_p_u2082_670_, 2);
            v_tail_679_ = lean_ctor_get(v_p_u2081_669_, 1);
            lean_inc(v_tail_679_);
            lean_dec_ref_known(v_p_u2081_669_, 2);
            v_fst_680_ = lean_ctor_get(v_head_676_, 0);
            lean_inc(v_fst_680_);
            v_snd_681_ = lean_ctor_get(v_head_676_, 1);
            lean_inc(v_snd_681_);
            lean_dec(v_head_676_);
            v_fst_682_ = lean_ctor_get(v_head_677_, 0);
            lean_inc(v_fst_682_);
            v_snd_683_ = lean_ctor_get(v_head_677_, 1);
            lean_inc(v_snd_683_);
            lean_dec(v_head_677_);
            v___x_684_ = lean_apply_6(
                v_h__3_673_,
                v_fst_680_,
                v_snd_681_,
                v_tail_679_,
                v_fst_682_,
                v_snd_683_,
                v_tail_678_,
            );
            return v___x_684_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_SOM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_SOM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_SOM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_SOM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_SOM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_SOM(builtin);
}
