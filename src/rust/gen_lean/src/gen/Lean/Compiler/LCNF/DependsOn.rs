// Lean compiler output
// Module: Lean.Compiler.LCNF.DependsOn
// Imports: Lean.Compiler.LCNF.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_uget_borrowed, lean_nat_dec_lt, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasFVar;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(
    mut v_k_410_: *mut crate::leanh::LeanObject,
    mut v_t_411_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_417_: u8 = 0;
    let mut v___x_419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_411_) == 0 {
                    v_k_412_ = crate::leanh::lean_ctor_get(v_t_411_, 1);
                    v_l_413_ = crate::leanh::lean_ctor_get(v_t_411_, 3);
                    v_r_414_ = crate::leanh::lean_ctor_get(v_t_411_, 4);
                    v___x_415_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_410_, v_k_412_);
                    match v___x_415_ {
                        0 => {
                            v_t_411_ = v_l_413_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_417_ = 1;
                            return v___x_417_;
                        }
                        _ => {
                            v_t_411_ = v_r_414_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_419_ = 0;
                    return v___x_419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg___boxed(
    mut v_k_420_: *mut crate::leanh::LeanObject,
    mut v_t_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_422_: u8 = 0;
    let mut v_r_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_422_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_420_, v_t_421_);
    crate::leanh::lean_dec(v_t_421_);
    crate::leanh::lean_dec(v_k_420_);
    v_r_423_ = crate::leanh::lean_box((v_res_422_) as usize);
    return v_r_423_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(
    mut v_fvarId_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_426_: u8 = 0;
    v___x_426_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_424_, v_a_425_);
    return v___x_426_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___boxed(
    mut v_fvarId_427_: *mut crate::leanh::LeanObject,
    mut v_a_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_429_: u8 = 0;
    let mut v_r_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(
        v_fvarId_427_,
        v_a_428_,
    );
    crate::leanh::lean_dec(v_a_428_);
    crate::leanh::lean_dec(v_fvarId_427_);
    v_r_430_ = crate::leanh::lean_box((v_res_429_) as usize);
    return v_r_430_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(
    mut v_00_u03b2_431_: *mut crate::leanh::LeanObject,
    mut v_k_432_: *mut crate::leanh::LeanObject,
    mut v_t_433_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_434_: u8 = 0;
    v___x_434_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_432_, v_t_433_);
    return v___x_434_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___boxed(
    mut v_00_u03b2_435_: *mut crate::leanh::LeanObject,
    mut v_k_436_: *mut crate::leanh::LeanObject,
    mut v_t_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_438_: u8 = 0;
    let mut v_r_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(v_00_u03b2_435_, v_k_436_, v_t_437_);
    crate::leanh::lean_dec(v_t_437_);
    crate::leanh::lean_dec(v_k_436_);
    v_r_439_ = crate::leanh::lean_box((v_res_438_) as usize);
    return v_r_439_;
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_e_441_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_442_: u8 = 0;
    let mut v_d_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u8 = 0;
    let mut v_binderType_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    let mut v___x_458_: u8 = 0;
    let mut v_fn_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: u8 = 0;
    let mut v_struct_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut v___x_468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_442_ = l_Lean_Expr_hasFVar(v_e_441_);
                if v___x_442_ == 0 {
                    return v___x_442_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_441_) {
                        7 => {
                            v_binderType_448_ = crate::leanh::lean_ctor_get(v_e_441_, 1);
                            v_body_449_ = crate::leanh::lean_ctor_get(v_e_441_, 2);
                            v_d_444_ = v_binderType_448_;
                            v_b_445_ = v_body_449_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_450_ = crate::leanh::lean_ctor_get(v_e_441_, 1);
                            v_body_451_ = crate::leanh::lean_ctor_get(v_e_441_, 2);
                            v_d_444_ = v_binderType_450_;
                            v_b_445_ = v_body_451_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_452_ = crate::leanh::lean_ctor_get(v_e_441_, 1);
                            v_e_441_ = v_expr_452_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_454_ = crate::leanh::lean_ctor_get(v_e_441_, 1);
                            v_value_455_ = crate::leanh::lean_ctor_get(v_e_441_, 2);
                            v_body_456_ = crate::leanh::lean_ctor_get(v_e_441_, 3);
                            v___x_457_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_440_, v_type_454_);
                            if v___x_457_ == 0 {
                                v___x_458_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_440_, v_value_455_);
                                if v___x_458_ == 0 {
                                    v_e_441_ = v_body_456_;
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_442_;
                                }
                            } else {
                                return v___x_442_;
                            }
                        }
                        5 => {
                            v_fn_460_ = crate::leanh::lean_ctor_get(v_e_441_, 0);
                            v_arg_461_ = crate::leanh::lean_ctor_get(v_e_441_, 1);
                            v___x_462_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_440_, v_fn_460_);
                            if v___x_462_ == 0 {
                                v_e_441_ = v_arg_461_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_442_;
                            }
                        }
                        11 => {
                            v_struct_464_ = crate::leanh::lean_ctor_get(v_e_441_, 2);
                            v_e_441_ = v_struct_464_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_fvarId_466_ = crate::leanh::lean_ctor_get(v_e_441_, 0);
                            v___x_467_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_466_, v_a_440_);
                            return v___x_467_;
                        }
                        _ => {
                            v___x_468_ = 0;
                            return v___x_468_;
                        }
                    }
                }
            }
            1 => {
                v___x_446_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_440_, v_d_444_);
                if v___x_446_ == 0 {
                    v_e_441_ = v_b_445_;
                    state = 0;
                    continue;
                } else {
                    return v___x_442_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0___boxed(
    mut v_a_469_: *mut crate::leanh::LeanObject,
    mut v_e_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_471_: u8 = 0;
    let mut v_r_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_471_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_469_, v_e_470_);
    crate::leanh::lean_dec_ref(v_e_470_);
    crate::leanh::lean_dec(v_a_469_);
    v_r_472_ = crate::leanh::lean_box((v_res_471_) as usize);
    return v_r_472_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(
    mut v_e_473_: *mut crate::leanh::LeanObject,
    mut v_a_474_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_475_: u8 = 0;
    v___x_475_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_474_, v_e_473_);
    return v___x_475_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn___boxed(
    mut v_e_476_: *mut crate::leanh::LeanObject,
    mut v_a_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: u8 = 0;
    let mut v_r_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(
        v_e_476_, v_a_477_,
    );
    crate::leanh::lean_dec(v_a_477_);
    crate::leanh::lean_dec_ref(v_e_476_);
    v_r_479_ = crate::leanh::lean_box((v_res_478_) as usize);
    return v_r_479_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(
    mut v_a_480_: *mut crate::leanh::LeanObject,
    mut v_a_481_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_a_480_) {
        0 => {
            let mut v___x_482_: u8 = 0;
            v___x_482_ = 0;
            return v___x_482_;
        }
        1 => {
            let mut v_fvarId_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: u8 = 0;
            v_fvarId_483_ = crate::leanh::lean_ctor_get(v_a_480_, 0);
            v___x_484_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_483_, v_a_481_);
            return v___x_484_;
        }
        _ => {
            let mut v_expr_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_486_: u8 = 0;
            v_expr_485_ = crate::leanh::lean_ctor_get(v_a_480_, 0);
            v___x_486_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_481_, v_expr_485_);
            return v___x_486_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg___boxed(
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_489_: u8 = 0;
    let mut v_r_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_489_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(
        v_a_487_, v_a_488_,
    );
    crate::leanh::lean_dec(v_a_488_);
    crate::leanh::lean_dec(v_a_487_);
    v_r_490_ = crate::leanh::lean_box((v_res_489_) as usize);
    return v_r_490_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(
    mut v_pu_491_: u8,
    mut v_a_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_494_: u8 = 0;
    v___x_494_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(
        v_a_492_, v_a_493_,
    );
    return v___x_494_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___boxed(
    mut v_pu_495_: *mut crate::leanh::LeanObject,
    mut v_a_496_: *mut crate::leanh::LeanObject,
    mut v_a_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_498_: u8 = 0;
    let mut v_res_499_: u8 = 0;
    let mut v_r_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_498_ = (crate::leanh::lean_unbox(v_pu_495_) as u8);
    v_res_499_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(
        v_pu_boxed_498_,
        v_a_496_,
        v_a_497_,
    );
    crate::leanh::lean_dec(v_a_497_);
    crate::leanh::lean_dec(v_a_496_);
    v_r_500_ = crate::leanh::lean_box((v_res_499_) as usize);
    return v_r_500_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(
    mut v_as_501_: *mut crate::leanh::LeanObject,
    mut v_i_502_: usize,
    mut v_stop_503_: usize,
    mut v___y_504_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: u8 = 0;
    let mut v___x_508_: usize = 0;
    let mut v___x_509_: usize = 0;
    let mut v___x_511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_505_ = lean_usize_dec_eq(v_i_502_, v_stop_503_);
                if v___x_505_ == 0 {
                    v___x_506_ = lean_array_uget_borrowed(v_as_501_, v_i_502_);
                    v___x_507_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v___x_506_, v___y_504_);
                    if v___x_507_ == 0 {
                        v___x_508_ = 1usize;
                        v___x_509_ = lean_usize_add(v_i_502_, v___x_508_);
                        v_i_502_ = v___x_509_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_507_;
                    }
                } else {
                    v___x_511_ = 0;
                    return v___x_511_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg___boxed(
    mut v_as_512_: *mut crate::leanh::LeanObject,
    mut v_i_513_: *mut crate::leanh::LeanObject,
    mut v_stop_514_: *mut crate::leanh::LeanObject,
    mut v___y_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_516_: usize = 0;
    let mut v_stop_boxed_517_: usize = 0;
    let mut v_res_518_: u8 = 0;
    let mut v_r_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_516_ = crate::leanh::lean_unbox_usize(v_i_513_);
    crate::leanh::lean_dec(v_i_513_);
    v_stop_boxed_517_ = crate::leanh::lean_unbox_usize(v_stop_514_);
    crate::leanh::lean_dec(v_stop_514_);
    v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_512_, v_i_boxed_516_, v_stop_boxed_517_, v___y_515_);
    crate::leanh::lean_dec(v___y_515_);
    crate::leanh::lean_dec_ref(v_as_512_);
    v_r_519_ = crate::leanh::lean_box((v_res_518_) as usize);
    return v_r_519_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(
    mut v_pu_520_: u8,
    mut v_e_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_args_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: u8 = 0;
    let mut v___x_529_: usize = 0;
    let mut v___x_530_: usize = 0;
    let mut v___x_531_: u8 = 0;
    let mut v_struct_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v_args_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: usize = 0;
    let mut v___x_539_: usize = 0;
    let mut v___x_540_: u8 = 0;
    let mut v_fvarId_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: u8 = 0;
    let mut v___x_547_: usize = 0;
    let mut v___x_548_: usize = 0;
    let mut v___x_549_: u8 = 0;
    let mut v_args_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: usize = 0;
    let mut v___x_555_: usize = 0;
    let mut v___x_556_: u8 = 0;
    let mut v_var_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: u8 = 0;
    let mut v_var_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut v_var_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: u8 = 0;
    let mut v_args_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: u8 = 0;
    let mut v_var_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: u8 = 0;
    let mut v___x_573_: usize = 0;
    let mut v___x_574_: usize = 0;
    let mut v___x_575_: u8 = 0;
    let mut v_fvarId_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: u8 = 0;
    let mut v_fvarId_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v_fvarId_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_521_) {
                2 => {
                    v_struct_532_ = crate::leanh::lean_ctor_get(v_e_521_, 2);
                    v___x_533_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_struct_532_, v_a_522_);
                    return v___x_533_;
                }
                3 => {
                    v_args_534_ = crate::leanh::lean_ctor_get(v_e_521_, 2);
                    v___x_535_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_536_ = lean_array_get_size(v_args_534_);
                    v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
                    if v___x_537_ == 0 {
                        return v___x_537_;
                    } else {
                        if v___x_537_ == 0 {
                            return v___x_537_;
                        } else {
                            v___x_538_ = 0usize;
                            v___x_539_ = lean_usize_of_nat(v___x_536_);
                            v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_534_, v___x_538_, v___x_539_, v_a_522_);
                            return v___x_540_;
                        }
                    }
                }
                4 => {
                    v_fvarId_541_ = crate::leanh::lean_ctor_get(v_e_521_, 0);
                    v_args_542_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v___x_543_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_541_, v_a_522_);
                    if v___x_543_ == 0 {
                        v___x_544_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_545_ = lean_array_get_size(v_args_542_);
                        v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
                        if v___x_546_ == 0 {
                            return v___x_543_;
                        } else {
                            if v___x_546_ == 0 {
                                return v___x_543_;
                            } else {
                                v___x_547_ = 0usize;
                                v___x_548_ = lean_usize_of_nat(v___x_545_);
                                v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_542_, v___x_547_, v___x_548_, v_a_522_);
                                return v___x_549_;
                            }
                        }
                    } else {
                        return v___x_543_;
                    }
                }
                5 => {
                    v_args_550_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v___x_551_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_552_ = lean_array_get_size(v_args_550_);
                    v___x_553_ = lean_nat_dec_lt(v___x_551_, v___x_552_);
                    if v___x_553_ == 0 {
                        return v___x_553_;
                    } else {
                        if v___x_553_ == 0 {
                            return v___x_553_;
                        } else {
                            v___x_554_ = 0usize;
                            v___x_555_ = lean_usize_of_nat(v___x_552_);
                            v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_550_, v___x_554_, v___x_555_, v_a_522_);
                            return v___x_556_;
                        }
                    }
                }
                6 => {
                    v_var_557_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v___x_558_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_557_, v_a_522_);
                    return v___x_558_;
                }
                7 => {
                    v_var_559_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v___x_560_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_559_, v_a_522_);
                    return v___x_560_;
                }
                8 => {
                    v_var_561_ = crate::leanh::lean_ctor_get(v_e_521_, 2);
                    v___x_562_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_561_, v_a_522_);
                    return v___x_562_;
                }
                9 => {
                    v_args_563_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v_args_524_ = v_args_563_;
                    v___y_525_ = v_a_522_;
                    state = 1;
                    continue;
                }
                10 => {
                    v_args_564_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v_args_524_ = v_args_564_;
                    v___y_525_ = v_a_522_;
                    state = 1;
                    continue;
                }
                11 => {
                    v_var_565_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v___x_566_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_565_, v_a_522_);
                    return v___x_566_;
                }
                12 => {
                    v_var_567_ = crate::leanh::lean_ctor_get(v_e_521_, 0);
                    v_args_568_ = crate::leanh::lean_ctor_get(v_e_521_, 2);
                    v___x_569_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_567_, v_a_522_);
                    if v___x_569_ == 0 {
                        v___x_570_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_571_ = lean_array_get_size(v_args_568_);
                        v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
                        if v___x_572_ == 0 {
                            return v___x_569_;
                        } else {
                            if v___x_572_ == 0 {
                                return v___x_569_;
                            } else {
                                v___x_573_ = 0usize;
                                v___x_574_ = lean_usize_of_nat(v___x_571_);
                                v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_568_, v___x_573_, v___x_574_, v_a_522_);
                                return v___x_575_;
                            }
                        }
                    } else {
                        return v___x_569_;
                    }
                }
                13 => {
                    v_fvarId_576_ = crate::leanh::lean_ctor_get(v_e_521_, 1);
                    v___x_577_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_576_, v_a_522_);
                    return v___x_577_;
                }
                14 => {
                    v_fvarId_578_ = crate::leanh::lean_ctor_get(v_e_521_, 0);
                    v___x_579_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_578_, v_a_522_);
                    return v___x_579_;
                }
                15 => {
                    v_fvarId_580_ = crate::leanh::lean_ctor_get(v_e_521_, 0);
                    v___x_581_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_580_, v_a_522_);
                    return v___x_581_;
                }
                _ => {
                    v___x_582_ = 0;
                    return v___x_582_;
                }
            },
            1 => {
                v___x_526_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_527_ = lean_array_get_size(v_args_524_);
                v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
                if v___x_528_ == 0 {
                    return v___x_528_;
                } else {
                    if v___x_528_ == 0 {
                        return v___x_528_;
                    } else {
                        v___x_529_ = 0usize;
                        v___x_530_ = lean_usize_of_nat(v___x_527_);
                        v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_524_, v___x_529_, v___x_530_, v___y_525_);
                        return v___x_531_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn___boxed(
    mut v_pu_583_: *mut crate::leanh::LeanObject,
    mut v_e_584_: *mut crate::leanh::LeanObject,
    mut v_a_585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_586_: u8 = 0;
    let mut v_res_587_: u8 = 0;
    let mut v_r_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_586_ = (crate::leanh::lean_unbox(v_pu_583_) as u8);
    v_res_587_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(
        v_pu_boxed_586_,
        v_e_584_,
        v_a_585_,
    );
    crate::leanh::lean_dec(v_a_585_);
    crate::leanh::lean_dec(v_e_584_);
    v_r_588_ = crate::leanh::lean_box((v_res_587_) as usize);
    return v_r_588_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(
    mut v_pu_589_: u8,
    mut v_as_590_: *mut crate::leanh::LeanObject,
    mut v_i_591_: usize,
    mut v_stop_592_: usize,
    mut v___y_593_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_594_: u8 = 0;
    v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_590_, v_i_591_, v_stop_592_, v___y_593_);
    return v___x_594_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___boxed(
    mut v_pu_595_: *mut crate::leanh::LeanObject,
    mut v_as_596_: *mut crate::leanh::LeanObject,
    mut v_i_597_: *mut crate::leanh::LeanObject,
    mut v_stop_598_: *mut crate::leanh::LeanObject,
    mut v___y_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_600_: u8 = 0;
    let mut v_i_boxed_601_: usize = 0;
    let mut v_stop_boxed_602_: usize = 0;
    let mut v_res_603_: u8 = 0;
    let mut v_r_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_600_ = (crate::leanh::lean_unbox(v_pu_595_) as u8);
    v_i_boxed_601_ = crate::leanh::lean_unbox_usize(v_i_597_);
    crate::leanh::lean_dec(v_i_597_);
    v_stop_boxed_602_ = crate::leanh::lean_unbox_usize(v_stop_598_);
    crate::leanh::lean_dec(v_stop_598_);
    v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(v_pu_boxed_600_, v_as_596_, v_i_boxed_601_, v_stop_boxed_602_, v___y_599_);
    crate::leanh::lean_dec(v___y_599_);
    crate::leanh::lean_dec_ref(v_as_596_);
    v_r_604_ = crate::leanh::lean_box((v_res_603_) as usize);
    return v_r_604_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(
    mut v_pu_605_: u8,
    mut v_decl_606_: *mut crate::leanh::LeanObject,
    mut v_a_607_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_type_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    v_type_608_ = crate::leanh::lean_ctor_get(v_decl_606_, 2);
    v_value_609_ = crate::leanh::lean_ctor_get(v_decl_606_, 3);
    v___x_610_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_607_, v_type_608_);
    if v___x_610_ == 0 {
        let mut v___x_611_: u8 = 0;
        v___x_611_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(
            v_pu_605_,
            v_value_609_,
            v_a_607_,
        );
        return v___x_611_;
    } else {
        return v___x_610_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn___boxed(
    mut v_pu_612_: *mut crate::leanh::LeanObject,
    mut v_decl_613_: *mut crate::leanh::LeanObject,
    mut v_a_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_615_: u8 = 0;
    let mut v_res_616_: u8 = 0;
    let mut v_r_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_615_ = (crate::leanh::lean_unbox(v_pu_612_) as u8);
    v_res_616_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(
        v_pu_boxed_615_,
        v_decl_613_,
        v_a_614_,
    );
    crate::leanh::lean_dec(v_a_614_);
    crate::leanh::lean_dec_ref(v_decl_613_);
    v_r_617_ = crate::leanh::lean_box((v_res_616_) as usize);
    return v_r_617_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
    mut v_pu_618_: u8,
    mut v_c_619_: *mut crate::leanh::LeanObject,
    mut v_a_620_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_decl_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    let mut v_fvarId_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: usize = 0;
    let mut v___x_632_: usize = 0;
    let mut v___x_633_: u8 = 0;
    let mut v_cases_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v___x_639_: u8 = 0;
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: usize = 0;
    let mut v___x_644_: usize = 0;
    let mut v___x_645_: u8 = 0;
    let mut v_fvarId_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v_fvarId_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: u8 = 0;
    let mut v_fvarId_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: u8 = 0;
    let mut v_fvarId_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: u8 = 0;
    let mut v_fvarId_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v_fvarId_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: u8 = 0;
    let mut v_fvarId_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v_fvarId_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v_decl_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_c_619_) {
                    0 => {
                        v_decl_621_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_k_622_ = crate::leanh::lean_ctor_get(v_c_619_, 1);
                        v___x_623_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_618_, v_decl_621_, v_a_620_);
                        if v___x_623_ == 0 {
                            v_c_619_ = v_k_622_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_623_;
                        }
                    }
                    3 => {
                        v_fvarId_625_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_args_626_ = crate::leanh::lean_ctor_get(v_c_619_, 1);
                        v___x_627_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_625_, v_a_620_);
                        if v___x_627_ == 0 {
                            v___x_628_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_629_ = lean_array_get_size(v_args_626_);
                            v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
                            if v___x_630_ == 0 {
                                return v___x_627_;
                            } else {
                                if v___x_630_ == 0 {
                                    return v___x_627_;
                                } else {
                                    v___x_631_ = 0usize;
                                    v___x_632_ = lean_usize_of_nat(v___x_629_);
                                    v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_626_, v___x_631_, v___x_632_, v_a_620_);
                                    return v___x_633_;
                                }
                            }
                        } else {
                            return v___x_627_;
                        }
                    }
                    4 => {
                        v_cases_634_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_resultType_635_ = crate::leanh::lean_ctor_get(v_cases_634_, 1);
                        v_discr_636_ = crate::leanh::lean_ctor_get(v_cases_634_, 2);
                        v_alts_637_ = crate::leanh::lean_ctor_get(v_cases_634_, 3);
                        v___x_638_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_620_, v_resultType_635_);
                        if v___x_638_ == 0 {
                            v___x_639_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_discr_636_, v_a_620_);
                            if v___x_639_ == 0 {
                                v___x_640_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_641_ = lean_array_get_size(v_alts_637_);
                                v___x_642_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
                                if v___x_642_ == 0 {
                                    return v___x_639_;
                                } else {
                                    if v___x_642_ == 0 {
                                        return v___x_639_;
                                    } else {
                                        v___x_643_ = 0usize;
                                        v___x_644_ = lean_usize_of_nat(v___x_641_);
                                        v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_618_, v_alts_637_, v___x_643_, v___x_644_, v_a_620_);
                                        return v___x_645_;
                                    }
                                }
                            } else {
                                return v___x_639_;
                            }
                        } else {
                            return v___x_638_;
                        }
                    }
                    5 => {
                        v_fvarId_646_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v___x_647_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_646_, v_a_620_);
                        return v___x_647_;
                    }
                    6 => {
                        v___x_648_ = 0;
                        return v___x_648_;
                    }
                    7 => {
                        v_fvarId_649_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_y_650_ = crate::leanh::lean_ctor_get(v_c_619_, 2);
                        v_k_651_ = crate::leanh::lean_ctor_get(v_c_619_, 3);
                        v___x_652_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_649_, v_a_620_);
                        if v___x_652_ == 0 {
                            v___x_653_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_650_, v_a_620_);
                            if v___x_653_ == 0 {
                                v_c_619_ = v_k_651_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_653_;
                            }
                        } else {
                            return v___x_652_;
                        }
                    }
                    8 => {
                        v_fvarId_655_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_y_656_ = crate::leanh::lean_ctor_get(v_c_619_, 2);
                        v_k_657_ = crate::leanh::lean_ctor_get(v_c_619_, 3);
                        v___x_658_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_655_, v_a_620_);
                        if v___x_658_ == 0 {
                            v___x_659_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_656_, v_a_620_);
                            if v___x_659_ == 0 {
                                v_c_619_ = v_k_657_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_659_;
                            }
                        } else {
                            return v___x_658_;
                        }
                    }
                    9 => {
                        v_fvarId_661_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_y_662_ = crate::leanh::lean_ctor_get(v_c_619_, 3);
                        v_k_663_ = crate::leanh::lean_ctor_get(v_c_619_, 5);
                        v___x_664_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_661_, v_a_620_);
                        if v___x_664_ == 0 {
                            v___x_665_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_662_, v_a_620_);
                            if v___x_665_ == 0 {
                                v_c_619_ = v_k_663_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_665_;
                            }
                        } else {
                            return v___x_664_;
                        }
                    }
                    10 => {
                        v_fvarId_667_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_k_668_ = crate::leanh::lean_ctor_get(v_c_619_, 2);
                        v___x_669_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_667_, v_a_620_);
                        if v___x_669_ == 0 {
                            v_c_619_ = v_k_668_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_669_;
                        }
                    }
                    11 => {
                        v_fvarId_671_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_k_672_ = crate::leanh::lean_ctor_get(v_c_619_, 2);
                        v___x_673_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_671_, v_a_620_);
                        if v___x_673_ == 0 {
                            v_c_619_ = v_k_672_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_673_;
                        }
                    }
                    12 => {
                        v_fvarId_675_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_k_676_ = crate::leanh::lean_ctor_get(v_c_619_, 3);
                        v___x_677_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_675_, v_a_620_);
                        if v___x_677_ == 0 {
                            v_c_619_ = v_k_676_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_677_;
                        }
                    }
                    13 => {
                        v_fvarId_679_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_k_680_ = crate::leanh::lean_ctor_get(v_c_619_, 1);
                        v___x_681_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_679_, v_a_620_);
                        if v___x_681_ == 0 {
                            v_c_619_ = v_k_680_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_681_;
                        }
                    }
                    _ => {
                        v_decl_683_ = crate::leanh::lean_ctor_get(v_c_619_, 0);
                        v_k_684_ = crate::leanh::lean_ctor_get(v_c_619_, 1);
                        v_type_685_ = crate::leanh::lean_ctor_get(v_decl_683_, 3);
                        v_value_686_ = crate::leanh::lean_ctor_get(v_decl_683_, 4);
                        v___x_687_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_620_, v_type_685_);
                        if v___x_687_ == 0 {
                            v___x_688_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_618_, v_value_686_, v_a_620_);
                            if v___x_688_ == 0 {
                                v_c_619_ = v_k_684_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_688_;
                            }
                        } else {
                            return v___x_687_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(
    mut v_pu_690_: u8,
    mut v_as_691_: *mut crate::leanh::LeanObject,
    mut v_i_692_: usize,
    mut v_stop_693_: usize,
    mut v___y_694_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: u8 = 0;
    let mut v___y_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    let mut v___x_700_: usize = 0;
    let mut v___x_701_: usize = 0;
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_695_ = lean_usize_dec_eq(v_i_692_, v_stop_693_);
                if v___x_695_ == 0 {
                    v___x_696_ = 1;
                    v___x_703_ = lean_array_uget_borrowed(v_as_691_, v_i_692_);
                    match crate::leanh::lean_obj_tag(v___x_703_) {
                        0 => {
                            v_code_704_ = crate::leanh::lean_ctor_get(v___x_703_, 2);
                            v___y_698_ = v_code_704_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_705_ = crate::leanh::lean_ctor_get(v___x_703_, 1);
                            v___y_698_ = v_code_705_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_706_ = crate::leanh::lean_ctor_get(v___x_703_, 0);
                            v___y_698_ = v_code_706_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_707_ = 0;
                    return v___x_707_;
                }
            }
            1 => {
                v___x_699_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
                    v_pu_690_, v___y_698_, v___y_694_,
                );
                if v___x_699_ == 0 {
                    v___x_700_ = 1usize;
                    v___x_701_ = lean_usize_add(v_i_692_, v___x_700_);
                    v_i_692_ = v___x_701_;
                    state = 0;
                    continue;
                } else {
                    return v___x_696_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0___boxed(
    mut v_pu_708_: *mut crate::leanh::LeanObject,
    mut v_as_709_: *mut crate::leanh::LeanObject,
    mut v_i_710_: *mut crate::leanh::LeanObject,
    mut v_stop_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_713_: u8 = 0;
    let mut v_i_boxed_714_: usize = 0;
    let mut v_stop_boxed_715_: usize = 0;
    let mut v_res_716_: u8 = 0;
    let mut v_r_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_713_ = (crate::leanh::lean_unbox(v_pu_708_) as u8);
    v_i_boxed_714_ = crate::leanh::lean_unbox_usize(v_i_710_);
    crate::leanh::lean_dec(v_i_710_);
    v_stop_boxed_715_ = crate::leanh::lean_unbox_usize(v_stop_711_);
    crate::leanh::lean_dec(v_stop_711_);
    v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_boxed_713_, v_as_709_, v_i_boxed_714_, v_stop_boxed_715_, v___y_712_);
    crate::leanh::lean_dec(v___y_712_);
    crate::leanh::lean_dec_ref(v_as_709_);
    v_r_717_ = crate::leanh::lean_box((v_res_716_) as usize);
    return v_r_717_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn___boxed(
    mut v_pu_718_: *mut crate::leanh::LeanObject,
    mut v_c_719_: *mut crate::leanh::LeanObject,
    mut v_a_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_721_: u8 = 0;
    let mut v_res_722_: u8 = 0;
    let mut v_r_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_721_ = (crate::leanh::lean_unbox(v_pu_718_) as u8);
    v_res_722_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
        v_pu_boxed_721_,
        v_c_719_,
        v_a_720_,
    );
    crate::leanh::lean_dec(v_a_720_);
    crate::leanh::lean_dec_ref(v_c_719_);
    v_r_723_ = crate::leanh::lean_box((v_res_722_) as usize);
    return v_r_723_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(
    mut v_arg_724_: *mut crate::leanh::LeanObject,
    mut v_s_725_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_726_: u8 = 0;
    v___x_726_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(
        v_arg_724_, v_s_725_,
    );
    return v___x_726_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_dependsOn___redArg___boxed(
    mut v_arg_727_: *mut crate::leanh::LeanObject,
    mut v_s_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_729_: u8 = 0;
    let mut v_r_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(v_arg_727_, v_s_728_);
    crate::leanh::lean_dec(v_s_728_);
    crate::leanh::lean_dec(v_arg_727_);
    v_r_730_ = crate::leanh::lean_box((v_res_729_) as usize);
    return v_r_730_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_dependsOn(
    mut v_pu_731_: u8,
    mut v_arg_732_: *mut crate::leanh::LeanObject,
    mut v_s_733_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_734_: u8 = 0;
    v___x_734_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(
        v_arg_732_, v_s_733_,
    );
    return v___x_734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_dependsOn___boxed(
    mut v_pu_735_: *mut crate::leanh::LeanObject,
    mut v_arg_736_: *mut crate::leanh::LeanObject,
    mut v_s_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_738_: u8 = 0;
    let mut v_res_739_: u8 = 0;
    let mut v_r_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_738_ = (crate::leanh::lean_unbox(v_pu_735_) as u8);
    v_res_739_ = l_Lean_Compiler_LCNF_Arg_dependsOn(v_pu_boxed_738_, v_arg_736_, v_s_737_);
    crate::leanh::lean_dec(v_s_737_);
    crate::leanh::lean_dec(v_arg_736_);
    v_r_740_ = crate::leanh::lean_box((v_res_739_) as usize);
    return v_r_740_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_dependsOn(
    mut v_pu_741_: u8,
    mut v_value_742_: *mut crate::leanh::LeanObject,
    mut v_s_743_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_744_: u8 = 0;
    v___x_744_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(
        v_pu_741_,
        v_value_742_,
        v_s_743_,
    );
    return v___x_744_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_dependsOn___boxed(
    mut v_pu_745_: *mut crate::leanh::LeanObject,
    mut v_value_746_: *mut crate::leanh::LeanObject,
    mut v_s_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_748_: u8 = 0;
    let mut v_res_749_: u8 = 0;
    let mut v_r_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_748_ = (crate::leanh::lean_unbox(v_pu_745_) as u8);
    v_res_749_ = l_Lean_Compiler_LCNF_LetValue_dependsOn(v_pu_boxed_748_, v_value_746_, v_s_747_);
    crate::leanh::lean_dec(v_s_747_);
    crate::leanh::lean_dec(v_value_746_);
    v_r_750_ = crate::leanh::lean_box((v_res_749_) as usize);
    return v_r_750_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_dependsOn(
    mut v_pu_751_: u8,
    mut v_decl_752_: *mut crate::leanh::LeanObject,
    mut v_s_753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_754_: u8 = 0;
    v___x_754_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(
        v_pu_751_,
        v_decl_752_,
        v_s_753_,
    );
    return v___x_754_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_dependsOn___boxed(
    mut v_pu_755_: *mut crate::leanh::LeanObject,
    mut v_decl_756_: *mut crate::leanh::LeanObject,
    mut v_s_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_758_: u8 = 0;
    let mut v_res_759_: u8 = 0;
    let mut v_r_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_758_ = (crate::leanh::lean_unbox(v_pu_755_) as u8);
    v_res_759_ = l_Lean_Compiler_LCNF_LetDecl_dependsOn(v_pu_boxed_758_, v_decl_756_, v_s_757_);
    crate::leanh::lean_dec(v_s_757_);
    crate::leanh::lean_dec_ref(v_decl_756_);
    v_r_760_ = crate::leanh::lean_box((v_res_759_) as usize);
    return v_r_760_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_dependsOn(
    mut v_pu_761_: u8,
    mut v_decl_762_: *mut crate::leanh::LeanObject,
    mut v_s_763_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_type_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    v_type_764_ = crate::leanh::lean_ctor_get(v_decl_762_, 3);
    v_value_765_ = crate::leanh::lean_ctor_get(v_decl_762_, 4);
    v___x_766_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_763_, v_type_764_);
    if v___x_766_ == 0 {
        let mut v___x_767_: u8 = 0;
        v___x_767_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
            v_pu_761_,
            v_value_765_,
            v_s_763_,
        );
        return v___x_767_;
    } else {
        return v___x_766_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_dependsOn___boxed(
    mut v_pu_768_: *mut crate::leanh::LeanObject,
    mut v_decl_769_: *mut crate::leanh::LeanObject,
    mut v_s_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_771_: u8 = 0;
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_771_ = (crate::leanh::lean_unbox(v_pu_768_) as u8);
    v_res_772_ = l_Lean_Compiler_LCNF_FunDecl_dependsOn(v_pu_boxed_771_, v_decl_769_, v_s_770_);
    crate::leanh::lean_dec(v_s_770_);
    crate::leanh::lean_dec_ref(v_decl_769_);
    v_r_773_ = crate::leanh::lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CodeDecl_dependsOn(
    mut v_pu_774_: u8,
    mut v_decl_775_: *mut crate::leanh::LeanObject,
    mut v_s_776_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_decl_775_) {
        0 => {
            let mut v_decl_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_778_: u8 = 0;
            v_decl_777_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v___x_778_ =
                l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(
                    v_pu_774_,
                    v_decl_777_,
                    v_s_776_,
                );
            return v___x_778_;
        }
        1 => {
            let mut v_decl_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: u8 = 0;
            v_decl_779_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v_type_780_ = crate::leanh::lean_ctor_get(v_decl_779_, 3);
            v_value_781_ = crate::leanh::lean_ctor_get(v_decl_779_, 4);
            v___x_782_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_776_, v_type_780_);
            if v___x_782_ == 0 {
                let mut v___x_783_: u8 = 0;
                v___x_783_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
                    v_pu_774_,
                    v_value_781_,
                    v_s_776_,
                );
                return v___x_783_;
            } else {
                return v___x_782_;
            }
        }
        2 => {
            let mut v_decl_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_787_: u8 = 0;
            v_decl_784_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v_type_785_ = crate::leanh::lean_ctor_get(v_decl_784_, 3);
            v_value_786_ = crate::leanh::lean_ctor_get(v_decl_784_, 4);
            v___x_787_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_776_, v_type_785_);
            if v___x_787_ == 0 {
                let mut v___x_788_: u8 = 0;
                v___x_788_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
                    v_pu_774_,
                    v_value_786_,
                    v_s_776_,
                );
                return v___x_788_;
            } else {
                return v___x_787_;
            }
        }
        3 => {
            let mut v_fvarId_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_791_: u8 = 0;
            v_fvarId_789_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v_y_790_ = crate::leanh::lean_ctor_get(v_decl_775_, 2);
            v___x_791_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_789_, v_s_776_);
            if v___x_791_ == 0 {
                let mut v___x_792_: u8 = 0;
                v___x_792_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_790_, v_s_776_);
                return v___x_792_;
            } else {
                return v___x_791_;
            }
        }
        4 => {
            let mut v_fvarId_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_795_: u8 = 0;
            v_fvarId_793_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v_y_794_ = crate::leanh::lean_ctor_get(v_decl_775_, 2);
            v___x_795_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_793_, v_s_776_);
            if v___x_795_ == 0 {
                let mut v___x_796_: u8 = 0;
                v___x_796_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_794_, v_s_776_);
                return v___x_796_;
            } else {
                return v___x_795_;
            }
        }
        5 => {
            let mut v_fvarId_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_799_: u8 = 0;
            v_fvarId_797_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v_y_798_ = crate::leanh::lean_ctor_get(v_decl_775_, 3);
            v___x_799_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_797_, v_s_776_);
            if v___x_799_ == 0 {
                let mut v___x_800_: u8 = 0;
                v___x_800_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_798_, v_s_776_);
                return v___x_800_;
            } else {
                return v___x_799_;
            }
        }
        _ => {
            let mut v_fvarId_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_802_: u8 = 0;
            v_fvarId_801_ = crate::leanh::lean_ctor_get(v_decl_775_, 0);
            v___x_802_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_801_, v_s_776_);
            return v___x_802_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CodeDecl_dependsOn___boxed(
    mut v_pu_803_: *mut crate::leanh::LeanObject,
    mut v_decl_804_: *mut crate::leanh::LeanObject,
    mut v_s_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_806_: u8 = 0;
    let mut v_res_807_: u8 = 0;
    let mut v_r_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_806_ = (crate::leanh::lean_unbox(v_pu_803_) as u8);
    v_res_807_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v_pu_boxed_806_, v_decl_804_, v_s_805_);
    crate::leanh::lean_dec(v_s_805_);
    crate::leanh::lean_dec_ref(v_decl_804_);
    v_r_808_ = crate::leanh::lean_box((v_res_807_) as usize);
    return v_r_808_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_dependsOn(
    mut v_pu_809_: u8,
    mut v_c_810_: *mut crate::leanh::LeanObject,
    mut v_s_811_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_812_: u8 = 0;
    v___x_812_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(
        v_pu_809_, v_c_810_, v_s_811_,
    );
    return v___x_812_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_dependsOn___boxed(
    mut v_pu_813_: *mut crate::leanh::LeanObject,
    mut v_c_814_: *mut crate::leanh::LeanObject,
    mut v_s_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_816_: u8 = 0;
    let mut v_res_817_: u8 = 0;
    let mut v_r_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_816_ = (crate::leanh::lean_unbox(v_pu_813_) as u8);
    v_res_817_ = l_Lean_Compiler_LCNF_Code_dependsOn(v_pu_boxed_816_, v_c_814_, v_s_815_);
    crate::leanh::lean_dec(v_s_815_);
    crate::leanh::lean_dec_ref(v_c_814_);
    v_r_818_ = crate::leanh::lean_box((v_res_817_) as usize);
    return v_r_818_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_DependsOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_DependsOn(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_DependsOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_DependsOn(builtin);
}
