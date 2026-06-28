// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
// Imports: Lean.Meta.Sym.SymM Lean.Meta.WHNF Lean.Meta.Sym
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux, l_Lean_Expr_betaRev, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_mkAppRev,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_shareCommonInc___redArg,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::Sym::Util::l_Lean_Meta_Sym_unfoldReducible;
use crate::r#gen::Lean::Meta::Sym::{initialize_Lean_Meta_Sym, runtime_initialize_Lean_Meta_Sym};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_projectCore_x3f, l_Lean_Meta_reduceRecMatcher_x3f,
    l_Lean_Meta_unfoldDefinition_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_isProjectionFn;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0: u64 = 0;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0: u64 = 0;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(
    mut v_e_409_: *mut LeanObject,
    mut v_a_410_: *mut LeanObject,
    mut v_a_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v_a_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_idx_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_425_: u8 = 0;
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_430_: u8 = 0;
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut v_a_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_441_: u8 = 0;
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_isSharedCheck_446_: u8 = 0;
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_454_: u8 = 0;
    let mut v_unused_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_409_) == 11 {
                    v_idx_415_ = lean_ctor_get(v_e_409_, 1);
                    lean_inc(v_idx_415_);
                    v_struct_416_ = lean_ctor_get(v_e_409_, 2);
                    lean_inc_ref_n(v_struct_416_, 2);
                    lean_dec_ref_known(v_e_409_, 3);
                    lean_inc(v_a_413_);
                    lean_inc_ref(v_a_412_);
                    lean_inc(v_a_411_);
                    lean_inc_ref(v_a_410_);
                    v___x_417_ = lean_whnf(v_struct_416_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
                    if lean_obj_tag(v___x_417_) == 0 {
                        v_a_418_ = lean_ctor_get(v___x_417_, 0);
                        lean_inc_n(v_a_418_, 2);
                        lean_dec_ref_known(v___x_417_, 1);
                        v___x_419_ = l_Lean_Meta_projectCore_x3f(
                            v_a_418_, v_idx_415_, v_a_410_, v_a_411_, v_a_412_, v_a_413_,
                        );
                        lean_dec(v_idx_415_);
                        if lean_obj_tag(v___x_419_) == 0 {
                            v_a_420_ = lean_ctor_get(v___x_419_, 0);
                            lean_inc(v_a_420_);
                            if lean_obj_tag(v_a_420_) == 1 {
                                v_val_421_ = lean_ctor_get(v_a_420_, 0);
                                v_isSharedCheck_446_ = (!lean_is_exclusive(v_a_420_)) as u8;
                                if v_isSharedCheck_446_ == 0 {
                                    v___x_423_ = v_a_420_;
                                    v_isShared_424_ = v_isSharedCheck_446_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_421_);
                                    lean_dec(v_a_420_);
                                    v___x_423_ = lean_box(0);
                                    v_isShared_424_ = v_isSharedCheck_446_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_420_);
                                lean_dec(v_a_418_);
                                lean_dec_ref(v_struct_416_);
                                v_isSharedCheck_454_ = (!lean_is_exclusive(v___x_419_)) as u8;
                                if v_isSharedCheck_454_ == 0 {
                                    v_unused_455_ = lean_ctor_get(v___x_419_, 0);
                                    lean_dec(v_unused_455_);
                                    v___x_448_ = v___x_419_;
                                    v_isShared_449_ = v_isSharedCheck_454_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec(v___x_419_);
                                    v___x_448_ = lean_box(0);
                                    v_isShared_449_ = v_isSharedCheck_454_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_418_);
                            lean_dec_ref(v_struct_416_);
                            return v___x_419_;
                        }
                    } else {
                        lean_dec_ref(v_struct_416_);
                        lean_dec(v_idx_415_);
                        v_a_456_ = lean_ctor_get(v___x_417_, 0);
                        v_isSharedCheck_463_ = (!lean_is_exclusive(v___x_417_)) as u8;
                        if v_isSharedCheck_463_ == 0 {
                            v___x_458_ = v___x_417_;
                            v_isShared_459_ = v_isSharedCheck_463_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_456_);
                            lean_dec(v___x_417_);
                            v___x_458_ = lean_box(0);
                            v_isShared_459_ = v_isSharedCheck_463_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_409_);
                    v___x_464_ = lean_box(0);
                    v___x_465_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_465_, 0, v___x_464_);
                    return v___x_465_;
                }
            }
            1 => {
                v___x_425_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_416_,
                        v_a_418_,
                    );
                lean_dec(v_a_418_);
                lean_dec_ref(v_struct_416_);
                if v___x_425_ == 0 {
                    lean_dec_ref_known(v___x_419_, 1);
                    v___x_426_ = l_Lean_Meta_Sym_unfoldReducible(
                        v_val_421_, v_a_410_, v_a_411_, v_a_412_, v_a_413_,
                    );
                    if lean_obj_tag(v___x_426_) == 0 {
                        v_a_427_ = lean_ctor_get(v___x_426_, 0);
                        v_isSharedCheck_437_ = (!lean_is_exclusive(v___x_426_)) as u8;
                        if v_isSharedCheck_437_ == 0 {
                            v___x_429_ = v___x_426_;
                            v_isShared_430_ = v_isSharedCheck_437_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_427_);
                            lean_dec(v___x_426_);
                            v___x_429_ = lean_box(0);
                            v_isShared_430_ = v_isSharedCheck_437_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_423_);
                        v_a_438_ = lean_ctor_get(v___x_426_, 0);
                        v_isSharedCheck_445_ = (!lean_is_exclusive(v___x_426_)) as u8;
                        if v_isSharedCheck_445_ == 0 {
                            v___x_440_ = v___x_426_;
                            v_isShared_441_ = v_isSharedCheck_445_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_438_);
                            lean_dec(v___x_426_);
                            v___x_440_ = lean_box(0);
                            v_isShared_441_ = v_isSharedCheck_445_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_423_);
                    lean_dec(v_val_421_);
                    return v___x_419_;
                }
            }
            2 => {
                if v_isShared_424_ == 0 {
                    lean_ctor_set(v___x_423_, 0, v_a_427_);
                    v___x_432_ = v___x_423_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_427_);
                    v___x_432_ = v_reuseFailAlloc_436_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_430_ == 0 {
                    lean_ctor_set(v___x_429_, 0, v___x_432_);
                    v___x_434_ = v___x_429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
                    v___x_434_ = v_reuseFailAlloc_435_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_434_;
            }
            5 => {
                if v_isShared_441_ == 0 {
                    v___x_443_ = v___x_440_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
                    v___x_443_ = v_reuseFailAlloc_444_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_443_;
            }
            7 => {
                v___x_450_ = lean_box(0);
                if v_isShared_449_ == 0 {
                    lean_ctor_set(v___x_448_, 0, v___x_450_);
                    v___x_452_ = v___x_448_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
                    v___x_452_ = v_reuseFailAlloc_453_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_452_;
            }
            9 => {
                if v_isShared_459_ == 0 {
                    v___x_461_ = v___x_458_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
                    v___x_461_ = v_reuseFailAlloc_462_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f___boxed(
    mut v_e_466_: *mut LeanObject,
    mut v_a_467_: *mut LeanObject,
    mut v_a_468_: *mut LeanObject,
    mut v_a_469_: *mut LeanObject,
    mut v_a_470_: *mut LeanObject,
    mut v_a_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_472_: *mut LeanObject = core::ptr::null_mut();
    v_res_472_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_e_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
    lean_dec(v_a_470_);
    lean_dec_ref(v_a_469_);
    lean_dec(v_a_468_);
    lean_dec_ref(v_a_467_);
    return v_res_472_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(
    mut v_declName_473_: *mut LeanObject,
    mut v___y_474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: u8 = 0;
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_st_ref_get(v___y_474_);
    v_env_477_ = lean_ctor_get(v___x_476_, 0);
    lean_inc_ref(v_env_477_);
    lean_dec(v___x_476_);
    v___x_478_ = l_Lean_Environment_isProjectionFn(v_env_477_, v_declName_473_);
    v___x_479_ = lean_box((v___x_478_) as usize);
    v___x_480_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_480_, 0, v___x_479_);
    return v___x_480_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(
    mut v_declName_481_: *mut LeanObject,
    mut v___y_482_: *mut LeanObject,
    mut v___y_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_481_, v___y_482_);
    lean_dec(v___y_482_);
    return v_res_484_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(
    mut v_declName_485_: *mut LeanObject,
    mut v___y_486_: *mut LeanObject,
    mut v___y_487_: *mut LeanObject,
    mut v___y_488_: *mut LeanObject,
    mut v___y_489_: *mut LeanObject,
    mut v___y_490_: *mut LeanObject,
    mut v___y_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_485_, v___y_491_);
    return v___x_493_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(
    mut v_declName_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
    mut v___y_499_: *mut LeanObject,
    mut v___y_500_: *mut LeanObject,
    mut v___y_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(v_declName_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
    lean_dec(v___y_500_);
    lean_dec_ref(v___y_499_);
    lean_dec(v___y_498_);
    lean_dec_ref(v___y_497_);
    lean_dec(v___y_496_);
    lean_dec_ref(v___y_495_);
    return v_res_502_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0()
-> u64 {
    let mut v___x_503_: u8 = 0;
    let mut v___x_504_: u64 = 0;
    v___x_503_ = 3;
    v___x_504_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_503_);
    return v___x_504_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(
    mut v_lastReduction_505_: *mut LeanObject,
    mut v_f_506_: *mut LeanObject,
    mut v_rargs_507_: *mut LeanObject,
    mut v_a_508_: *mut LeanObject,
    mut v_a_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
    mut v_a_511_: *mut LeanObject,
    mut v_a_512_: *mut LeanObject,
    mut v_a_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_536_: u8 = 0;
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_expr_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v_e_x27_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_563_: u8 = 0;
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: u8 = 0;
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_578_: u8 = 0;
    let mut v_val_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_582_: u8 = 0;
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_596_: u8 = 0;
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_600_: u8 = 0;
    let mut v_isSharedCheck_601_: u8 = 0;
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: u8 = 0;
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v_val_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_624_: u8 = 0;
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_632_: u8 = 0;
    let mut v_a_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_636_: u8 = 0;
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_642_: u8 = 0;
    let mut v_ctxApprox_643_: u8 = 0;
    let mut v_quasiPatternApprox_644_: u8 = 0;
    let mut v_constApprox_645_: u8 = 0;
    let mut v_isDefEqStuckEx_646_: u8 = 0;
    let mut v_unificationHints_647_: u8 = 0;
    let mut v_proofIrrelevance_648_: u8 = 0;
    let mut v_assignSyntheticOpaque_649_: u8 = 0;
    let mut v_offsetCnstrs_650_: u8 = 0;
    let mut v_etaStruct_651_: u8 = 0;
    let mut v_univApprox_652_: u8 = 0;
    let mut v_iota_653_: u8 = 0;
    let mut v_beta_654_: u8 = 0;
    let mut v_proj_655_: u8 = 0;
    let mut v_zeta_656_: u8 = 0;
    let mut v_zetaDelta_657_: u8 = 0;
    let mut v_zetaUnused_658_: u8 = 0;
    let mut v_zetaHave_659_: u8 = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v_trackZetaDelta_663_: u8 = 0;
    let mut v_zetaDeltaSet_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_670_: u8 = 0;
    let mut v_inTypeClassResolution_671_: u8 = 0;
    let mut v_cacheInferType_672_: u8 = 0;
    let mut v___x_673_: u8 = 0;
    let mut v_config_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: u64 = 0;
    let mut v___x_677_: u64 = 0;
    let mut v___x_678_: u64 = 0;
    let mut v___x_679_: u64 = 0;
    let mut v___x_680_: u64 = 0;
    let mut v_key_681_: u64 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_688_: u8 = 0;
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_f_506_) {
                10 => {
                    v_expr_542_ = lean_ctor_get(v_f_506_, 1);
                    lean_inc_ref(v_expr_542_);
                    lean_dec_ref_known(v_f_506_, 2);
                    v_f_506_ = v_expr_542_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_fn_544_ = lean_ctor_get(v_f_506_, 0);
                    lean_inc_ref(v_fn_544_);
                    v_arg_545_ = lean_ctor_get(v_f_506_, 1);
                    lean_inc_ref(v_arg_545_);
                    lean_dec_ref_known(v_f_506_, 2);
                    v___x_546_ = lean_array_push(v_rargs_507_, v_arg_545_);
                    v_f_506_ = v_fn_544_;
                    v_rargs_507_ = v___x_546_;
                    state = 0;
                    continue;
                }
                6 => {
                    v___x_548_ = lean_array_get_size(v_rargs_507_);
                    v___x_549_ = lean_unsigned_to_nat(0);
                    v___x_550_ = lean_nat_dec_eq(v___x_548_, v___x_549_);
                    if v___x_550_ == 0 {
                        lean_dec(v_lastReduction_505_);
                        v_e_x27_551_ =
                            l_Lean_Expr_betaRev(v_f_506_, v_rargs_507_, v___x_550_, v___x_550_);
                        lean_dec_ref(v_rargs_507_);
                        v___x_552_ =
                            l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_x27_551_, v_a_509_);
                        if lean_obj_tag(v___x_552_) == 0 {
                            v_a_553_ = lean_ctor_get(v___x_552_, 0);
                            lean_inc_n(v_a_553_, 2);
                            lean_dec_ref_known(v___x_552_, 1);
                            v___x_554_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_554_, 0, v_a_553_);
                            v___x_555_ = l_Lean_Expr_getAppFn(v_a_553_);
                            v___x_556_ = l_Lean_Expr_getAppNumArgs(v_a_553_);
                            v___x_557_ = lean_mk_empty_array_with_capacity(v___x_556_);
                            lean_dec(v___x_556_);
                            v___x_558_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(
                                v_a_553_, v___x_557_,
                            );
                            v_lastReduction_505_ = v___x_554_;
                            v_f_506_ = v___x_555_;
                            v_rargs_507_ = v___x_558_;
                            state = 0;
                            continue;
                        } else {
                            v_a_560_ = lean_ctor_get(v___x_552_, 0);
                            v_isSharedCheck_567_ = (!lean_is_exclusive(v___x_552_)) as u8;
                            if v_isSharedCheck_567_ == 0 {
                                v___x_562_ = v___x_552_;
                                v_isShared_563_ = v_isSharedCheck_567_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_560_);
                                lean_dec(v___x_552_);
                                v___x_562_ = lean_box(0);
                                v_isShared_563_ = v_isSharedCheck_567_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_f_506_, 3);
                        lean_dec_ref(v_rargs_507_);
                        v___x_568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_568_, 0, v_lastReduction_505_);
                        return v___x_568_;
                    }
                }
                4 => {
                    v_declName_569_ = lean_ctor_get(v_f_506_, 0);
                    lean_inc(v_declName_569_);
                    v___x_570_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_569_, v_a_513_);
                    if lean_obj_tag(v___x_570_) == 0 {
                        v_a_571_ = lean_ctor_get(v___x_570_, 0);
                        lean_inc(v_a_571_);
                        lean_dec_ref_known(v___x_570_, 1);
                        v___x_572_ = (lean_unbox(v_a_571_) as u8);
                        lean_dec(v_a_571_);
                        if v___x_572_ == 0 {
                            v___x_573_ = l_Lean_mkAppRev(v_f_506_, v_rargs_507_);
                            lean_dec_ref(v_rargs_507_);
                            v___x_574_ = l_Lean_Meta_reduceRecMatcher_x3f(
                                v___x_573_, v_a_510_, v_a_511_, v_a_512_, v_a_513_,
                            );
                            lean_dec_ref(v___x_573_);
                            if lean_obj_tag(v___x_574_) == 0 {
                                v_a_575_ = lean_ctor_get(v___x_574_, 0);
                                v_isSharedCheck_605_ = (!lean_is_exclusive(v___x_574_)) as u8;
                                if v_isSharedCheck_605_ == 0 {
                                    v___x_577_ = v___x_574_;
                                    v_isShared_578_ = v_isSharedCheck_605_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_575_);
                                    lean_dec(v___x_574_);
                                    v___x_577_ = lean_box(0);
                                    v_isShared_578_ = v_isSharedCheck_605_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_lastReduction_505_);
                                return v___x_574_;
                            }
                        } else {
                            v___x_606_ = l_Lean_mkAppRev(v_f_506_, v_rargs_507_);
                            lean_dec_ref(v_rargs_507_);
                            v___x_607_ = 0;
                            v___x_608_ = l_Lean_Meta_unfoldDefinition_x3f(
                                v___x_606_, v___x_607_, v_a_510_, v_a_511_, v_a_512_, v_a_513_,
                            );
                            if lean_obj_tag(v___x_608_) == 0 {
                                v_a_609_ = lean_ctor_get(v___x_608_, 0);
                                v_isSharedCheck_632_ = (!lean_is_exclusive(v___x_608_)) as u8;
                                if v_isSharedCheck_632_ == 0 {
                                    v___x_611_ = v___x_608_;
                                    v_isShared_612_ = v_isSharedCheck_632_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_609_);
                                    lean_dec(v___x_608_);
                                    v___x_611_ = lean_box(0);
                                    v_isShared_612_ = v_isSharedCheck_632_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                lean_dec(v_lastReduction_505_);
                                return v___x_608_;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_f_506_, 2);
                        lean_dec_ref(v_rargs_507_);
                        lean_dec(v_lastReduction_505_);
                        v_a_633_ = lean_ctor_get(v___x_570_, 0);
                        v_isSharedCheck_640_ = (!lean_is_exclusive(v___x_570_)) as u8;
                        if v_isSharedCheck_640_ == 0 {
                            v___x_635_ = v___x_570_;
                            v_isShared_636_ = v_isSharedCheck_640_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_633_);
                            lean_dec(v___x_570_);
                            v___x_635_ = lean_box(0);
                            v_isShared_636_ = v_isSharedCheck_640_;
                            state = 18;
                            continue;
                        }
                    }
                }
                11 => {
                    v___x_641_ = l_Lean_Meta_Context_config(v_a_510_);
                    v_foApprox_642_ = lean_ctor_get_uint8(v___x_641_, 0 as u32);
                    v_ctxApprox_643_ = lean_ctor_get_uint8(v___x_641_, 1 as u32);
                    v_quasiPatternApprox_644_ = lean_ctor_get_uint8(v___x_641_, 2 as u32);
                    v_constApprox_645_ = lean_ctor_get_uint8(v___x_641_, 3 as u32);
                    v_isDefEqStuckEx_646_ = lean_ctor_get_uint8(v___x_641_, 4 as u32);
                    v_unificationHints_647_ = lean_ctor_get_uint8(v___x_641_, 5 as u32);
                    v_proofIrrelevance_648_ = lean_ctor_get_uint8(v___x_641_, 6 as u32);
                    v_assignSyntheticOpaque_649_ = lean_ctor_get_uint8(v___x_641_, 7 as u32);
                    v_offsetCnstrs_650_ = lean_ctor_get_uint8(v___x_641_, 8 as u32);
                    v_etaStruct_651_ = lean_ctor_get_uint8(v___x_641_, 10 as u32);
                    v_univApprox_652_ = lean_ctor_get_uint8(v___x_641_, 11 as u32);
                    v_iota_653_ = lean_ctor_get_uint8(v___x_641_, 12 as u32);
                    v_beta_654_ = lean_ctor_get_uint8(v___x_641_, 13 as u32);
                    v_proj_655_ = lean_ctor_get_uint8(v___x_641_, 14 as u32);
                    v_zeta_656_ = lean_ctor_get_uint8(v___x_641_, 15 as u32);
                    v_zetaDelta_657_ = lean_ctor_get_uint8(v___x_641_, 16 as u32);
                    v_zetaUnused_658_ = lean_ctor_get_uint8(v___x_641_, 17 as u32);
                    v_zetaHave_659_ = lean_ctor_get_uint8(v___x_641_, 18 as u32);
                    v_isSharedCheck_688_ = (!lean_is_exclusive(v___x_641_)) as u8;
                    if v_isSharedCheck_688_ == 0 {
                        v___x_661_ = v___x_641_;
                        v_isShared_662_ = v_isSharedCheck_688_;
                        state = 20;
                        continue;
                    } else {
                        lean_dec(v___x_641_);
                        v___x_661_ = lean_box(0);
                        v_isShared_662_ = v_isSharedCheck_688_;
                        state = 20;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_rargs_507_);
                    lean_dec_ref(v_f_506_);
                    v___x_689_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_689_, 0, v_lastReduction_505_);
                    return v___x_689_;
                }
            },
            1 => {
                if lean_obj_tag(v_a_516_) == 0 {
                    lean_dec_ref(v_rargs_507_);
                    v___x_517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_517_, 0, v_lastReduction_505_);
                    return v___x_517_;
                } else {
                    lean_dec(v_lastReduction_505_);
                    v_val_518_ = lean_ctor_get(v_a_516_, 0);
                    v_isSharedCheck_541_ = (!lean_is_exclusive(v_a_516_)) as u8;
                    if v_isSharedCheck_541_ == 0 {
                        v___x_520_ = v_a_516_;
                        v_isShared_521_ = v_isSharedCheck_541_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_518_);
                        lean_dec(v_a_516_);
                        v___x_520_ = lean_box(0);
                        v_isShared_521_ = v_isSharedCheck_541_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_522_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_518_, v_a_509_);
                if lean_obj_tag(v___x_522_) == 0 {
                    v_a_523_ = lean_ctor_get(v___x_522_, 0);
                    lean_inc(v_a_523_);
                    lean_dec_ref_known(v___x_522_, 1);
                    v___x_524_ = l_Lean_mkAppRev(v_a_523_, v_rargs_507_);
                    lean_dec_ref(v_rargs_507_);
                    lean_inc_ref(v___x_524_);
                    if v_isShared_521_ == 0 {
                        lean_ctor_set(v___x_520_, 0, v___x_524_);
                        v___x_526_ = v___x_520_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_524_);
                        v___x_526_ = v_reuseFailAlloc_532_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_520_);
                    lean_dec_ref(v_rargs_507_);
                    v_a_533_ = lean_ctor_get(v___x_522_, 0);
                    v_isSharedCheck_540_ = (!lean_is_exclusive(v___x_522_)) as u8;
                    if v_isSharedCheck_540_ == 0 {
                        v___x_535_ = v___x_522_;
                        v_isShared_536_ = v_isSharedCheck_540_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_533_);
                        lean_dec(v___x_522_);
                        v___x_535_ = lean_box(0);
                        v_isShared_536_ = v_isSharedCheck_540_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_527_ = l_Lean_Expr_getAppFn(v___x_524_);
                v___x_528_ = l_Lean_Expr_getAppNumArgs(v___x_524_);
                v___x_529_ = lean_mk_empty_array_with_capacity(v___x_528_);
                lean_dec(v___x_528_);
                v___x_530_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_524_, v___x_529_);
                v_lastReduction_505_ = v___x_526_;
                v_f_506_ = v___x_527_;
                v_rargs_507_ = v___x_530_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_536_ == 0 {
                    v___x_538_ = v___x_535_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
                    v___x_538_ = v_reuseFailAlloc_539_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_538_;
            }
            6 => {
                if v_isShared_563_ == 0 {
                    v___x_565_ = v___x_562_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
                    v___x_565_ = v_reuseFailAlloc_566_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_565_;
            }
            8 => {
                if lean_obj_tag(v_a_575_) == 1 {
                    lean_del_object(v___x_577_);
                    lean_dec(v_lastReduction_505_);
                    v_val_579_ = lean_ctor_get(v_a_575_, 0);
                    v_isSharedCheck_601_ = (!lean_is_exclusive(v_a_575_)) as u8;
                    if v_isSharedCheck_601_ == 0 {
                        v___x_581_ = v_a_575_;
                        v_isShared_582_ = v_isSharedCheck_601_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_579_);
                        lean_dec(v_a_575_);
                        v___x_581_ = lean_box(0);
                        v_isShared_582_ = v_isSharedCheck_601_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_a_575_);
                    if v_isShared_578_ == 0 {
                        lean_ctor_set(v___x_577_, 0, v_lastReduction_505_);
                        v___x_603_ = v___x_577_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_604_, 0, v_lastReduction_505_);
                        v___x_603_ = v_reuseFailAlloc_604_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                v___x_583_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_579_, v_a_509_);
                if lean_obj_tag(v___x_583_) == 0 {
                    v_a_584_ = lean_ctor_get(v___x_583_, 0);
                    lean_inc_n(v_a_584_, 2);
                    lean_dec_ref_known(v___x_583_, 1);
                    if v_isShared_582_ == 0 {
                        lean_ctor_set(v___x_581_, 0, v_a_584_);
                        v___x_586_ = v___x_581_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_584_);
                        v___x_586_ = v_reuseFailAlloc_592_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_581_);
                    v_a_593_ = lean_ctor_get(v___x_583_, 0);
                    v_isSharedCheck_600_ = (!lean_is_exclusive(v___x_583_)) as u8;
                    if v_isSharedCheck_600_ == 0 {
                        v___x_595_ = v___x_583_;
                        v_isShared_596_ = v_isSharedCheck_600_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_593_);
                        lean_dec(v___x_583_);
                        v___x_595_ = lean_box(0);
                        v_isShared_596_ = v_isSharedCheck_600_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                v___x_587_ = l_Lean_Expr_getAppFn(v_a_584_);
                v___x_588_ = l_Lean_Expr_getAppNumArgs(v_a_584_);
                v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
                lean_dec(v___x_588_);
                v___x_590_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_584_, v___x_589_);
                v_lastReduction_505_ = v___x_586_;
                v_f_506_ = v___x_587_;
                v_rargs_507_ = v___x_590_;
                state = 0;
                continue;
            }
            11 => {
                if v_isShared_596_ == 0 {
                    v___x_598_ = v___x_595_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
                    v___x_598_ = v_reuseFailAlloc_599_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_598_;
            }
            13 => {
                return v___x_603_;
            }
            14 => {
                if lean_obj_tag(v_a_609_) == 1 {
                    lean_del_object(v___x_611_);
                    v_val_613_ = lean_ctor_get(v_a_609_, 0);
                    lean_inc(v_val_613_);
                    lean_dec_ref_known(v_a_609_, 1);
                    v___x_614_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_613_, v_a_509_);
                    if lean_obj_tag(v___x_614_) == 0 {
                        v_a_615_ = lean_ctor_get(v___x_614_, 0);
                        lean_inc(v_a_615_);
                        lean_dec_ref_known(v___x_614_, 1);
                        v___x_616_ = l_Lean_Expr_getAppFn(v_a_615_);
                        v___x_617_ = l_Lean_Expr_getAppNumArgs(v_a_615_);
                        v___x_618_ = lean_mk_empty_array_with_capacity(v___x_617_);
                        lean_dec(v___x_617_);
                        v___x_619_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(
                            v_a_615_, v___x_618_,
                        );
                        v_f_506_ = v___x_616_;
                        v_rargs_507_ = v___x_619_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_lastReduction_505_);
                        v_a_621_ = lean_ctor_get(v___x_614_, 0);
                        v_isSharedCheck_628_ = (!lean_is_exclusive(v___x_614_)) as u8;
                        if v_isSharedCheck_628_ == 0 {
                            v___x_623_ = v___x_614_;
                            v_isShared_624_ = v_isSharedCheck_628_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_621_);
                            lean_dec(v___x_614_);
                            v___x_623_ = lean_box(0);
                            v_isShared_624_ = v_isSharedCheck_628_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_609_);
                    if v_isShared_612_ == 0 {
                        lean_ctor_set(v___x_611_, 0, v_lastReduction_505_);
                        v___x_630_ = v___x_611_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_631_, 0, v_lastReduction_505_);
                        v___x_630_ = v_reuseFailAlloc_631_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_624_ == 0 {
                    v___x_626_ = v___x_623_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
                    v___x_626_ = v_reuseFailAlloc_627_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_626_;
            }
            17 => {
                return v___x_630_;
            }
            18 => {
                if v_isShared_636_ == 0 {
                    v___x_638_ = v___x_635_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
                    v___x_638_ = v_reuseFailAlloc_639_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_638_;
            }
            20 => {
                v_trackZetaDelta_663_ = lean_ctor_get_uint8(
                    v_a_510_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_664_ = lean_ctor_get(v_a_510_, 1);
                v_lctx_665_ = lean_ctor_get(v_a_510_, 2);
                v_localInstances_666_ = lean_ctor_get(v_a_510_, 3);
                v_defEqCtx_x3f_667_ = lean_ctor_get(v_a_510_, 4);
                v_synthPendingDepth_668_ = lean_ctor_get(v_a_510_, 5);
                v_canUnfold_x3f_669_ = lean_ctor_get(v_a_510_, 6);
                v_univApprox_670_ = lean_ctor_get_uint8(
                    v_a_510_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_671_ = lean_ctor_get_uint8(
                    v_a_510_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_672_ = lean_ctor_get_uint8(
                    v_a_510_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_673_ = 3;
                if v_isShared_662_ == 0 {
                    v_config_675_ = v___x_661_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 0 as u32, v_foApprox_642_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 1 as u32, v_ctxApprox_643_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 2 as u32, v_quasiPatternApprox_644_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 3 as u32, v_constApprox_645_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 4 as u32, v_isDefEqStuckEx_646_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 5 as u32, v_unificationHints_647_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 6 as u32, v_proofIrrelevance_648_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_687_,
                        7 as u32,
                        v_assignSyntheticOpaque_649_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 8 as u32, v_offsetCnstrs_650_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 10 as u32, v_etaStruct_651_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 11 as u32, v_univApprox_652_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 12 as u32, v_iota_653_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 13 as u32, v_beta_654_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 14 as u32, v_proj_655_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 15 as u32, v_zeta_656_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 16 as u32, v_zetaDelta_657_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 17 as u32, v_zetaUnused_658_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_687_, 18 as u32, v_zetaHave_659_);
                    v_config_675_ = v_reuseFailAlloc_687_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                lean_ctor_set_uint8(v_config_675_, 9 as u32, v___x_673_);
                v___x_676_ = l_Lean_Meta_Context_configKey(v_a_510_);
                v___x_677_ = 3u64;
                v___x_678_ = lean_uint64_shift_right(v___x_676_, v___x_677_);
                v___x_679_ = lean_uint64_shift_left(v___x_678_, v___x_677_);
                v___x_680_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0_once), _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0);
                v_key_681_ = lean_uint64_lor(v___x_679_, v___x_680_);
                v___x_682_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_682_, 0, v_config_675_);
                lean_ctor_set_uint64(
                    v___x_682_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_681_,
                );
                lean_inc(v_canUnfold_x3f_669_);
                lean_inc(v_synthPendingDepth_668_);
                lean_inc(v_defEqCtx_x3f_667_);
                lean_inc_ref(v_localInstances_666_);
                lean_inc_ref(v_lctx_665_);
                lean_inc(v_zetaDeltaSet_664_);
                v___x_683_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_683_, 0, v___x_682_);
                lean_ctor_set(v___x_683_, 1, v_zetaDeltaSet_664_);
                lean_ctor_set(v___x_683_, 2, v_lctx_665_);
                lean_ctor_set(v___x_683_, 3, v_localInstances_666_);
                lean_ctor_set(v___x_683_, 4, v_defEqCtx_x3f_667_);
                lean_ctor_set(v___x_683_, 5, v_synthPendingDepth_668_);
                lean_ctor_set(v___x_683_, 6, v_canUnfold_x3f_669_);
                lean_ctor_set_uint8(
                    v___x_683_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_663_,
                );
                lean_ctor_set_uint8(
                    v___x_683_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_670_,
                );
                lean_ctor_set_uint8(
                    v___x_683_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_671_,
                );
                lean_ctor_set_uint8(
                    v___x_683_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_672_,
                );
                v___x_684_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_f_506_, v___x_683_, v_a_511_, v_a_512_, v_a_513_);
                lean_dec_ref_known(v___x_683_, 7);
                if lean_obj_tag(v___x_684_) == 0 {
                    v_a_685_ = lean_ctor_get(v___x_684_, 0);
                    lean_inc(v_a_685_);
                    lean_dec_ref_known(v___x_684_, 1);
                    v_a_516_ = v_a_685_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___x_684_) == 0 {
                        v_a_686_ = lean_ctor_get(v___x_684_, 0);
                        lean_inc(v_a_686_);
                        lean_dec_ref_known(v___x_684_, 1);
                        v_a_516_ = v_a_686_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_rargs_507_);
                        lean_dec(v_lastReduction_505_);
                        return v___x_684_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(
    mut v_lastReduction_690_: *mut LeanObject,
    mut v_f_691_: *mut LeanObject,
    mut v_rargs_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
    mut v_a_694_: *mut LeanObject,
    mut v_a_695_: *mut LeanObject,
    mut v_a_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_700_: *mut LeanObject = core::ptr::null_mut();
    v_res_700_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v_lastReduction_690_, v_f_691_, v_rargs_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
    lean_dec(v_a_698_);
    lean_dec_ref(v_a_697_);
    lean_dec(v_a_696_);
    lean_dec_ref(v_a_695_);
    lean_dec(v_a_694_);
    lean_dec_ref(v_a_693_);
    return v_res_700_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0() -> u64 {
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: u64 = 0;
    v___x_701_ = 2;
    v___x_702_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_701_);
    return v___x_702_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
    mut v_e_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
    mut v_a_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
    mut v_a_708_: *mut LeanObject,
    mut v_a_709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_712_: u8 = 0;
    let mut v_ctxApprox_713_: u8 = 0;
    let mut v_quasiPatternApprox_714_: u8 = 0;
    let mut v_constApprox_715_: u8 = 0;
    let mut v_isDefEqStuckEx_716_: u8 = 0;
    let mut v_unificationHints_717_: u8 = 0;
    let mut v_proofIrrelevance_718_: u8 = 0;
    let mut v_assignSyntheticOpaque_719_: u8 = 0;
    let mut v_offsetCnstrs_720_: u8 = 0;
    let mut v_etaStruct_721_: u8 = 0;
    let mut v_univApprox_722_: u8 = 0;
    let mut v_iota_723_: u8 = 0;
    let mut v_beta_724_: u8 = 0;
    let mut v_proj_725_: u8 = 0;
    let mut v_zeta_726_: u8 = 0;
    let mut v_zetaDelta_727_: u8 = 0;
    let mut v_zetaUnused_728_: u8 = 0;
    let mut v_zetaHave_729_: u8 = 0;
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v_trackZetaDelta_733_: u8 = 0;
    let mut v_zetaDeltaSet_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_740_: u8 = 0;
    let mut v_inTypeClassResolution_741_: u8 = 0;
    let mut v_cacheInferType_742_: u8 = 0;
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: u8 = 0;
    let mut v_config_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u64 = 0;
    let mut v___x_749_: u64 = 0;
    let mut v___x_750_: u64 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: u64 = 0;
    let mut v___x_755_: u64 = 0;
    let mut v_key_756_: u64 = 0;
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_763_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut v_reuseFailAlloc_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_711_ = l_Lean_Meta_Context_config(v_a_706_);
                v_foApprox_712_ = lean_ctor_get_uint8(v___x_711_, 0 as u32);
                v_ctxApprox_713_ = lean_ctor_get_uint8(v___x_711_, 1 as u32);
                v_quasiPatternApprox_714_ = lean_ctor_get_uint8(v___x_711_, 2 as u32);
                v_constApprox_715_ = lean_ctor_get_uint8(v___x_711_, 3 as u32);
                v_isDefEqStuckEx_716_ = lean_ctor_get_uint8(v___x_711_, 4 as u32);
                v_unificationHints_717_ = lean_ctor_get_uint8(v___x_711_, 5 as u32);
                v_proofIrrelevance_718_ = lean_ctor_get_uint8(v___x_711_, 6 as u32);
                v_assignSyntheticOpaque_719_ = lean_ctor_get_uint8(v___x_711_, 7 as u32);
                v_offsetCnstrs_720_ = lean_ctor_get_uint8(v___x_711_, 8 as u32);
                v_etaStruct_721_ = lean_ctor_get_uint8(v___x_711_, 10 as u32);
                v_univApprox_722_ = lean_ctor_get_uint8(v___x_711_, 11 as u32);
                v_iota_723_ = lean_ctor_get_uint8(v___x_711_, 12 as u32);
                v_beta_724_ = lean_ctor_get_uint8(v___x_711_, 13 as u32);
                v_proj_725_ = lean_ctor_get_uint8(v___x_711_, 14 as u32);
                v_zeta_726_ = lean_ctor_get_uint8(v___x_711_, 15 as u32);
                v_zetaDelta_727_ = lean_ctor_get_uint8(v___x_711_, 16 as u32);
                v_zetaUnused_728_ = lean_ctor_get_uint8(v___x_711_, 17 as u32);
                v_zetaHave_729_ = lean_ctor_get_uint8(v___x_711_, 18 as u32);
                v_isSharedCheck_769_ = (!lean_is_exclusive(v___x_711_)) as u8;
                if v_isSharedCheck_769_ == 0 {
                    v___x_731_ = v___x_711_;
                    v_isShared_732_ = v_isSharedCheck_769_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_711_);
                    v___x_731_ = lean_box(0);
                    v_isShared_732_ = v_isSharedCheck_769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_733_ = lean_ctor_get_uint8(
                    v_a_706_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_734_ = lean_ctor_get(v_a_706_, 1);
                v_lctx_735_ = lean_ctor_get(v_a_706_, 2);
                v_localInstances_736_ = lean_ctor_get(v_a_706_, 3);
                v_defEqCtx_x3f_737_ = lean_ctor_get(v_a_706_, 4);
                v_synthPendingDepth_738_ = lean_ctor_get(v_a_706_, 5);
                v_canUnfold_x3f_739_ = lean_ctor_get(v_a_706_, 6);
                v_univApprox_740_ = lean_ctor_get_uint8(
                    v_a_706_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_741_ = lean_ctor_get_uint8(
                    v_a_706_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_742_ = lean_ctor_get_uint8(
                    v_a_706_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_743_ = l_Lean_Expr_getAppFn(v_e_703_);
                v___x_744_ = l_Lean_Expr_getAppNumArgs(v_e_703_);
                v___x_745_ = 2;
                if v_isShared_732_ == 0 {
                    v_config_747_ = v___x_731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 0 as u32, v_foApprox_712_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 1 as u32, v_ctxApprox_713_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 2 as u32, v_quasiPatternApprox_714_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 3 as u32, v_constApprox_715_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 4 as u32, v_isDefEqStuckEx_716_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 5 as u32, v_unificationHints_717_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 6 as u32, v_proofIrrelevance_718_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_768_,
                        7 as u32,
                        v_assignSyntheticOpaque_719_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 8 as u32, v_offsetCnstrs_720_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 10 as u32, v_etaStruct_721_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 11 as u32, v_univApprox_722_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 12 as u32, v_iota_723_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 13 as u32, v_beta_724_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 14 as u32, v_proj_725_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 15 as u32, v_zeta_726_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 16 as u32, v_zetaDelta_727_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 17 as u32, v_zetaUnused_728_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_768_, 18 as u32, v_zetaHave_729_);
                    v_config_747_ = v_reuseFailAlloc_768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_747_, 9 as u32, v___x_745_);
                v___x_748_ = l_Lean_Meta_Context_configKey(v_a_706_);
                v___x_749_ = 3u64;
                v___x_750_ = lean_uint64_shift_right(v___x_748_, v___x_749_);
                v___x_751_ = lean_box(0);
                v___x_752_ = lean_mk_empty_array_with_capacity(v___x_744_);
                lean_dec(v___x_744_);
                v___x_753_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_703_, v___x_752_);
                v___x_754_ = lean_uint64_shift_left(v___x_750_, v___x_749_);
                v___x_755_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0,
                );
                v_key_756_ = lean_uint64_lor(v___x_754_, v___x_755_);
                v___x_757_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_757_, 0, v_config_747_);
                lean_ctor_set_uint64(
                    v___x_757_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_756_,
                );
                lean_inc(v_canUnfold_x3f_739_);
                lean_inc(v_synthPendingDepth_738_);
                lean_inc(v_defEqCtx_x3f_737_);
                lean_inc_ref(v_localInstances_736_);
                lean_inc_ref(v_lctx_735_);
                lean_inc(v_zetaDeltaSet_734_);
                v___x_758_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_758_, 0, v___x_757_);
                lean_ctor_set(v___x_758_, 1, v_zetaDeltaSet_734_);
                lean_ctor_set(v___x_758_, 2, v_lctx_735_);
                lean_ctor_set(v___x_758_, 3, v_localInstances_736_);
                lean_ctor_set(v___x_758_, 4, v_defEqCtx_x3f_737_);
                lean_ctor_set(v___x_758_, 5, v_synthPendingDepth_738_);
                lean_ctor_set(v___x_758_, 6, v_canUnfold_x3f_739_);
                lean_ctor_set_uint8(
                    v___x_758_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_733_,
                );
                lean_ctor_set_uint8(
                    v___x_758_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_740_,
                );
                lean_ctor_set_uint8(
                    v___x_758_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_741_,
                );
                lean_ctor_set_uint8(
                    v___x_758_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_742_,
                );
                v___x_759_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v___x_751_, v___x_743_, v___x_753_, v_a_704_, v_a_705_, v___x_758_, v_a_707_, v_a_708_, v_a_709_);
                lean_dec_ref_known(v___x_758_, 7);
                if lean_obj_tag(v___x_759_) == 0 {
                    v_a_760_ = lean_ctor_get(v___x_759_, 0);
                    v_isSharedCheck_767_ = (!lean_is_exclusive(v___x_759_)) as u8;
                    if v_isSharedCheck_767_ == 0 {
                        v___x_762_ = v___x_759_;
                        v_isShared_763_ = v_isSharedCheck_767_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_760_);
                        lean_dec(v___x_759_);
                        v___x_762_ = lean_box(0);
                        v_isShared_763_ = v_isSharedCheck_767_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_759_;
                }
            }
            3 => {
                if v_isShared_763_ == 0 {
                    v___x_765_ = v___x_762_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
                    v___x_765_ = v_reuseFailAlloc_766_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(
    mut v_e_770_: *mut LeanObject,
    mut v_a_771_: *mut LeanObject,
    mut v_a_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
    mut v_a_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
    mut v_a_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
        v_e_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_,
    );
    lean_dec(v_a_776_);
    lean_dec_ref(v_a_775_);
    lean_dec(v_a_774_);
    lean_dec_ref(v_a_773_);
    lean_dec(v_a_772_);
    lean_dec_ref(v_a_771_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
    mut v_e_779_: *mut LeanObject,
    mut v_a_780_: *mut LeanObject,
    mut v_a_781_: *mut LeanObject,
    mut v_a_782_: *mut LeanObject,
    mut v_a_783_: *mut LeanObject,
    mut v_a_784_: *mut LeanObject,
    mut v_a_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_791_: u8 = 0;
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut v_a_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_803_: u8 = 0;
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_779_);
                v___x_787_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(
                    v_e_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_,
                );
                if lean_obj_tag(v___x_787_) == 0 {
                    v_a_788_ = lean_ctor_get(v___x_787_, 0);
                    v_isSharedCheck_799_ = (!lean_is_exclusive(v___x_787_)) as u8;
                    if v_isSharedCheck_799_ == 0 {
                        v___x_790_ = v___x_787_;
                        v_isShared_791_ = v_isSharedCheck_799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_788_);
                        lean_dec(v___x_787_);
                        v___x_790_ = lean_box(0);
                        v_isShared_791_ = v_isSharedCheck_799_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_779_);
                    v_a_800_ = lean_ctor_get(v___x_787_, 0);
                    v_isSharedCheck_807_ = (!lean_is_exclusive(v___x_787_)) as u8;
                    if v_isSharedCheck_807_ == 0 {
                        v___x_802_ = v___x_787_;
                        v_isShared_803_ = v_isSharedCheck_807_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_800_);
                        lean_dec(v___x_787_);
                        v___x_802_ = lean_box(0);
                        v_isShared_803_ = v_isSharedCheck_807_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_788_) == 0 {
                    if v_isShared_791_ == 0 {
                        lean_ctor_set(v___x_790_, 0, v_e_779_);
                        v___x_793_ = v___x_790_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_794_, 0, v_e_779_);
                        v___x_793_ = v_reuseFailAlloc_794_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_779_);
                    v_val_795_ = lean_ctor_get(v_a_788_, 0);
                    lean_inc(v_val_795_);
                    lean_dec_ref_known(v_a_788_, 1);
                    if v_isShared_791_ == 0 {
                        lean_ctor_set(v___x_790_, 0, v_val_795_);
                        v___x_797_ = v___x_790_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_798_, 0, v_val_795_);
                        v___x_797_ = v_reuseFailAlloc_798_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_793_;
            }
            3 => {
                return v___x_797_;
            }
            4 => {
                if v_isShared_803_ == 0 {
                    v___x_805_ = v___x_802_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
                    v___x_805_ = v_reuseFailAlloc_806_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(
    mut v_e_808_: *mut LeanObject,
    mut v_a_809_: *mut LeanObject,
    mut v_a_810_: *mut LeanObject,
    mut v_a_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
    mut v_a_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_816_: *mut LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
        v_e_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_,
    );
    lean_dec(v_a_814_);
    lean_dec_ref(v_a_813_);
    lean_dec(v_a_812_);
    lean_dec_ref(v_a_811_);
    lean_dec(v_a_810_);
    lean_dec_ref(v_a_809_);
    return v_res_816_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
}
