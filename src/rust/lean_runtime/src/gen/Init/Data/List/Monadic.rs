// Lean compiler output
// Module: Init.Data.List.Monadic
// Imports: Init.Data.List.Attach Init.Data.List.Control Init.Data.Array.Bootstrap Init.Data.Bool
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l_List_mapM_x27___redArg___lam__0(
    mut v_____do__lift_374_: *mut LeanObject,
    mut v_toPure_375_: *mut LeanObject,
    mut v_____do__lift_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_377_, 0, v_____do__lift_374_);
    lean_ctor_set(v___x_377_, 1, v_____do__lift_376_);
    v___x_378_ = lean_apply_2(v_toPure_375_, lean_box(0), v___x_377_);
    return v___x_378_;
}
pub unsafe fn l_List_mapM_x27___redArg(
    mut v_inst_379_: *mut LeanObject,
    mut v_f_380_: *mut LeanObject,
    mut v_x_381_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_381_) == 0 {
        let mut v_toApplicative_382_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_382_ = lean_ctor_get(v_inst_379_, 0);
        lean_inc_ref(v_toApplicative_382_);
        lean_dec(v_f_380_);
        lean_dec_ref(v_inst_379_);
        v_toPure_383_ = lean_ctor_get(v_toApplicative_382_, 1);
        lean_inc(v_toPure_383_);
        lean_dec_ref(v_toApplicative_382_);
        v___x_384_ = lean_box(0);
        v___x_385_ = lean_apply_2(v_toPure_383_, lean_box(0), v___x_384_);
        return v___x_385_;
    } else {
        let mut v_toApplicative_386_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_387_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_388_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_389_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_386_ = lean_ctor_get(v_inst_379_, 0);
        v_toBind_387_ = lean_ctor_get(v_inst_379_, 1);
        lean_inc_n(v_toBind_387_, 2);
        v_toPure_388_ = lean_ctor_get(v_toApplicative_386_, 1);
        lean_inc(v_toPure_388_);
        v_head_389_ = lean_ctor_get(v_x_381_, 0);
        lean_inc(v_head_389_);
        v_tail_390_ = lean_ctor_get(v_x_381_, 1);
        lean_inc(v_tail_390_);
        lean_dec_ref_known(v_x_381_, 2);
        lean_inc(v_f_380_);
        v___f_391_ = lean_alloc_closure(
            l_List_mapM_x27___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_391_, 0, v_toPure_388_);
        lean_closure_set(v___f_391_, 1, v_inst_379_);
        lean_closure_set(v___f_391_, 2, v_f_380_);
        lean_closure_set(v___f_391_, 3, v_tail_390_);
        lean_closure_set(v___f_391_, 4, v_toBind_387_);
        v___x_392_ = lean_apply_1(v_f_380_, v_head_389_);
        v___x_393_ = lean_apply_4(
            v_toBind_387_,
            lean_box(0),
            lean_box(0),
            v___x_392_,
            v___f_391_,
        );
        return v___x_393_;
    }
}
pub unsafe fn l_List_mapM_x27___redArg___lam__1(
    mut v_toPure_394_: *mut LeanObject,
    mut v_inst_395_: *mut LeanObject,
    mut v_f_396_: *mut LeanObject,
    mut v_tail_397_: *mut LeanObject,
    mut v_toBind_398_: *mut LeanObject,
    mut v_____do__lift_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___f_400_ = lean_alloc_closure(
        l_List_mapM_x27___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_400_, 0, v_____do__lift_399_);
    lean_closure_set(v___f_400_, 1, v_toPure_394_);
    v___x_401_ = l_List_mapM_x27___redArg(v_inst_395_, v_f_396_, v_tail_397_);
    v___x_402_ = lean_apply_4(
        v_toBind_398_,
        lean_box(0),
        lean_box(0),
        v___x_401_,
        v___f_400_,
    );
    return v___x_402_;
}
pub unsafe fn l_List_mapM_x27(
    mut v_m_403_: *mut LeanObject,
    mut v_00_u03b1_404_: *mut LeanObject,
    mut v_00_u03b2_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
    mut v_f_407_: *mut LeanObject,
    mut v_x_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_409_ = l_List_mapM_x27___redArg(v_inst_406_, v_f_407_, v_x_408_);
    return v___x_409_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(
    mut v_x_410_: *mut LeanObject,
    mut v_x_411_: *mut LeanObject,
    mut v_h__1_412_: *mut LeanObject,
    mut v_h__2_413_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_410_) == 0 {
        let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_413_);
        v___x_414_ = lean_apply_1(v_h__1_412_, v_x_411_);
        return v___x_414_;
    } else {
        let mut v_head_415_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_412_);
        v_head_415_ = lean_ctor_get(v_x_410_, 0);
        lean_inc(v_head_415_);
        v_tail_416_ = lean_ctor_get(v_x_410_, 1);
        lean_inc(v_tail_416_);
        lean_dec_ref_known(v_x_410_, 2);
        v___x_417_ = lean_apply_3(v_h__2_413_, v_head_415_, v_tail_416_, v_x_411_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter(
    mut v_00_u03b1_418_: *mut LeanObject,
    mut v_00_u03b2_419_: *mut LeanObject,
    mut v_motive_420_: *mut LeanObject,
    mut v_x_421_: *mut LeanObject,
    mut v_x_422_: *mut LeanObject,
    mut v_h__1_423_: *mut LeanObject,
    mut v_h__2_424_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_421_) == 0 {
        let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_424_);
        v___x_425_ = lean_apply_1(v_h__1_423_, v_x_422_);
        return v___x_425_;
    } else {
        let mut v_head_426_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_423_);
        v_head_426_ = lean_ctor_get(v_x_421_, 0);
        lean_inc(v_head_426_);
        v_tail_427_ = lean_ctor_get(v_x_421_, 1);
        lean_inc(v_tail_427_);
        lean_dec_ref_known(v_x_421_, 2);
        v___x_428_ = lean_apply_3(v_h__2_424_, v_head_426_, v_tail_427_, v_x_422_);
        return v___x_428_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter___redArg(
    mut v_x_429_: *mut LeanObject,
    mut v_h__1_430_: *mut LeanObject,
    mut v_h__2_431_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_429_) == 0 {
        let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_431_);
        v___x_432_ = lean_box(0);
        v___x_433_ = lean_apply_1(v_h__1_430_, v___x_432_);
        return v___x_433_;
    } else {
        let mut v_head_434_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_430_);
        v_head_434_ = lean_ctor_get(v_x_429_, 0);
        lean_inc(v_head_434_);
        v_tail_435_ = lean_ctor_get(v_x_429_, 1);
        lean_inc(v_tail_435_);
        lean_dec_ref_known(v_x_429_, 2);
        v___x_436_ = lean_apply_2(v_h__2_431_, v_head_434_, v_tail_435_);
        return v___x_436_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter(
    mut v_00_u03b1_437_: *mut LeanObject,
    mut v_motive_438_: *mut LeanObject,
    mut v_x_439_: *mut LeanObject,
    mut v_h__1_440_: *mut LeanObject,
    mut v_h__2_441_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_439_) == 0 {
        let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_441_);
        v___x_442_ = lean_box(0);
        v___x_443_ = lean_apply_1(v_h__1_440_, v___x_442_);
        return v___x_443_;
    } else {
        let mut v_head_444_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_440_);
        v_head_444_ = lean_ctor_get(v_x_439_, 0);
        lean_inc(v_head_444_);
        v_tail_445_ = lean_ctor_get(v_x_439_, 1);
        lean_inc(v_tail_445_);
        lean_dec_ref_known(v_x_439_, 2);
        v___x_446_ = lean_apply_2(v_h__2_441_, v_head_444_, v_tail_445_);
        return v___x_446_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_447_: *mut LeanObject,
    mut v_h__1_448_: *mut LeanObject,
    mut v_h__2_449_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_447_) == 0 {
        let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_449_);
        v___x_450_ = lean_box(0);
        v___x_451_ = lean_apply_1(v_h__1_448_, v___x_450_);
        return v___x_451_;
    } else {
        let mut v_val_452_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_448_);
        v_val_452_ = lean_ctor_get(v_____do__lift_447_, 0);
        lean_inc(v_val_452_);
        lean_dec_ref_known(v_____do__lift_447_, 1);
        v___x_453_ = lean_apply_1(v_h__2_449_, v_val_452_);
        return v___x_453_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(
    mut v_00_u03b2_454_: *mut LeanObject,
    mut v_motive_455_: *mut LeanObject,
    mut v_____do__lift_456_: *mut LeanObject,
    mut v_h__1_457_: *mut LeanObject,
    mut v_h__2_458_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_456_) == 0 {
        let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_458_);
        v___x_459_ = lean_box(0);
        v___x_460_ = lean_apply_1(v_h__1_457_, v___x_459_);
        return v___x_460_;
    } else {
        let mut v_val_461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_457_);
        v_val_461_ = lean_ctor_get(v_____do__lift_456_, 0);
        lean_inc(v_val_461_);
        lean_dec_ref_known(v_____do__lift_456_, 1);
        v___x_462_ = lean_apply_1(v_h__2_458_, v_val_461_);
        return v___x_462_;
    }
}
pub unsafe fn l_List_zipWithM_x27___redArg___lam__0(
    mut v_z_463_: *mut LeanObject,
    mut v_toPure_464_: *mut LeanObject,
    mut v_zs_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_466_, 0, v_z_463_);
    lean_ctor_set(v___x_466_, 1, v_zs_465_);
    v___x_467_ = lean_apply_2(v_toPure_464_, lean_box(0), v___x_466_);
    return v___x_467_;
}
pub unsafe fn l_List_zipWithM_x27___redArg(
    mut v_inst_468_: *mut LeanObject,
    mut v_f_469_: *mut LeanObject,
    mut v_x_470_: *mut LeanObject,
    mut v_x_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_472_ = lean_ctor_get(v_inst_468_, 0);
                v_toBind_473_ = lean_ctor_get(v_inst_468_, 1);
                lean_inc(v_toBind_473_);
                v_toPure_474_ = lean_ctor_get(v_toApplicative_472_, 1);
                lean_inc(v_toPure_474_);
                if lean_obj_tag(v_x_470_) == 1 {
                    if lean_obj_tag(v_x_471_) == 1 {
                        v_head_478_ = lean_ctor_get(v_x_470_, 0);
                        lean_inc(v_head_478_);
                        v_tail_479_ = lean_ctor_get(v_x_470_, 1);
                        lean_inc(v_tail_479_);
                        lean_dec_ref_known(v_x_470_, 2);
                        v_head_480_ = lean_ctor_get(v_x_471_, 0);
                        lean_inc(v_head_480_);
                        v_tail_481_ = lean_ctor_get(v_x_471_, 1);
                        lean_inc(v_tail_481_);
                        lean_dec_ref_known(v_x_471_, 2);
                        lean_inc(v_toBind_473_);
                        lean_inc(v_f_469_);
                        v___f_482_ = lean_alloc_closure(
                            l_List_zipWithM_x27___redArg___lam__1 as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        lean_closure_set(v___f_482_, 0, v_toPure_474_);
                        lean_closure_set(v___f_482_, 1, v_inst_468_);
                        lean_closure_set(v___f_482_, 2, v_f_469_);
                        lean_closure_set(v___f_482_, 3, v_tail_479_);
                        lean_closure_set(v___f_482_, 4, v_tail_481_);
                        lean_closure_set(v___f_482_, 5, v_toBind_473_);
                        v___x_483_ = lean_apply_2(v_f_469_, v_head_478_, v_head_480_);
                        v___x_484_ = lean_apply_4(
                            v_toBind_473_,
                            lean_box(0),
                            lean_box(0),
                            v___x_483_,
                            v___f_482_,
                        );
                        return v___x_484_;
                    } else {
                        lean_dec_ref_known(v_x_470_, 2);
                        lean_dec(v_toBind_473_);
                        lean_dec(v_x_471_);
                        lean_dec(v_f_469_);
                        lean_dec_ref(v_inst_468_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_toBind_473_);
                    lean_dec(v_x_471_);
                    lean_dec(v_x_470_);
                    lean_dec(v_f_469_);
                    lean_dec_ref(v_inst_468_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_476_ = lean_box(0);
                v___x_477_ = lean_apply_2(v_toPure_474_, lean_box(0), v___x_476_);
                return v___x_477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithM_x27___redArg___lam__1(
    mut v_toPure_485_: *mut LeanObject,
    mut v_inst_486_: *mut LeanObject,
    mut v_f_487_: *mut LeanObject,
    mut v_tail_488_: *mut LeanObject,
    mut v_tail_489_: *mut LeanObject,
    mut v_toBind_490_: *mut LeanObject,
    mut v_z_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___f_492_ = lean_alloc_closure(
        l_List_zipWithM_x27___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_492_, 0, v_z_491_);
    lean_closure_set(v___f_492_, 1, v_toPure_485_);
    v___x_493_ = l_List_zipWithM_x27___redArg(v_inst_486_, v_f_487_, v_tail_488_, v_tail_489_);
    v___x_494_ = lean_apply_4(
        v_toBind_490_,
        lean_box(0),
        lean_box(0),
        v___x_493_,
        v___f_492_,
    );
    return v___x_494_;
}
pub unsafe fn l_List_zipWithM_x27(
    mut v_m_495_: *mut LeanObject,
    mut v_inst_496_: *mut LeanObject,
    mut v_00_u03b1_497_: *mut LeanObject,
    mut v_00_u03b2_498_: *mut LeanObject,
    mut v_00_u03b3_499_: *mut LeanObject,
    mut v_f_500_: *mut LeanObject,
    mut v_x_501_: *mut LeanObject,
    mut v_x_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = l_List_zipWithM_x27___redArg(v_inst_496_, v_f_500_, v_x_501_, v_x_502_);
    return v___x_503_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter___redArg(
    mut v_x_504_: *mut LeanObject,
    mut v_x_505_: *mut LeanObject,
    mut v_h__1_506_: *mut LeanObject,
    mut v_h__2_507_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_504_) == 1 {
        if lean_obj_tag(v_x_505_) == 1 {
            let mut v_head_508_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_509_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_510_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_511_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_507_);
            v_head_508_ = lean_ctor_get(v_x_504_, 0);
            lean_inc(v_head_508_);
            v_tail_509_ = lean_ctor_get(v_x_504_, 1);
            lean_inc(v_tail_509_);
            lean_dec_ref_known(v_x_504_, 2);
            v_head_510_ = lean_ctor_get(v_x_505_, 0);
            lean_inc(v_head_510_);
            v_tail_511_ = lean_ctor_get(v_x_505_, 1);
            lean_inc(v_tail_511_);
            lean_dec_ref_known(v_x_505_, 2);
            v___x_512_ = lean_apply_4(
                v_h__1_506_,
                v_head_508_,
                v_tail_509_,
                v_head_510_,
                v_tail_511_,
            );
            return v___x_512_;
        } else {
            let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_506_);
            v___x_513_ = lean_apply_3(v_h__2_507_, v_x_504_, v_x_505_, lean_box(0));
            return v___x_513_;
        }
    } else {
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_506_);
        v___x_514_ = lean_apply_3(v_h__2_507_, v_x_504_, v_x_505_, lean_box(0));
        return v___x_514_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter(
    mut v_00_u03b1_515_: *mut LeanObject,
    mut v_00_u03b2_516_: *mut LeanObject,
    mut v_motive_517_: *mut LeanObject,
    mut v_x_518_: *mut LeanObject,
    mut v_x_519_: *mut LeanObject,
    mut v_h__1_520_: *mut LeanObject,
    mut v_h__2_521_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_518_) == 1 {
        if lean_obj_tag(v_x_519_) == 1 {
            let mut v_head_522_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_523_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_524_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_525_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_521_);
            v_head_522_ = lean_ctor_get(v_x_518_, 0);
            lean_inc(v_head_522_);
            v_tail_523_ = lean_ctor_get(v_x_518_, 1);
            lean_inc(v_tail_523_);
            lean_dec_ref_known(v_x_518_, 2);
            v_head_524_ = lean_ctor_get(v_x_519_, 0);
            lean_inc(v_head_524_);
            v_tail_525_ = lean_ctor_get(v_x_519_, 1);
            lean_inc(v_tail_525_);
            lean_dec_ref_known(v_x_519_, 2);
            v___x_526_ = lean_apply_4(
                v_h__1_520_,
                v_head_522_,
                v_tail_523_,
                v_head_524_,
                v_tail_525_,
            );
            return v___x_526_;
        } else {
            let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_520_);
            v___x_527_ = lean_apply_3(v_h__2_521_, v_x_518_, v_x_519_, lean_box(0));
            return v___x_527_;
        }
    } else {
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_520_);
        v___x_528_ = lean_apply_3(v_h__2_521_, v_x_518_, v_x_519_, lean_box(0));
        return v___x_528_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter___redArg(
    mut v_x_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
    mut v_x_531_: *mut LeanObject,
    mut v_h__1_532_: *mut LeanObject,
    mut v_h__2_533_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_529_) == 1 {
        if lean_obj_tag(v_x_530_) == 1 {
            let mut v_head_534_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_535_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_536_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_537_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_533_);
            v_head_534_ = lean_ctor_get(v_x_529_, 0);
            lean_inc(v_head_534_);
            v_tail_535_ = lean_ctor_get(v_x_529_, 1);
            lean_inc(v_tail_535_);
            lean_dec_ref_known(v_x_529_, 2);
            v_head_536_ = lean_ctor_get(v_x_530_, 0);
            lean_inc(v_head_536_);
            v_tail_537_ = lean_ctor_get(v_x_530_, 1);
            lean_inc(v_tail_537_);
            lean_dec_ref_known(v_x_530_, 2);
            v___x_538_ = lean_apply_5(
                v_h__1_532_,
                v_head_534_,
                v_tail_535_,
                v_head_536_,
                v_tail_537_,
                v_x_531_,
            );
            return v___x_538_;
        } else {
            let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_532_);
            v___x_539_ = lean_apply_4(v_h__2_533_, v_x_529_, v_x_530_, v_x_531_, lean_box(0));
            return v___x_539_;
        }
    } else {
        let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_532_);
        v___x_540_ = lean_apply_4(v_h__2_533_, v_x_529_, v_x_530_, v_x_531_, lean_box(0));
        return v___x_540_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter(
    mut v_00_u03b1_541_: *mut LeanObject,
    mut v_00_u03b2_542_: *mut LeanObject,
    mut v_00_u03b3_543_: *mut LeanObject,
    mut v_motive_544_: *mut LeanObject,
    mut v_x_545_: *mut LeanObject,
    mut v_x_546_: *mut LeanObject,
    mut v_x_547_: *mut LeanObject,
    mut v_h__1_548_: *mut LeanObject,
    mut v_h__2_549_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_545_) == 1 {
        if lean_obj_tag(v_x_546_) == 1 {
            let mut v_head_550_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_551_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_552_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_553_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_549_);
            v_head_550_ = lean_ctor_get(v_x_545_, 0);
            lean_inc(v_head_550_);
            v_tail_551_ = lean_ctor_get(v_x_545_, 1);
            lean_inc(v_tail_551_);
            lean_dec_ref_known(v_x_545_, 2);
            v_head_552_ = lean_ctor_get(v_x_546_, 0);
            lean_inc(v_head_552_);
            v_tail_553_ = lean_ctor_get(v_x_546_, 1);
            lean_inc(v_tail_553_);
            lean_dec_ref_known(v_x_546_, 2);
            v___x_554_ = lean_apply_5(
                v_h__1_548_,
                v_head_550_,
                v_tail_551_,
                v_head_552_,
                v_tail_553_,
                v_x_547_,
            );
            return v___x_554_;
        } else {
            let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_548_);
            v___x_555_ = lean_apply_4(v_h__2_549_, v_x_545_, v_x_546_, v_x_547_, lean_box(0));
            return v___x_555_;
        }
    } else {
        let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_548_);
        v___x_556_ = lean_apply_4(v_h__2_549_, v_x_545_, v_x_546_, v_x_547_, lean_box(0));
        return v___x_556_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(
    mut v_x_557_: *mut LeanObject,
    mut v_x_558_: *mut LeanObject,
    mut v_h__1_559_: *mut LeanObject,
    mut v_h__2_560_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_557_) == 0 {
        let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_560_);
        v___x_561_ = lean_apply_1(v_h__1_559_, v_x_558_);
        return v___x_561_;
    } else {
        let mut v_head_562_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_559_);
        v_head_562_ = lean_ctor_get(v_x_557_, 0);
        lean_inc(v_head_562_);
        v_tail_563_ = lean_ctor_get(v_x_557_, 1);
        lean_inc(v_tail_563_);
        lean_dec_ref_known(v_x_557_, 2);
        v___x_564_ = lean_apply_3(v_h__2_560_, v_head_562_, v_tail_563_, v_x_558_);
        return v___x_564_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter(
    mut v_00_u03b1_565_: *mut LeanObject,
    mut v_00_u03b2_566_: *mut LeanObject,
    mut v_motive_567_: *mut LeanObject,
    mut v_x_568_: *mut LeanObject,
    mut v_x_569_: *mut LeanObject,
    mut v_h__1_570_: *mut LeanObject,
    mut v_h__2_571_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_568_) == 0 {
        let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_571_);
        v___x_572_ = lean_apply_1(v_h__1_570_, v_x_569_);
        return v___x_572_;
    } else {
        let mut v_head_573_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_570_);
        v_head_573_ = lean_ctor_get(v_x_568_, 0);
        lean_inc(v_head_573_);
        v_tail_574_ = lean_ctor_get(v_x_568_, 1);
        lean_inc(v_tail_574_);
        lean_dec_ref_known(v_x_568_, 2);
        v___x_575_ = lean_apply_3(v_h__2_571_, v_head_573_, v_tail_574_, v_x_569_);
        return v___x_575_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_576_: *mut LeanObject,
    mut v_h__1_577_: *mut LeanObject,
    mut v_h__2_578_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_576_) == 0 {
        let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_578_);
        v___x_579_ = lean_box(0);
        v___x_580_ = lean_apply_1(v_h__1_577_, v___x_579_);
        return v___x_580_;
    } else {
        let mut v_val_581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_577_);
        v_val_581_ = lean_ctor_get(v_x_576_, 0);
        lean_inc(v_val_581_);
        lean_dec_ref_known(v_x_576_, 1);
        v___x_582_ = lean_apply_1(v_h__2_578_, v_val_581_);
        return v___x_582_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_583_: *mut LeanObject,
    mut v_motive_584_: *mut LeanObject,
    mut v_x_585_: *mut LeanObject,
    mut v_h__1_586_: *mut LeanObject,
    mut v_h__2_587_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_585_) == 0 {
        let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_587_);
        v___x_588_ = lean_box(0);
        v___x_589_ = lean_apply_1(v_h__1_586_, v___x_588_);
        return v___x_589_;
    } else {
        let mut v_val_590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_586_);
        v_val_590_ = lean_ctor_get(v_x_585_, 0);
        lean_inc(v_val_590_);
        lean_dec_ref_known(v_x_585_, 1);
        v___x_591_ = lean_apply_1(v_h__2_587_, v_val_590_);
        return v___x_591_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_592_: *mut LeanObject,
    mut v_h__1_593_: *mut LeanObject,
    mut v_h__2_594_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_592_) == 0 {
        let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_593_);
        v___x_595_ = lean_box(0);
        v___x_596_ = lean_apply_1(v_h__2_594_, v___x_595_);
        return v___x_596_;
    } else {
        let mut v_val_597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_594_);
        v_val_597_ = lean_ctor_get(v_x_592_, 0);
        lean_inc(v_val_597_);
        lean_dec_ref_known(v_x_592_, 1);
        v___x_598_ = lean_apply_1(v_h__1_593_, v_val_597_);
        return v___x_598_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_599_: *mut LeanObject,
    mut v_motive_600_: *mut LeanObject,
    mut v_x_601_: *mut LeanObject,
    mut v_h__1_602_: *mut LeanObject,
    mut v_h__2_603_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_601_) == 0 {
        let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_602_);
        v___x_604_ = lean_box(0);
        v___x_605_ = lean_apply_1(v_h__2_603_, v___x_604_);
        return v___x_605_;
    } else {
        let mut v_val_606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_603_);
        v_val_606_ = lean_ctor_get(v_x_601_, 0);
        lean_inc(v_val_606_);
        lean_dec_ref_known(v_x_601_, 1);
        v___x_607_ = lean_apply_1(v_h__1_602_, v_val_606_);
        return v___x_607_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___redArg(
    mut v_x_608_: *mut LeanObject,
    mut v_x_609_: *mut LeanObject,
    mut v_h__1_610_: *mut LeanObject,
    mut v_h__2_611_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_608_) == 0 {
        let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_611_);
        v___x_612_ = lean_apply_2(v_h__1_610_, v_x_609_, lean_box(0));
        return v___x_612_;
    } else {
        let mut v_head_613_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_614_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_610_);
        v_head_613_ = lean_ctor_get(v_x_608_, 0);
        lean_inc(v_head_613_);
        v_tail_614_ = lean_ctor_get(v_x_608_, 1);
        lean_inc(v_tail_614_);
        lean_dec_ref_known(v_x_608_, 2);
        v___x_615_ = lean_apply_4(v_h__2_611_, v_head_613_, v_tail_614_, v_x_609_, lean_box(0));
        return v___x_615_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(
    mut v_00_u03b1_616_: *mut LeanObject,
    mut v_00_u03b2_617_: *mut LeanObject,
    mut v_as_618_: *mut LeanObject,
    mut v_motive_619_: *mut LeanObject,
    mut v_x_620_: *mut LeanObject,
    mut v_x_621_: *mut LeanObject,
    mut v_x_622_: *mut LeanObject,
    mut v_h__1_623_: *mut LeanObject,
    mut v_h__2_624_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_620_) == 0 {
        let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_624_);
        v___x_625_ = lean_apply_2(v_h__1_623_, v_x_621_, lean_box(0));
        return v___x_625_;
    } else {
        let mut v_head_626_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_623_);
        v_head_626_ = lean_ctor_get(v_x_620_, 0);
        lean_inc(v_head_626_);
        v_tail_627_ = lean_ctor_get(v_x_620_, 1);
        lean_inc(v_tail_627_);
        lean_dec_ref_known(v_x_620_, 2);
        v___x_628_ = lean_apply_4(v_h__2_624_, v_head_626_, v_tail_627_, v_x_621_, lean_box(0));
        return v___x_628_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___boxed(
    mut v_00_u03b1_629_: *mut LeanObject,
    mut v_00_u03b2_630_: *mut LeanObject,
    mut v_as_631_: *mut LeanObject,
    mut v_motive_632_: *mut LeanObject,
    mut v_x_633_: *mut LeanObject,
    mut v_x_634_: *mut LeanObject,
    mut v_x_635_: *mut LeanObject,
    mut v_h__1_636_: *mut LeanObject,
    mut v_h__2_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_638_: *mut LeanObject = core::ptr::null_mut();
    v_res_638_ = l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(
        v_00_u03b1_629_,
        v_00_u03b2_630_,
        v_as_631_,
        v_motive_632_,
        v_x_633_,
        v_x_634_,
        v_x_635_,
        v_h__1_636_,
        v_h__2_637_,
    );
    lean_dec(v_as_631_);
    return v_res_638_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(
    mut v_____do__lift_639_: *mut LeanObject,
    mut v_h__1_640_: *mut LeanObject,
    mut v_h__2_641_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_639_) == 0 {
        let mut v_a_642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_641_);
        v_a_642_ = lean_ctor_get(v_____do__lift_639_, 0);
        lean_inc(v_a_642_);
        lean_dec_ref_known(v_____do__lift_639_, 1);
        v___x_643_ = lean_apply_1(v_h__1_640_, v_a_642_);
        return v___x_643_;
    } else {
        let mut v_a_644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_640_);
        v_a_644_ = lean_ctor_get(v_____do__lift_639_, 0);
        lean_inc(v_a_644_);
        lean_dec_ref_known(v_____do__lift_639_, 1);
        v___x_645_ = lean_apply_1(v_h__2_641_, v_a_644_);
        return v___x_645_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b2_646_: *mut LeanObject,
    mut v_motive_647_: *mut LeanObject,
    mut v_____do__lift_648_: *mut LeanObject,
    mut v_h__1_649_: *mut LeanObject,
    mut v_h__2_650_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_648_) == 0 {
        let mut v_a_651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_650_);
        v_a_651_ = lean_ctor_get(v_____do__lift_648_, 0);
        lean_inc(v_a_651_);
        lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_652_ = lean_apply_1(v_h__1_649_, v_a_651_);
        return v___x_652_;
    } else {
        let mut v_a_653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_649_);
        v_a_653_ = lean_ctor_get(v_____do__lift_648_, 0);
        lean_inc(v_a_653_);
        lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_654_ = lean_apply_1(v_h__2_650_, v_a_653_);
        return v___x_654_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_655_: *mut LeanObject,
    mut v_h__1_656_: *mut LeanObject,
    mut v_h__2_657_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_655_) == 0 {
        let mut v_a_658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_657_);
        v_a_658_ = lean_ctor_get(v_x_655_, 0);
        lean_inc(v_a_658_);
        lean_dec_ref_known(v_x_655_, 1);
        v___x_659_ = lean_apply_1(v_h__1_656_, v_a_658_);
        return v___x_659_;
    } else {
        let mut v_a_660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_656_);
        v_a_660_ = lean_ctor_get(v_x_655_, 0);
        lean_inc(v_a_660_);
        lean_dec_ref_known(v_x_655_, 1);
        v___x_661_ = lean_apply_1(v_h__2_657_, v_a_660_);
        return v___x_661_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_662_: *mut LeanObject,
    mut v_motive_663_: *mut LeanObject,
    mut v_x_664_: *mut LeanObject,
    mut v_h__1_665_: *mut LeanObject,
    mut v_h__2_666_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_664_) == 0 {
        let mut v_a_667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_666_);
        v_a_667_ = lean_ctor_get(v_x_664_, 0);
        lean_inc(v_a_667_);
        lean_dec_ref_known(v_x_664_, 1);
        v___x_668_ = lean_apply_1(v_h__1_665_, v_a_667_);
        return v___x_668_;
    } else {
        let mut v_a_669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_665_);
        v_a_669_ = lean_ctor_get(v_x_664_, 0);
        lean_inc(v_a_669_);
        lean_dec_ref_known(v_x_664_, 1);
        v___x_670_ = lean_apply_1(v_h__2_666_, v_a_669_);
        return v___x_670_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_671_: *mut LeanObject,
    mut v_h__1_672_: *mut LeanObject,
    mut v_h__2_673_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_671_) == 0 {
        let mut v_a_674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_672_);
        v_a_674_ = lean_ctor_get(v_b_671_, 0);
        lean_inc(v_a_674_);
        lean_dec_ref_known(v_b_671_, 1);
        v___x_675_ = lean_apply_1(v_h__2_673_, v_a_674_);
        return v___x_675_;
    } else {
        let mut v_a_676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_673_);
        v_a_676_ = lean_ctor_get(v_b_671_, 0);
        lean_inc(v_a_676_);
        lean_dec_ref_known(v_b_671_, 1);
        v___x_677_ = lean_apply_1(v_h__1_672_, v_a_676_);
        return v___x_677_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_678_: *mut LeanObject,
    mut v_motive_679_: *mut LeanObject,
    mut v_b_680_: *mut LeanObject,
    mut v_h__1_681_: *mut LeanObject,
    mut v_h__2_682_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_680_) == 0 {
        let mut v_a_683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_681_);
        v_a_683_ = lean_ctor_get(v_b_680_, 0);
        lean_inc(v_a_683_);
        lean_dec_ref_known(v_b_680_, 1);
        v___x_684_ = lean_apply_1(v_h__2_682_, v_a_683_);
        return v___x_684_;
    } else {
        let mut v_a_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_682_);
        v_a_685_ = lean_ctor_get(v_b_680_, 0);
        lean_inc(v_a_685_);
        lean_dec_ref_known(v_b_680_, 1);
        v___x_686_ = lean_apply_1(v_h__1_681_, v_a_685_);
        return v___x_686_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter___redArg(
    mut v_x_687_: *mut LeanObject,
    mut v_h__1_688_: *mut LeanObject,
    mut v_h__2_689_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_687_) == 0 {
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_689_);
        v___x_690_ = lean_box(0);
        v___x_691_ = lean_apply_1(v_h__1_688_, v___x_690_);
        return v___x_691_;
    } else {
        let mut v_head_692_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_688_);
        v_head_692_ = lean_ctor_get(v_x_687_, 0);
        lean_inc(v_head_692_);
        v_tail_693_ = lean_ctor_get(v_x_687_, 1);
        lean_inc(v_tail_693_);
        lean_dec_ref_known(v_x_687_, 2);
        v___x_694_ = lean_apply_2(v_h__2_689_, v_head_692_, v_tail_693_);
        return v___x_694_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_695_: *mut LeanObject,
    mut v_motive_696_: *mut LeanObject,
    mut v_x_697_: *mut LeanObject,
    mut v_h__1_698_: *mut LeanObject,
    mut v_h__2_699_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_697_) == 0 {
        let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_699_);
        v___x_700_ = lean_box(0);
        v___x_701_ = lean_apply_1(v_h__1_698_, v___x_700_);
        return v___x_701_;
    } else {
        let mut v_head_702_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_698_);
        v_head_702_ = lean_ctor_get(v_x_697_, 0);
        lean_inc(v_head_702_);
        v_tail_703_ = lean_ctor_get(v_x_697_, 1);
        lean_inc(v_tail_703_);
        lean_dec_ref_known(v_x_697_, 2);
        v___x_704_ = lean_apply_2(v_h__2_699_, v_head_702_, v_tail_703_);
        return v___x_704_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_705_: u8,
    mut v_h__1_706_: *mut LeanObject,
    mut v_h__2_707_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_705_ == 0 {
        let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_706_);
        v___x_708_ = lean_box(0);
        v___x_709_ = lean_apply_1(v_h__2_707_, v___x_708_);
        return v___x_709_;
    } else {
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_707_);
        v___x_710_ = lean_box(0);
        v___x_711_ = lean_apply_1(v_h__1_706_, v___x_710_);
        return v___x_711_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_712_: *mut LeanObject,
    mut v_h__1_713_: *mut LeanObject,
    mut v_h__2_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_26__boxed_715_: u8 = 0;
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_715_ = (lean_unbox(v_____do__lift_712_) as u8);
    v_res_716_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_715_,
        v_h__1_713_,
        v_h__2_714_,
    );
    return v_res_716_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(
    mut v_motive_717_: *mut LeanObject,
    mut v_____do__lift_718_: u8,
    mut v_h__1_719_: *mut LeanObject,
    mut v_h__2_720_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_718_ == 0 {
        let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_719_);
        v___x_721_ = lean_box(0);
        v___x_722_ = lean_apply_1(v_h__2_720_, v___x_721_);
        return v___x_722_;
    } else {
        let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_720_);
        v___x_723_ = lean_box(0);
        v___x_724_ = lean_apply_1(v_h__1_719_, v___x_723_);
        return v___x_724_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_725_: *mut LeanObject,
    mut v_____do__lift_726_: *mut LeanObject,
    mut v_h__1_727_: *mut LeanObject,
    mut v_h__2_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_37__boxed_729_: u8 = 0;
    let mut v_res_730_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_729_ = (lean_unbox(v_____do__lift_726_) as u8);
    v_res_730_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(
        v_motive_725_,
        v_____do__lift_37__boxed_729_,
        v_h__1_727_,
        v_h__2_728_,
    );
    return v_res_730_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(
    mut v_____do__lift_731_: *mut LeanObject,
    mut v_h__1_732_: *mut LeanObject,
    mut v_h__2_733_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_731_) == 0 {
        let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_733_);
        v___x_734_ = lean_box(0);
        v___x_735_ = lean_apply_1(v_h__1_732_, v___x_734_);
        return v___x_735_;
    } else {
        let mut v_val_736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_732_);
        v_val_736_ = lean_ctor_get(v_____do__lift_731_, 0);
        lean_inc(v_val_736_);
        lean_dec_ref_known(v_____do__lift_731_, 1);
        v___x_737_ = lean_apply_1(v_h__2_733_, v_val_736_);
        return v___x_737_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter(
    mut v_00_u03b2_738_: *mut LeanObject,
    mut v_motive_739_: *mut LeanObject,
    mut v_____do__lift_740_: *mut LeanObject,
    mut v_h__1_741_: *mut LeanObject,
    mut v_h__2_742_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_740_) == 0 {
        let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_742_);
        v___x_743_ = lean_box(0);
        v___x_744_ = lean_apply_1(v_h__1_741_, v___x_743_);
        return v___x_744_;
    } else {
        let mut v_val_745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_741_);
        v_val_745_ = lean_ctor_get(v_____do__lift_740_, 0);
        lean_inc(v_val_745_);
        lean_dec_ref_known(v_____do__lift_740_, 1);
        v___x_746_ = lean_apply_1(v_h__2_742_, v_val_745_);
        return v___x_746_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Monadic(builtin);
}
