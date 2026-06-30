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
pub unsafe fn l_List_mapM_x27___redArg___lam__0(
    mut v_____do__lift_374_: *mut leanh::LeanObject,
    mut v_toPure_375_: *mut leanh::LeanObject,
    mut v_____do__lift_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_377_, 0, v_____do__lift_374_);
    leanh::lean_ctor_set(v___x_377_, 1, v_____do__lift_376_);
    v___x_378_ = leanh::lean_apply_2(v_toPure_375_, leanh::lean_box(0), v___x_377_);
    return v___x_378_;
}
pub unsafe fn l_List_mapM_x27___redArg(
    mut v_inst_379_: *mut leanh::LeanObject,
    mut v_f_380_: *mut leanh::LeanObject,
    mut v_x_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_381_) == 0 {
        let mut v_toApplicative_382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_382_ = leanh::lean_ctor_get(v_inst_379_, 0);
        leanh::lean_inc_ref(v_toApplicative_382_);
        leanh::lean_dec(v_f_380_);
        leanh::lean_dec_ref(v_inst_379_);
        v_toPure_383_ = leanh::lean_ctor_get(v_toApplicative_382_, 1);
        leanh::lean_inc(v_toPure_383_);
        leanh::lean_dec_ref(v_toApplicative_382_);
        v___x_384_ = leanh::lean_box(0);
        v___x_385_ =
            leanh::lean_apply_2(v_toPure_383_, leanh::lean_box(0), v___x_384_);
        return v___x_385_;
    } else {
        let mut v_toApplicative_386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_386_ = leanh::lean_ctor_get(v_inst_379_, 0);
        v_toBind_387_ = leanh::lean_ctor_get(v_inst_379_, 1);
        leanh::lean_inc_n(v_toBind_387_, 2);
        v_toPure_388_ = leanh::lean_ctor_get(v_toApplicative_386_, 1);
        leanh::lean_inc(v_toPure_388_);
        v_head_389_ = leanh::lean_ctor_get(v_x_381_, 0);
        leanh::lean_inc(v_head_389_);
        v_tail_390_ = leanh::lean_ctor_get(v_x_381_, 1);
        leanh::lean_inc(v_tail_390_);
        leanh::lean_dec_ref_known(v_x_381_, 2);
        leanh::lean_inc(v_f_380_);
        v___f_391_ = leanh::lean_alloc_closure(
            l_List_mapM_x27___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_391_, 0, v_toPure_388_);
        leanh::lean_closure_set(v___f_391_, 1, v_inst_379_);
        leanh::lean_closure_set(v___f_391_, 2, v_f_380_);
        leanh::lean_closure_set(v___f_391_, 3, v_tail_390_);
        leanh::lean_closure_set(v___f_391_, 4, v_toBind_387_);
        v___x_392_ = leanh::lean_apply_1(v_f_380_, v_head_389_);
        v___x_393_ = leanh::lean_apply_4(
            v_toBind_387_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_392_,
            v___f_391_,
        );
        return v___x_393_;
    }
}
pub unsafe fn l_List_mapM_x27___redArg___lam__1(
    mut v_toPure_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_f_396_: *mut leanh::LeanObject,
    mut v_tail_397_: *mut leanh::LeanObject,
    mut v_toBind_398_: *mut leanh::LeanObject,
    mut v_____do__lift_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_400_ = leanh::lean_alloc_closure(
        l_List_mapM_x27___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_400_, 0, v_____do__lift_399_);
    leanh::lean_closure_set(v___f_400_, 1, v_toPure_394_);
    v___x_401_ = l_List_mapM_x27___redArg(v_inst_395_, v_f_396_, v_tail_397_);
    v___x_402_ = leanh::lean_apply_4(
        v_toBind_398_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_401_,
        v___f_400_,
    );
    return v___x_402_;
}
pub unsafe fn l_List_mapM_x27(
    mut v_m_403_: *mut leanh::LeanObject,
    mut v_00_u03b1_404_: *mut leanh::LeanObject,
    mut v_00_u03b2_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_f_407_: *mut leanh::LeanObject,
    mut v_x_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = l_List_mapM_x27___redArg(v_inst_406_, v_f_407_, v_x_408_);
    return v___x_409_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter___redArg(
    mut v_x_410_: *mut leanh::LeanObject,
    mut v_x_411_: *mut leanh::LeanObject,
    mut v_h__1_412_: *mut leanh::LeanObject,
    mut v_h__2_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_410_) == 0 {
        let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_413_);
        v___x_414_ = leanh::lean_apply_1(v_h__1_412_, v_x_411_);
        return v___x_414_;
    } else {
        let mut v_head_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_412_);
        v_head_415_ = leanh::lean_ctor_get(v_x_410_, 0);
        leanh::lean_inc(v_head_415_);
        v_tail_416_ = leanh::lean_ctor_get(v_x_410_, 1);
        leanh::lean_inc(v_tail_416_);
        leanh::lean_dec_ref_known(v_x_410_, 2);
        v___x_417_ = leanh::lean_apply_3(v_h__2_413_, v_head_415_, v_tail_416_, v_x_411_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_match__1_splitter(
    mut v_00_u03b1_418_: *mut leanh::LeanObject,
    mut v_00_u03b2_419_: *mut leanh::LeanObject,
    mut v_motive_420_: *mut leanh::LeanObject,
    mut v_x_421_: *mut leanh::LeanObject,
    mut v_x_422_: *mut leanh::LeanObject,
    mut v_h__1_423_: *mut leanh::LeanObject,
    mut v_h__2_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_421_) == 0 {
        let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_424_);
        v___x_425_ = leanh::lean_apply_1(v_h__1_423_, v_x_422_);
        return v___x_425_;
    } else {
        let mut v_head_426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_423_);
        v_head_426_ = leanh::lean_ctor_get(v_x_421_, 0);
        leanh::lean_inc(v_head_426_);
        v_tail_427_ = leanh::lean_ctor_get(v_x_421_, 1);
        leanh::lean_inc(v_tail_427_);
        leanh::lean_dec_ref_known(v_x_421_, 2);
        v___x_428_ = leanh::lean_apply_3(v_h__2_424_, v_head_426_, v_tail_427_, v_x_422_);
        return v___x_428_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter___redArg(
    mut v_x_429_: *mut leanh::LeanObject,
    mut v_h__1_430_: *mut leanh::LeanObject,
    mut v_h__2_431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_429_) == 0 {
        let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_431_);
        v___x_432_ = leanh::lean_box(0);
        v___x_433_ = leanh::lean_apply_1(v_h__1_430_, v___x_432_);
        return v___x_433_;
    } else {
        let mut v_head_434_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_430_);
        v_head_434_ = leanh::lean_ctor_get(v_x_429_, 0);
        leanh::lean_inc(v_head_434_);
        v_tail_435_ = leanh::lean_ctor_get(v_x_429_, 1);
        leanh::lean_inc(v_tail_435_);
        leanh::lean_dec_ref_known(v_x_429_, 2);
        v___x_436_ = leanh::lean_apply_2(v_h__2_431_, v_head_434_, v_tail_435_);
        return v___x_436_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapM_x27_match__1_splitter(
    mut v_00_u03b1_437_: *mut leanh::LeanObject,
    mut v_motive_438_: *mut leanh::LeanObject,
    mut v_x_439_: *mut leanh::LeanObject,
    mut v_h__1_440_: *mut leanh::LeanObject,
    mut v_h__2_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_439_) == 0 {
        let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_441_);
        v___x_442_ = leanh::lean_box(0);
        v___x_443_ = leanh::lean_apply_1(v_h__1_440_, v___x_442_);
        return v___x_443_;
    } else {
        let mut v_head_444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_440_);
        v_head_444_ = leanh::lean_ctor_get(v_x_439_, 0);
        leanh::lean_inc(v_head_444_);
        v_tail_445_ = leanh::lean_ctor_get(v_x_439_, 1);
        leanh::lean_inc(v_tail_445_);
        leanh::lean_dec_ref_known(v_x_439_, 2);
        v___x_446_ = leanh::lean_apply_2(v_h__2_441_, v_head_444_, v_tail_445_);
        return v___x_446_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_447_: *mut leanh::LeanObject,
    mut v_h__1_448_: *mut leanh::LeanObject,
    mut v_h__2_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_447_) == 0 {
        let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_449_);
        v___x_450_ = leanh::lean_box(0);
        v___x_451_ = leanh::lean_apply_1(v_h__1_448_, v___x_450_);
        return v___x_451_;
    } else {
        let mut v_val_452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_448_);
        v_val_452_ = leanh::lean_ctor_get(v_____do__lift_447_, 0);
        leanh::lean_inc(v_val_452_);
        leanh::lean_dec_ref_known(v_____do__lift_447_, 1);
        v___x_453_ = leanh::lean_apply_1(v_h__2_449_, v_val_452_);
        return v___x_453_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM_match__1_splitter(
    mut v_00_u03b2_454_: *mut leanh::LeanObject,
    mut v_motive_455_: *mut leanh::LeanObject,
    mut v_____do__lift_456_: *mut leanh::LeanObject,
    mut v_h__1_457_: *mut leanh::LeanObject,
    mut v_h__2_458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_456_) == 0 {
        let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_458_);
        v___x_459_ = leanh::lean_box(0);
        v___x_460_ = leanh::lean_apply_1(v_h__1_457_, v___x_459_);
        return v___x_460_;
    } else {
        let mut v_val_461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_457_);
        v_val_461_ = leanh::lean_ctor_get(v_____do__lift_456_, 0);
        leanh::lean_inc(v_val_461_);
        leanh::lean_dec_ref_known(v_____do__lift_456_, 1);
        v___x_462_ = leanh::lean_apply_1(v_h__2_458_, v_val_461_);
        return v___x_462_;
    }
}
pub unsafe fn l_List_zipWithM_x27___redArg___lam__0(
    mut v_z_463_: *mut leanh::LeanObject,
    mut v_toPure_464_: *mut leanh::LeanObject,
    mut v_zs_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_466_, 0, v_z_463_);
    leanh::lean_ctor_set(v___x_466_, 1, v_zs_465_);
    v___x_467_ = leanh::lean_apply_2(v_toPure_464_, leanh::lean_box(0), v___x_466_);
    return v___x_467_;
}
pub unsafe fn l_List_zipWithM_x27___redArg(
    mut v_inst_468_: *mut leanh::LeanObject,
    mut v_f_469_: *mut leanh::LeanObject,
    mut v_x_470_: *mut leanh::LeanObject,
    mut v_x_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_472_ = leanh::lean_ctor_get(v_inst_468_, 0);
                v_toBind_473_ = leanh::lean_ctor_get(v_inst_468_, 1);
                leanh::lean_inc(v_toBind_473_);
                v_toPure_474_ = leanh::lean_ctor_get(v_toApplicative_472_, 1);
                leanh::lean_inc(v_toPure_474_);
                if leanh::lean_obj_tag(v_x_470_) == 1 {
                    if leanh::lean_obj_tag(v_x_471_) == 1 {
                        v_head_478_ = leanh::lean_ctor_get(v_x_470_, 0);
                        leanh::lean_inc(v_head_478_);
                        v_tail_479_ = leanh::lean_ctor_get(v_x_470_, 1);
                        leanh::lean_inc(v_tail_479_);
                        leanh::lean_dec_ref_known(v_x_470_, 2);
                        v_head_480_ = leanh::lean_ctor_get(v_x_471_, 0);
                        leanh::lean_inc(v_head_480_);
                        v_tail_481_ = leanh::lean_ctor_get(v_x_471_, 1);
                        leanh::lean_inc(v_tail_481_);
                        leanh::lean_dec_ref_known(v_x_471_, 2);
                        leanh::lean_inc(v_toBind_473_);
                        leanh::lean_inc(v_f_469_);
                        v___f_482_ = leanh::lean_alloc_closure(
                            l_List_zipWithM_x27___redArg___lam__1 as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        leanh::lean_closure_set(v___f_482_, 0, v_toPure_474_);
                        leanh::lean_closure_set(v___f_482_, 1, v_inst_468_);
                        leanh::lean_closure_set(v___f_482_, 2, v_f_469_);
                        leanh::lean_closure_set(v___f_482_, 3, v_tail_479_);
                        leanh::lean_closure_set(v___f_482_, 4, v_tail_481_);
                        leanh::lean_closure_set(v___f_482_, 5, v_toBind_473_);
                        v___x_483_ = leanh::lean_apply_2(v_f_469_, v_head_478_, v_head_480_);
                        v___x_484_ = leanh::lean_apply_4(
                            v_toBind_473_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_483_,
                            v___f_482_,
                        );
                        return v___x_484_;
                    } else {
                        leanh::lean_dec_ref_known(v_x_470_, 2);
                        leanh::lean_dec(v_toBind_473_);
                        leanh::lean_dec(v_x_471_);
                        leanh::lean_dec(v_f_469_);
                        leanh::lean_dec_ref(v_inst_468_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toBind_473_);
                    leanh::lean_dec(v_x_471_);
                    leanh::lean_dec(v_x_470_);
                    leanh::lean_dec(v_f_469_);
                    leanh::lean_dec_ref(v_inst_468_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_476_ = leanh::lean_box(0);
                v___x_477_ = leanh::lean_apply_2(
                    v_toPure_474_,
                    leanh::lean_box(0),
                    v___x_476_,
                );
                return v___x_477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithM_x27___redArg___lam__1(
    mut v_toPure_485_: *mut leanh::LeanObject,
    mut v_inst_486_: *mut leanh::LeanObject,
    mut v_f_487_: *mut leanh::LeanObject,
    mut v_tail_488_: *mut leanh::LeanObject,
    mut v_tail_489_: *mut leanh::LeanObject,
    mut v_toBind_490_: *mut leanh::LeanObject,
    mut v_z_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_492_ = leanh::lean_alloc_closure(
        l_List_zipWithM_x27___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_492_, 0, v_z_491_);
    leanh::lean_closure_set(v___f_492_, 1, v_toPure_485_);
    v___x_493_ = l_List_zipWithM_x27___redArg(v_inst_486_, v_f_487_, v_tail_488_, v_tail_489_);
    v___x_494_ = leanh::lean_apply_4(
        v_toBind_490_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_493_,
        v___f_492_,
    );
    return v___x_494_;
}
pub unsafe fn l_List_zipWithM_x27(
    mut v_m_495_: *mut leanh::LeanObject,
    mut v_inst_496_: *mut leanh::LeanObject,
    mut v_00_u03b1_497_: *mut leanh::LeanObject,
    mut v_00_u03b2_498_: *mut leanh::LeanObject,
    mut v_00_u03b3_499_: *mut leanh::LeanObject,
    mut v_f_500_: *mut leanh::LeanObject,
    mut v_x_501_: *mut leanh::LeanObject,
    mut v_x_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = l_List_zipWithM_x27___redArg(v_inst_496_, v_f_500_, v_x_501_, v_x_502_);
    return v___x_503_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter___redArg(
    mut v_x_504_: *mut leanh::LeanObject,
    mut v_x_505_: *mut leanh::LeanObject,
    mut v_h__1_506_: *mut leanh::LeanObject,
    mut v_h__2_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_504_) == 1 {
        if leanh::lean_obj_tag(v_x_505_) == 1 {
            let mut v_head_508_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_510_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_511_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_507_);
            v_head_508_ = leanh::lean_ctor_get(v_x_504_, 0);
            leanh::lean_inc(v_head_508_);
            v_tail_509_ = leanh::lean_ctor_get(v_x_504_, 1);
            leanh::lean_inc(v_tail_509_);
            leanh::lean_dec_ref_known(v_x_504_, 2);
            v_head_510_ = leanh::lean_ctor_get(v_x_505_, 0);
            leanh::lean_inc(v_head_510_);
            v_tail_511_ = leanh::lean_ctor_get(v_x_505_, 1);
            leanh::lean_inc(v_tail_511_);
            leanh::lean_dec_ref_known(v_x_505_, 2);
            v___x_512_ = leanh::lean_apply_4(
                v_h__1_506_,
                v_head_508_,
                v_tail_509_,
                v_head_510_,
                v_tail_511_,
            );
            return v___x_512_;
        } else {
            let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_506_);
            v___x_513_ = leanh::lean_apply_3(
                v_h__2_507_,
                v_x_504_,
                v_x_505_,
                leanh::lean_box(0),
            );
            return v___x_513_;
        }
    } else {
        let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_506_);
        v___x_514_ =
            leanh::lean_apply_3(v_h__2_507_, v_x_504_, v_x_505_, leanh::lean_box(0));
        return v___x_514_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_x27_match__1_splitter(
    mut v_00_u03b1_515_: *mut leanh::LeanObject,
    mut v_00_u03b2_516_: *mut leanh::LeanObject,
    mut v_motive_517_: *mut leanh::LeanObject,
    mut v_x_518_: *mut leanh::LeanObject,
    mut v_x_519_: *mut leanh::LeanObject,
    mut v_h__1_520_: *mut leanh::LeanObject,
    mut v_h__2_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_518_) == 1 {
        if leanh::lean_obj_tag(v_x_519_) == 1 {
            let mut v_head_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_524_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_521_);
            v_head_522_ = leanh::lean_ctor_get(v_x_518_, 0);
            leanh::lean_inc(v_head_522_);
            v_tail_523_ = leanh::lean_ctor_get(v_x_518_, 1);
            leanh::lean_inc(v_tail_523_);
            leanh::lean_dec_ref_known(v_x_518_, 2);
            v_head_524_ = leanh::lean_ctor_get(v_x_519_, 0);
            leanh::lean_inc(v_head_524_);
            v_tail_525_ = leanh::lean_ctor_get(v_x_519_, 1);
            leanh::lean_inc(v_tail_525_);
            leanh::lean_dec_ref_known(v_x_519_, 2);
            v___x_526_ = leanh::lean_apply_4(
                v_h__1_520_,
                v_head_522_,
                v_tail_523_,
                v_head_524_,
                v_tail_525_,
            );
            return v___x_526_;
        } else {
            let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_520_);
            v___x_527_ = leanh::lean_apply_3(
                v_h__2_521_,
                v_x_518_,
                v_x_519_,
                leanh::lean_box(0),
            );
            return v___x_527_;
        }
    } else {
        let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_520_);
        v___x_528_ =
            leanh::lean_apply_3(v_h__2_521_, v_x_518_, v_x_519_, leanh::lean_box(0));
        return v___x_528_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter___redArg(
    mut v_x_529_: *mut leanh::LeanObject,
    mut v_x_530_: *mut leanh::LeanObject,
    mut v_x_531_: *mut leanh::LeanObject,
    mut v_h__1_532_: *mut leanh::LeanObject,
    mut v_h__2_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_529_) == 1 {
        if leanh::lean_obj_tag(v_x_530_) == 1 {
            let mut v_head_534_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_535_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_536_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_537_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_533_);
            v_head_534_ = leanh::lean_ctor_get(v_x_529_, 0);
            leanh::lean_inc(v_head_534_);
            v_tail_535_ = leanh::lean_ctor_get(v_x_529_, 1);
            leanh::lean_inc(v_tail_535_);
            leanh::lean_dec_ref_known(v_x_529_, 2);
            v_head_536_ = leanh::lean_ctor_get(v_x_530_, 0);
            leanh::lean_inc(v_head_536_);
            v_tail_537_ = leanh::lean_ctor_get(v_x_530_, 1);
            leanh::lean_inc(v_tail_537_);
            leanh::lean_dec_ref_known(v_x_530_, 2);
            v___x_538_ = leanh::lean_apply_5(
                v_h__1_532_,
                v_head_534_,
                v_tail_535_,
                v_head_536_,
                v_tail_537_,
                v_x_531_,
            );
            return v___x_538_;
        } else {
            let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_532_);
            v___x_539_ = leanh::lean_apply_4(
                v_h__2_533_,
                v_x_529_,
                v_x_530_,
                v_x_531_,
                leanh::lean_box(0),
            );
            return v___x_539_;
        }
    } else {
        let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_532_);
        v___x_540_ = leanh::lean_apply_4(
            v_h__2_533_,
            v_x_529_,
            v_x_530_,
            v_x_531_,
            leanh::lean_box(0),
        );
        return v___x_540_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_zipWithM_match__1_splitter(
    mut v_00_u03b1_541_: *mut leanh::LeanObject,
    mut v_00_u03b2_542_: *mut leanh::LeanObject,
    mut v_00_u03b3_543_: *mut leanh::LeanObject,
    mut v_motive_544_: *mut leanh::LeanObject,
    mut v_x_545_: *mut leanh::LeanObject,
    mut v_x_546_: *mut leanh::LeanObject,
    mut v_x_547_: *mut leanh::LeanObject,
    mut v_h__1_548_: *mut leanh::LeanObject,
    mut v_h__2_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_545_) == 1 {
        if leanh::lean_obj_tag(v_x_546_) == 1 {
            let mut v_head_550_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_551_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_552_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_553_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_549_);
            v_head_550_ = leanh::lean_ctor_get(v_x_545_, 0);
            leanh::lean_inc(v_head_550_);
            v_tail_551_ = leanh::lean_ctor_get(v_x_545_, 1);
            leanh::lean_inc(v_tail_551_);
            leanh::lean_dec_ref_known(v_x_545_, 2);
            v_head_552_ = leanh::lean_ctor_get(v_x_546_, 0);
            leanh::lean_inc(v_head_552_);
            v_tail_553_ = leanh::lean_ctor_get(v_x_546_, 1);
            leanh::lean_inc(v_tail_553_);
            leanh::lean_dec_ref_known(v_x_546_, 2);
            v___x_554_ = leanh::lean_apply_5(
                v_h__1_548_,
                v_head_550_,
                v_tail_551_,
                v_head_552_,
                v_tail_553_,
                v_x_547_,
            );
            return v___x_554_;
        } else {
            let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_548_);
            v___x_555_ = leanh::lean_apply_4(
                v_h__2_549_,
                v_x_545_,
                v_x_546_,
                v_x_547_,
                leanh::lean_box(0),
            );
            return v___x_555_;
        }
    } else {
        let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_548_);
        v___x_556_ = leanh::lean_apply_4(
            v_h__2_549_,
            v_x_545_,
            v_x_546_,
            v_x_547_,
            leanh::lean_box(0),
        );
        return v___x_556_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter___redArg(
    mut v_x_557_: *mut leanh::LeanObject,
    mut v_x_558_: *mut leanh::LeanObject,
    mut v_h__1_559_: *mut leanh::LeanObject,
    mut v_h__2_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_557_) == 0 {
        let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_560_);
        v___x_561_ = leanh::lean_apply_1(v_h__1_559_, v_x_558_);
        return v___x_561_;
    } else {
        let mut v_head_562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_559_);
        v_head_562_ = leanh::lean_ctor_get(v_x_557_, 0);
        leanh::lean_inc(v_head_562_);
        v_tail_563_ = leanh::lean_ctor_get(v_x_557_, 1);
        leanh::lean_inc(v_tail_563_);
        leanh::lean_dec_ref_known(v_x_557_, 2);
        v___x_564_ = leanh::lean_apply_3(v_h__2_560_, v_head_562_, v_tail_563_, v_x_558_);
        return v___x_564_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_flatMapM_match__1_splitter(
    mut v_00_u03b1_565_: *mut leanh::LeanObject,
    mut v_00_u03b2_566_: *mut leanh::LeanObject,
    mut v_motive_567_: *mut leanh::LeanObject,
    mut v_x_568_: *mut leanh::LeanObject,
    mut v_x_569_: *mut leanh::LeanObject,
    mut v_h__1_570_: *mut leanh::LeanObject,
    mut v_h__2_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_568_) == 0 {
        let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_571_);
        v___x_572_ = leanh::lean_apply_1(v_h__1_570_, v_x_569_);
        return v___x_572_;
    } else {
        let mut v_head_573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_570_);
        v_head_573_ = leanh::lean_ctor_get(v_x_568_, 0);
        leanh::lean_inc(v_head_573_);
        v_tail_574_ = leanh::lean_ctor_get(v_x_568_, 1);
        leanh::lean_inc(v_tail_574_);
        leanh::lean_dec_ref_known(v_x_568_, 2);
        v___x_575_ = leanh::lean_apply_3(v_h__2_571_, v_head_573_, v_tail_574_, v_x_569_);
        return v___x_575_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_576_: *mut leanh::LeanObject,
    mut v_h__1_577_: *mut leanh::LeanObject,
    mut v_h__2_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_576_) == 0 {
        let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_578_);
        v___x_579_ = leanh::lean_box(0);
        v___x_580_ = leanh::lean_apply_1(v_h__1_577_, v___x_579_);
        return v___x_580_;
    } else {
        let mut v_val_581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_577_);
        v_val_581_ = leanh::lean_ctor_get(v_x_576_, 0);
        leanh::lean_inc(v_val_581_);
        leanh::lean_dec_ref_known(v_x_576_, 1);
        v___x_582_ = leanh::lean_apply_1(v_h__2_578_, v_val_581_);
        return v___x_582_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_583_: *mut leanh::LeanObject,
    mut v_motive_584_: *mut leanh::LeanObject,
    mut v_x_585_: *mut leanh::LeanObject,
    mut v_h__1_586_: *mut leanh::LeanObject,
    mut v_h__2_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_585_) == 0 {
        let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_587_);
        v___x_588_ = leanh::lean_box(0);
        v___x_589_ = leanh::lean_apply_1(v_h__1_586_, v___x_588_);
        return v___x_589_;
    } else {
        let mut v_val_590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_586_);
        v_val_590_ = leanh::lean_ctor_get(v_x_585_, 0);
        leanh::lean_inc(v_val_590_);
        leanh::lean_dec_ref_known(v_x_585_, 1);
        v___x_591_ = leanh::lean_apply_1(v_h__2_587_, v_val_590_);
        return v___x_591_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_592_: *mut leanh::LeanObject,
    mut v_h__1_593_: *mut leanh::LeanObject,
    mut v_h__2_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_592_) == 0 {
        let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_593_);
        v___x_595_ = leanh::lean_box(0);
        v___x_596_ = leanh::lean_apply_1(v_h__2_594_, v___x_595_);
        return v___x_596_;
    } else {
        let mut v_val_597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_594_);
        v_val_597_ = leanh::lean_ctor_get(v_x_592_, 0);
        leanh::lean_inc(v_val_597_);
        leanh::lean_dec_ref_known(v_x_592_, 1);
        v___x_598_ = leanh::lean_apply_1(v_h__1_593_, v_val_597_);
        return v___x_598_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_599_: *mut leanh::LeanObject,
    mut v_motive_600_: *mut leanh::LeanObject,
    mut v_x_601_: *mut leanh::LeanObject,
    mut v_h__1_602_: *mut leanh::LeanObject,
    mut v_h__2_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_601_) == 0 {
        let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_602_);
        v___x_604_ = leanh::lean_box(0);
        v___x_605_ = leanh::lean_apply_1(v_h__2_603_, v___x_604_);
        return v___x_605_;
    } else {
        let mut v_val_606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_603_);
        v_val_606_ = leanh::lean_ctor_get(v_x_601_, 0);
        leanh::lean_inc(v_val_606_);
        leanh::lean_dec_ref_known(v_x_601_, 1);
        v___x_607_ = leanh::lean_apply_1(v_h__1_602_, v_val_606_);
        return v___x_607_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___redArg(
    mut v_x_608_: *mut leanh::LeanObject,
    mut v_x_609_: *mut leanh::LeanObject,
    mut v_h__1_610_: *mut leanh::LeanObject,
    mut v_h__2_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_608_) == 0 {
        let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_611_);
        v___x_612_ = leanh::lean_apply_2(v_h__1_610_, v_x_609_, leanh::lean_box(0));
        return v___x_612_;
    } else {
        let mut v_head_613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_610_);
        v_head_613_ = leanh::lean_ctor_get(v_x_608_, 0);
        leanh::lean_inc(v_head_613_);
        v_tail_614_ = leanh::lean_ctor_get(v_x_608_, 1);
        leanh::lean_inc(v_tail_614_);
        leanh::lean_dec_ref_known(v_x_608_, 2);
        v___x_615_ = leanh::lean_apply_4(
            v_h__2_611_,
            v_head_613_,
            v_tail_614_,
            v_x_609_,
            leanh::lean_box(0),
        );
        return v___x_615_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter(
    mut v_00_u03b1_616_: *mut leanh::LeanObject,
    mut v_00_u03b2_617_: *mut leanh::LeanObject,
    mut v_as_618_: *mut leanh::LeanObject,
    mut v_motive_619_: *mut leanh::LeanObject,
    mut v_x_620_: *mut leanh::LeanObject,
    mut v_x_621_: *mut leanh::LeanObject,
    mut v_x_622_: *mut leanh::LeanObject,
    mut v_h__1_623_: *mut leanh::LeanObject,
    mut v_h__2_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_620_) == 0 {
        let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_624_);
        v___x_625_ = leanh::lean_apply_2(v_h__1_623_, v_x_621_, leanh::lean_box(0));
        return v___x_625_;
    } else {
        let mut v_head_626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_623_);
        v_head_626_ = leanh::lean_ctor_get(v_x_620_, 0);
        leanh::lean_inc(v_head_626_);
        v_tail_627_ = leanh::lean_ctor_get(v_x_620_, 1);
        leanh::lean_inc(v_tail_627_);
        leanh::lean_dec_ref_known(v_x_620_, 2);
        v___x_628_ = leanh::lean_apply_4(
            v_h__2_624_,
            v_head_626_,
            v_tail_627_,
            v_x_621_,
            leanh::lean_box(0),
        );
        return v___x_628_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__5_splitter___boxed(
    mut v_00_u03b1_629_: *mut leanh::LeanObject,
    mut v_00_u03b2_630_: *mut leanh::LeanObject,
    mut v_as_631_: *mut leanh::LeanObject,
    mut v_motive_632_: *mut leanh::LeanObject,
    mut v_x_633_: *mut leanh::LeanObject,
    mut v_x_634_: *mut leanh::LeanObject,
    mut v_x_635_: *mut leanh::LeanObject,
    mut v_h__1_636_: *mut leanh::LeanObject,
    mut v_h__2_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_638_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_as_631_);
    return v_res_638_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter___redArg(
    mut v_____do__lift_639_: *mut leanh::LeanObject,
    mut v_h__1_640_: *mut leanh::LeanObject,
    mut v_h__2_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_639_) == 0 {
        let mut v_a_642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_641_);
        v_a_642_ = leanh::lean_ctor_get(v_____do__lift_639_, 0);
        leanh::lean_inc(v_a_642_);
        leanh::lean_dec_ref_known(v_____do__lift_639_, 1);
        v___x_643_ = leanh::lean_apply_1(v_h__1_640_, v_a_642_);
        return v___x_643_;
    } else {
        let mut v_a_644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_640_);
        v_a_644_ = leanh::lean_ctor_get(v_____do__lift_639_, 0);
        leanh::lean_inc(v_a_644_);
        leanh::lean_dec_ref_known(v_____do__lift_639_, 1);
        v___x_645_ = leanh::lean_apply_1(v_h__2_641_, v_a_644_);
        return v___x_645_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b2_646_: *mut leanh::LeanObject,
    mut v_motive_647_: *mut leanh::LeanObject,
    mut v_____do__lift_648_: *mut leanh::LeanObject,
    mut v_h__1_649_: *mut leanh::LeanObject,
    mut v_h__2_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_648_) == 0 {
        let mut v_a_651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_650_);
        v_a_651_ = leanh::lean_ctor_get(v_____do__lift_648_, 0);
        leanh::lean_inc(v_a_651_);
        leanh::lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_652_ = leanh::lean_apply_1(v_h__1_649_, v_a_651_);
        return v___x_652_;
    } else {
        let mut v_a_653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_649_);
        v_a_653_ = leanh::lean_ctor_get(v_____do__lift_648_, 0);
        leanh::lean_inc(v_a_653_);
        leanh::lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_654_ = leanh::lean_apply_1(v_h__2_650_, v_a_653_);
        return v___x_654_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_655_: *mut leanh::LeanObject,
    mut v_h__1_656_: *mut leanh::LeanObject,
    mut v_h__2_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_655_) == 0 {
        let mut v_a_658_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_657_);
        v_a_658_ = leanh::lean_ctor_get(v_x_655_, 0);
        leanh::lean_inc(v_a_658_);
        leanh::lean_dec_ref_known(v_x_655_, 1);
        v___x_659_ = leanh::lean_apply_1(v_h__1_656_, v_a_658_);
        return v___x_659_;
    } else {
        let mut v_a_660_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_656_);
        v_a_660_ = leanh::lean_ctor_get(v_x_655_, 0);
        leanh::lean_inc(v_a_660_);
        leanh::lean_dec_ref_known(v_x_655_, 1);
        v___x_661_ = leanh::lean_apply_1(v_h__2_657_, v_a_660_);
        return v___x_661_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_662_: *mut leanh::LeanObject,
    mut v_motive_663_: *mut leanh::LeanObject,
    mut v_x_664_: *mut leanh::LeanObject,
    mut v_h__1_665_: *mut leanh::LeanObject,
    mut v_h__2_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_664_) == 0 {
        let mut v_a_667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_666_);
        v_a_667_ = leanh::lean_ctor_get(v_x_664_, 0);
        leanh::lean_inc(v_a_667_);
        leanh::lean_dec_ref_known(v_x_664_, 1);
        v___x_668_ = leanh::lean_apply_1(v_h__1_665_, v_a_667_);
        return v___x_668_;
    } else {
        let mut v_a_669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_665_);
        v_a_669_ = leanh::lean_ctor_get(v_x_664_, 0);
        leanh::lean_inc(v_a_669_);
        leanh::lean_dec_ref_known(v_x_664_, 1);
        v___x_670_ = leanh::lean_apply_1(v_h__2_666_, v_a_669_);
        return v___x_670_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_671_: *mut leanh::LeanObject,
    mut v_h__1_672_: *mut leanh::LeanObject,
    mut v_h__2_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_671_) == 0 {
        let mut v_a_674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_672_);
        v_a_674_ = leanh::lean_ctor_get(v_b_671_, 0);
        leanh::lean_inc(v_a_674_);
        leanh::lean_dec_ref_known(v_b_671_, 1);
        v___x_675_ = leanh::lean_apply_1(v_h__2_673_, v_a_674_);
        return v___x_675_;
    } else {
        let mut v_a_676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_673_);
        v_a_676_ = leanh::lean_ctor_get(v_b_671_, 0);
        leanh::lean_inc(v_a_676_);
        leanh::lean_dec_ref_known(v_b_671_, 1);
        v___x_677_ = leanh::lean_apply_1(v_h__1_672_, v_a_676_);
        return v___x_677_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_678_: *mut leanh::LeanObject,
    mut v_motive_679_: *mut leanh::LeanObject,
    mut v_b_680_: *mut leanh::LeanObject,
    mut v_h__1_681_: *mut leanh::LeanObject,
    mut v_h__2_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_680_) == 0 {
        let mut v_a_683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_681_);
        v_a_683_ = leanh::lean_ctor_get(v_b_680_, 0);
        leanh::lean_inc(v_a_683_);
        leanh::lean_dec_ref_known(v_b_680_, 1);
        v___x_684_ = leanh::lean_apply_1(v_h__2_682_, v_a_683_);
        return v___x_684_;
    } else {
        let mut v_a_685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_682_);
        v_a_685_ = leanh::lean_ctor_get(v_b_680_, 0);
        leanh::lean_inc(v_a_685_);
        leanh::lean_dec_ref_known(v_b_680_, 1);
        v___x_686_ = leanh::lean_apply_1(v_h__1_681_, v_a_685_);
        return v___x_686_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter___redArg(
    mut v_x_687_: *mut leanh::LeanObject,
    mut v_h__1_688_: *mut leanh::LeanObject,
    mut v_h__2_689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_687_) == 0 {
        let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_689_);
        v___x_690_ = leanh::lean_box(0);
        v___x_691_ = leanh::lean_apply_1(v_h__1_688_, v___x_690_);
        return v___x_691_;
    } else {
        let mut v_head_692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_688_);
        v_head_692_ = leanh::lean_ctor_get(v_x_687_, 0);
        leanh::lean_inc(v_head_692_);
        v_tail_693_ = leanh::lean_ctor_get(v_x_687_, 1);
        leanh::lean_inc(v_tail_693_);
        leanh::lean_dec_ref_known(v_x_687_, 2);
        v___x_694_ = leanh::lean_apply_2(v_h__2_689_, v_head_692_, v_tail_693_);
        return v___x_694_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_695_: *mut leanh::LeanObject,
    mut v_motive_696_: *mut leanh::LeanObject,
    mut v_x_697_: *mut leanh::LeanObject,
    mut v_h__1_698_: *mut leanh::LeanObject,
    mut v_h__2_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_697_) == 0 {
        let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_699_);
        v___x_700_ = leanh::lean_box(0);
        v___x_701_ = leanh::lean_apply_1(v_h__1_698_, v___x_700_);
        return v___x_701_;
    } else {
        let mut v_head_702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_698_);
        v_head_702_ = leanh::lean_ctor_get(v_x_697_, 0);
        leanh::lean_inc(v_head_702_);
        v_tail_703_ = leanh::lean_ctor_get(v_x_697_, 1);
        leanh::lean_inc(v_tail_703_);
        leanh::lean_dec_ref_known(v_x_697_, 2);
        v___x_704_ = leanh::lean_apply_2(v_h__2_699_, v_head_702_, v_tail_703_);
        return v___x_704_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_705_: u8,
    mut v_h__1_706_: *mut leanh::LeanObject,
    mut v_h__2_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_705_ == 0 {
        let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_706_);
        v___x_708_ = leanh::lean_box(0);
        v___x_709_ = leanh::lean_apply_1(v_h__2_707_, v___x_708_);
        return v___x_709_;
    } else {
        let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_707_);
        v___x_710_ = leanh::lean_box(0);
        v___x_711_ = leanh::lean_apply_1(v_h__1_706_, v___x_710_);
        return v___x_711_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_712_: *mut leanh::LeanObject,
    mut v_h__1_713_: *mut leanh::LeanObject,
    mut v_h__2_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_26__boxed_715_: u8 = 0;
    let mut v_res_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_715_ = (leanh::lean_unbox(v_____do__lift_712_) as u8);
    v_res_716_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_715_,
        v_h__1_713_,
        v_h__2_714_,
    );
    return v_res_716_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(
    mut v_motive_717_: *mut leanh::LeanObject,
    mut v_____do__lift_718_: u8,
    mut v_h__1_719_: *mut leanh::LeanObject,
    mut v_h__2_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_718_ == 0 {
        let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_719_);
        v___x_721_ = leanh::lean_box(0);
        v___x_722_ = leanh::lean_apply_1(v_h__2_720_, v___x_721_);
        return v___x_722_;
    } else {
        let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_720_);
        v___x_723_ = leanh::lean_box(0);
        v___x_724_ = leanh::lean_apply_1(v_h__1_719_, v___x_723_);
        return v___x_724_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_725_: *mut leanh::LeanObject,
    mut v_____do__lift_726_: *mut leanh::LeanObject,
    mut v_h__1_727_: *mut leanh::LeanObject,
    mut v_h__2_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_37__boxed_729_: u8 = 0;
    let mut v_res_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_729_ = (leanh::lean_unbox(v_____do__lift_726_) as u8);
    v_res_730_ = l___private_Init_Data_List_Monadic_0__List_anyM_match__1_splitter(
        v_motive_725_,
        v_____do__lift_37__boxed_729_,
        v_h__1_727_,
        v_h__2_728_,
    );
    return v_res_730_;
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter___redArg(
    mut v_____do__lift_731_: *mut leanh::LeanObject,
    mut v_h__1_732_: *mut leanh::LeanObject,
    mut v_h__2_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_731_) == 0 {
        let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_733_);
        v___x_734_ = leanh::lean_box(0);
        v___x_735_ = leanh::lean_apply_1(v_h__1_732_, v___x_734_);
        return v___x_735_;
    } else {
        let mut v_val_736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_732_);
        v_val_736_ = leanh::lean_ctor_get(v_____do__lift_731_, 0);
        leanh::lean_inc(v_val_736_);
        leanh::lean_dec_ref_known(v_____do__lift_731_, 1);
        v___x_737_ = leanh::lean_apply_1(v_h__2_733_, v_val_736_);
        return v___x_737_;
    }
}
pub unsafe fn l___private_Init_Data_List_Monadic_0__List_filterMapM__cons_match__1_splitter(
    mut v_00_u03b2_738_: *mut leanh::LeanObject,
    mut v_motive_739_: *mut leanh::LeanObject,
    mut v_____do__lift_740_: *mut leanh::LeanObject,
    mut v_h__1_741_: *mut leanh::LeanObject,
    mut v_h__2_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_740_) == 0 {
        let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_742_);
        v___x_743_ = leanh::lean_box(0);
        v___x_744_ = leanh::lean_apply_1(v_h__1_741_, v___x_743_);
        return v___x_744_;
    } else {
        let mut v_val_745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_741_);
        v_val_745_ = leanh::lean_ctor_get(v_____do__lift_740_, 0);
        leanh::lean_inc(v_val_745_);
        leanh::lean_dec_ref_known(v_____do__lift_740_, 1);
        v___x_746_ = leanh::lean_apply_1(v_h__2_742_, v_val_745_);
        return v___x_746_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Monadic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Monadic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Monadic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Monadic(builtin);
}