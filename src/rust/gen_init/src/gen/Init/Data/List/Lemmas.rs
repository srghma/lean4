// Lean compiler output
// Module: Init.Data.List.Lemmas
// Imports: Init.Data.List.BasicAux Init.Data.List.BasicAux Init.Data.List.Control Init.Data.List.Control Init.BinderPredicates Init.Grind.Annotated Init.Data.BEq Init.Data.Option.Instances Init.Data.Bool Init.Data.Option.Lemmas Init.TacticsExtra
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::BasicAux::{
    initialize_Init_Data_List_BasicAux, runtime_initialize_Init_Data_List_BasicAux,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::Option::Instances::{
    initialize_Init_Data_Option_Instances, runtime_initialize_Init_Data_Option_Instances,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Grind::Annotated::{
    initialize_Init_Grind_Annotated, runtime_initialize_Init_Grind_Annotated,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
pub unsafe fn l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_402_: *mut leanh::LeanObject,
    mut v_h__1_403_: *mut leanh::LeanObject,
    mut v_h__2_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_402_) == 0 {
        let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_403_);
        v___x_405_ = leanh::lean_box(0);
        v___x_406_ = leanh::lean_apply_1(v_h__2_404_, v___x_405_);
        return v___x_406_;
    } else {
        let mut v_val_407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_404_);
        v_val_407_ = leanh::lean_ctor_get(v_x_402_, 0);
        leanh::lean_inc(v_val_407_);
        leanh::lean_dec_ref_known(v_x_402_, 1);
        v___x_408_ = leanh::lean_apply_1(v_h__1_403_, v_val_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_409_: *mut leanh::LeanObject,
    mut v_motive_410_: *mut leanh::LeanObject,
    mut v_x_411_: *mut leanh::LeanObject,
    mut v_h__1_412_: *mut leanh::LeanObject,
    mut v_h__2_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_411_) == 0 {
        let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_412_);
        v___x_414_ = leanh::lean_box(0);
        v___x_415_ = leanh::lean_apply_1(v_h__2_413_, v___x_414_);
        return v___x_415_;
    } else {
        let mut v_val_416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_413_);
        v_val_416_ = leanh::lean_ctor_get(v_x_411_, 0);
        leanh::lean_inc(v_val_416_);
        leanh::lean_dec_ref_known(v_x_411_, 1);
        v___x_417_ = leanh::lean_apply_1(v_h__1_412_, v_val_416_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(
    mut v_x_418_: u8,
    mut v_h__1_419_: *mut leanh::LeanObject,
    mut v_h__2_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_418_ == 0 {
        let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_419_);
        v___x_421_ = leanh::lean_box(0);
        v___x_422_ = leanh::lean_apply_1(v_h__2_420_, v___x_421_);
        return v___x_422_;
    } else {
        let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_420_);
        v___x_423_ = leanh::lean_box(0);
        v___x_424_ = leanh::lean_apply_1(v_h__1_419_, v___x_423_);
        return v___x_424_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_425_: *mut leanh::LeanObject,
    mut v_h__1_426_: *mut leanh::LeanObject,
    mut v_h__2_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_428_: u8 = 0;
    let mut v_res_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_428_ = (leanh::lean_unbox(v_x_425_) as u8);
    v_res_429_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_428_,
        v_h__1_426_,
        v_h__2_427_,
    );
    return v_res_429_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(
    mut v_motive_430_: *mut leanh::LeanObject,
    mut v_x_431_: u8,
    mut v_h__1_432_: *mut leanh::LeanObject,
    mut v_h__2_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_431_ == 0 {
        let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_432_);
        v___x_434_ = leanh::lean_box(0);
        v___x_435_ = leanh::lean_apply_1(v_h__2_433_, v___x_434_);
        return v___x_435_;
    } else {
        let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_433_);
        v___x_436_ = leanh::lean_box(0);
        v___x_437_ = leanh::lean_apply_1(v_h__1_432_, v___x_436_);
        return v___x_437_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(
    mut v_motive_438_: *mut leanh::LeanObject,
    mut v_x_439_: *mut leanh::LeanObject,
    mut v_h__1_440_: *mut leanh::LeanObject,
    mut v_h__2_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_442_: u8 = 0;
    let mut v_res_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_442_ = (leanh::lean_unbox(v_x_439_) as u8);
    v_res_443_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(
        v_motive_438_,
        v_x_37__boxed_442_,
        v_h__1_440_,
        v_h__2_441_,
    );
    return v_res_443_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(
    mut v_x_444_: *mut leanh::LeanObject,
    mut v_x_445_: *mut leanh::LeanObject,
    mut v_x_446_: *mut leanh::LeanObject,
    mut v_h__1_447_: *mut leanh::LeanObject,
    mut v_h__2_448_: *mut leanh::LeanObject,
    mut v_h__3_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_444_) == 0 {
        leanh::lean_dec(v_h__2_448_);
        if leanh::lean_obj_tag(v_x_445_) == 0 {
            let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_449_);
            v___x_450_ = leanh::lean_apply_1(v_h__1_447_, v_x_446_);
            return v___x_450_;
        } else {
            let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_447_);
            v___x_451_ = leanh::lean_apply_5(
                v_h__3_449_,
                v_x_444_,
                v_x_445_,
                v_x_446_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_451_;
        }
    } else {
        leanh::lean_dec(v_h__1_447_);
        if leanh::lean_obj_tag(v_x_445_) == 1 {
            let mut v_head_452_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_453_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_454_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_455_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_449_);
            v_head_452_ = leanh::lean_ctor_get(v_x_444_, 0);
            leanh::lean_inc(v_head_452_);
            v_tail_453_ = leanh::lean_ctor_get(v_x_444_, 1);
            leanh::lean_inc(v_tail_453_);
            leanh::lean_dec_ref_known(v_x_444_, 2);
            v_head_454_ = leanh::lean_ctor_get(v_x_445_, 0);
            leanh::lean_inc(v_head_454_);
            v_tail_455_ = leanh::lean_ctor_get(v_x_445_, 1);
            leanh::lean_inc(v_tail_455_);
            leanh::lean_dec_ref_known(v_x_445_, 2);
            v___x_456_ = leanh::lean_apply_5(
                v_h__2_448_,
                v_head_452_,
                v_tail_453_,
                v_head_454_,
                v_tail_455_,
                v_x_446_,
            );
            return v___x_456_;
        } else {
            let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_448_);
            v___x_457_ = leanh::lean_apply_5(
                v_h__3_449_,
                v_x_444_,
                v_x_445_,
                v_x_446_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_457_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(
    mut v_00_u03b1_458_: *mut leanh::LeanObject,
    mut v_motive_459_: *mut leanh::LeanObject,
    mut v_x_460_: *mut leanh::LeanObject,
    mut v_x_461_: *mut leanh::LeanObject,
    mut v_x_462_: *mut leanh::LeanObject,
    mut v_h__1_463_: *mut leanh::LeanObject,
    mut v_h__2_464_: *mut leanh::LeanObject,
    mut v_h__3_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_460_) == 0 {
        leanh::lean_dec(v_h__2_464_);
        if leanh::lean_obj_tag(v_x_461_) == 0 {
            let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_465_);
            v___x_466_ = leanh::lean_apply_1(v_h__1_463_, v_x_462_);
            return v___x_466_;
        } else {
            let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_463_);
            v___x_467_ = leanh::lean_apply_5(
                v_h__3_465_,
                v_x_460_,
                v_x_461_,
                v_x_462_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_467_;
        }
    } else {
        leanh::lean_dec(v_h__1_463_);
        if leanh::lean_obj_tag(v_x_461_) == 1 {
            let mut v_head_468_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_469_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_470_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_471_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_465_);
            v_head_468_ = leanh::lean_ctor_get(v_x_460_, 0);
            leanh::lean_inc(v_head_468_);
            v_tail_469_ = leanh::lean_ctor_get(v_x_460_, 1);
            leanh::lean_inc(v_tail_469_);
            leanh::lean_dec_ref_known(v_x_460_, 2);
            v_head_470_ = leanh::lean_ctor_get(v_x_461_, 0);
            leanh::lean_inc(v_head_470_);
            v_tail_471_ = leanh::lean_ctor_get(v_x_461_, 1);
            leanh::lean_inc(v_tail_471_);
            leanh::lean_dec_ref_known(v_x_461_, 2);
            v___x_472_ = leanh::lean_apply_5(
                v_h__2_464_,
                v_head_468_,
                v_tail_469_,
                v_head_470_,
                v_tail_471_,
                v_x_462_,
            );
            return v___x_472_;
        } else {
            let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_464_);
            v___x_473_ = leanh::lean_apply_5(
                v_h__3_465_,
                v_x_460_,
                v_x_461_,
                v_x_462_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_473_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(
    mut v_x_474_: *mut leanh::LeanObject,
    mut v_h__1_475_: *mut leanh::LeanObject,
    mut v_h__2_476_: *mut leanh::LeanObject,
    mut v_h__3_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_474_) == 0 {
        let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_477_);
        leanh::lean_dec(v_h__2_476_);
        v___x_478_ = leanh::lean_apply_1(v_h__1_475_, leanh::lean_box(0));
        return v___x_478_;
    } else {
        let mut v_tail_479_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_475_);
        v_tail_479_ = leanh::lean_ctor_get(v_x_474_, 1);
        if leanh::lean_obj_tag(v_tail_479_) == 0 {
            let mut v_head_480_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_477_);
            v_head_480_ = leanh::lean_ctor_get(v_x_474_, 0);
            leanh::lean_inc(v_head_480_);
            leanh::lean_dec_ref_known(v_x_474_, 2);
            v___x_481_ =
                leanh::lean_apply_2(v_h__2_476_, v_head_480_, leanh::lean_box(0));
            return v___x_481_;
        } else {
            let mut v_head_482_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_483_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_484_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_479_);
            leanh::lean_dec(v_h__2_476_);
            v_head_482_ = leanh::lean_ctor_get(v_x_474_, 0);
            leanh::lean_inc(v_head_482_);
            leanh::lean_dec_ref_known(v_x_474_, 2);
            v_head_483_ = leanh::lean_ctor_get(v_tail_479_, 0);
            leanh::lean_inc(v_head_483_);
            v_tail_484_ = leanh::lean_ctor_get(v_tail_479_, 1);
            leanh::lean_inc(v_tail_484_);
            leanh::lean_dec_ref_known(v_tail_479_, 2);
            v___x_485_ = leanh::lean_apply_4(
                v_h__3_477_,
                v_head_482_,
                v_head_483_,
                v_tail_484_,
                leanh::lean_box(0),
            );
            return v___x_485_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(
    mut v_00_u03b1_486_: *mut leanh::LeanObject,
    mut v_motive_487_: *mut leanh::LeanObject,
    mut v_x_488_: *mut leanh::LeanObject,
    mut v_x_489_: *mut leanh::LeanObject,
    mut v_h__1_490_: *mut leanh::LeanObject,
    mut v_h__2_491_: *mut leanh::LeanObject,
    mut v_h__3_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_488_) == 0 {
        let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_492_);
        leanh::lean_dec(v_h__2_491_);
        v___x_493_ = leanh::lean_apply_1(v_h__1_490_, leanh::lean_box(0));
        return v___x_493_;
    } else {
        let mut v_tail_494_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_490_);
        v_tail_494_ = leanh::lean_ctor_get(v_x_488_, 1);
        if leanh::lean_obj_tag(v_tail_494_) == 0 {
            let mut v_head_495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_492_);
            v_head_495_ = leanh::lean_ctor_get(v_x_488_, 0);
            leanh::lean_inc(v_head_495_);
            leanh::lean_dec_ref_known(v_x_488_, 2);
            v___x_496_ =
                leanh::lean_apply_2(v_h__2_491_, v_head_495_, leanh::lean_box(0));
            return v___x_496_;
        } else {
            let mut v_head_497_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_498_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_499_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_494_);
            leanh::lean_dec(v_h__2_491_);
            v_head_497_ = leanh::lean_ctor_get(v_x_488_, 0);
            leanh::lean_inc(v_head_497_);
            leanh::lean_dec_ref_known(v_x_488_, 2);
            v_head_498_ = leanh::lean_ctor_get(v_tail_494_, 0);
            leanh::lean_inc(v_head_498_);
            v_tail_499_ = leanh::lean_ctor_get(v_tail_494_, 1);
            leanh::lean_inc(v_tail_499_);
            leanh::lean_dec_ref_known(v_tail_494_, 2);
            v___x_500_ = leanh::lean_apply_4(
                v_h__3_492_,
                v_head_497_,
                v_head_498_,
                v_tail_499_,
                leanh::lean_box(0),
            );
            return v___x_500_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(
    mut v_x_501_: *mut leanh::LeanObject,
    mut v_h__1_502_: *mut leanh::LeanObject,
    mut v_h__2_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_501_) == 0 {
        let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_503_);
        v___x_504_ = leanh::lean_box(0);
        v___x_505_ = leanh::lean_apply_1(v_h__1_502_, v___x_504_);
        return v___x_505_;
    } else {
        let mut v_head_506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_502_);
        v_head_506_ = leanh::lean_ctor_get(v_x_501_, 0);
        leanh::lean_inc(v_head_506_);
        v_tail_507_ = leanh::lean_ctor_get(v_x_501_, 1);
        leanh::lean_inc(v_tail_507_);
        leanh::lean_dec_ref_known(v_x_501_, 2);
        v___x_508_ = leanh::lean_apply_2(v_h__2_503_, v_head_506_, v_tail_507_);
        return v___x_508_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(
    mut v_00_u03b1_509_: *mut leanh::LeanObject,
    mut v_motive_510_: *mut leanh::LeanObject,
    mut v_x_511_: *mut leanh::LeanObject,
    mut v_h__1_512_: *mut leanh::LeanObject,
    mut v_h__2_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_511_) == 0 {
        let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_513_);
        v___x_514_ = leanh::lean_box(0);
        v___x_515_ = leanh::lean_apply_1(v_h__1_512_, v___x_514_);
        return v___x_515_;
    } else {
        let mut v_head_516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_512_);
        v_head_516_ = leanh::lean_ctor_get(v_x_511_, 0);
        leanh::lean_inc(v_head_516_);
        v_tail_517_ = leanh::lean_ctor_get(v_x_511_, 1);
        leanh::lean_inc(v_tail_517_);
        leanh::lean_dec_ref_known(v_x_511_, 2);
        v___x_518_ = leanh::lean_apply_2(v_h__2_513_, v_head_516_, v_tail_517_);
        return v___x_518_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_519_: *mut leanh::LeanObject,
    mut v_h__1_520_: *mut leanh::LeanObject,
    mut v_h__2_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_519_) == 0 {
        let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_521_);
        v___x_522_ = leanh::lean_box(0);
        v___x_523_ = leanh::lean_apply_1(v_h__1_520_, v___x_522_);
        return v___x_523_;
    } else {
        let mut v_head_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_520_);
        v_head_524_ = leanh::lean_ctor_get(v_x_519_, 0);
        leanh::lean_inc(v_head_524_);
        v_tail_525_ = leanh::lean_ctor_get(v_x_519_, 1);
        leanh::lean_inc(v_tail_525_);
        leanh::lean_dec_ref_known(v_x_519_, 2);
        v___x_526_ = leanh::lean_apply_2(v_h__2_521_, v_head_524_, v_tail_525_);
        return v___x_526_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_527_: *mut leanh::LeanObject,
    mut v_motive_528_: *mut leanh::LeanObject,
    mut v_x_529_: *mut leanh::LeanObject,
    mut v_h__1_530_: *mut leanh::LeanObject,
    mut v_h__2_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_529_) == 0 {
        let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_531_);
        v___x_532_ = leanh::lean_box(0);
        v___x_533_ = leanh::lean_apply_1(v_h__1_530_, v___x_532_);
        return v___x_533_;
    } else {
        let mut v_head_534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_530_);
        v_head_534_ = leanh::lean_ctor_get(v_x_529_, 0);
        leanh::lean_inc(v_head_534_);
        v_tail_535_ = leanh::lean_ctor_get(v_x_529_, 1);
        leanh::lean_inc(v_tail_535_);
        leanh::lean_dec_ref_known(v_x_529_, 2);
        v___x_536_ = leanh::lean_apply_2(v_h__2_531_, v_head_534_, v_tail_535_);
        return v___x_536_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(
    mut v_x_537_: *mut leanh::LeanObject,
    mut v_x_538_: *mut leanh::LeanObject,
    mut v_h__1_539_: *mut leanh::LeanObject,
    mut v_h__2_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_537_) == 0 {
        let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_540_);
        v___x_541_ = leanh::lean_apply_1(v_h__1_539_, v_x_538_);
        return v___x_541_;
    } else {
        let mut v_head_542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_539_);
        v_head_542_ = leanh::lean_ctor_get(v_x_537_, 0);
        leanh::lean_inc(v_head_542_);
        v_tail_543_ = leanh::lean_ctor_get(v_x_537_, 1);
        leanh::lean_inc(v_tail_543_);
        leanh::lean_dec_ref_known(v_x_537_, 2);
        v___x_544_ = leanh::lean_apply_3(v_h__2_540_, v_head_542_, v_tail_543_, v_x_538_);
        return v___x_544_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(
    mut v_00_u03b1_545_: *mut leanh::LeanObject,
    mut v_motive_546_: *mut leanh::LeanObject,
    mut v_x_547_: *mut leanh::LeanObject,
    mut v_x_548_: *mut leanh::LeanObject,
    mut v_h__1_549_: *mut leanh::LeanObject,
    mut v_h__2_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_547_) == 0 {
        let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_550_);
        v___x_551_ = leanh::lean_apply_1(v_h__1_549_, v_x_548_);
        return v___x_551_;
    } else {
        let mut v_head_552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_549_);
        v_head_552_ = leanh::lean_ctor_get(v_x_547_, 0);
        leanh::lean_inc(v_head_552_);
        v_tail_553_ = leanh::lean_ctor_get(v_x_547_, 1);
        leanh::lean_inc(v_tail_553_);
        leanh::lean_dec_ref_known(v_x_547_, 2);
        v___x_554_ = leanh::lean_apply_3(v_h__2_550_, v_head_552_, v_tail_553_, v_x_548_);
        return v___x_554_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_555_: *mut leanh::LeanObject,
    mut v_h__1_556_: *mut leanh::LeanObject,
    mut v_h__2_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_555_) == 0 {
        let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_557_);
        v___x_558_ = leanh::lean_box(0);
        v___x_559_ = leanh::lean_apply_1(v_h__1_556_, v___x_558_);
        return v___x_559_;
    } else {
        let mut v_val_560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_556_);
        v_val_560_ = leanh::lean_ctor_get(v_x_555_, 0);
        leanh::lean_inc(v_val_560_);
        leanh::lean_dec_ref_known(v_x_555_, 1);
        v___x_561_ = leanh::lean_apply_1(v_h__2_557_, v_val_560_);
        return v___x_561_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_562_: *mut leanh::LeanObject,
    mut v_motive_563_: *mut leanh::LeanObject,
    mut v_x_564_: *mut leanh::LeanObject,
    mut v_h__1_565_: *mut leanh::LeanObject,
    mut v_h__2_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_564_) == 0 {
        let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_566_);
        v___x_567_ = leanh::lean_box(0);
        v___x_568_ = leanh::lean_apply_1(v_h__1_565_, v___x_567_);
        return v___x_568_;
    } else {
        let mut v_val_569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_565_);
        v_val_569_ = leanh::lean_ctor_get(v_x_564_, 0);
        leanh::lean_inc(v_val_569_);
        leanh::lean_dec_ref_known(v_x_564_, 1);
        v___x_570_ = leanh::lean_apply_1(v_h__2_566_, v_val_569_);
        return v___x_570_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(
    mut v_x_571_: *mut leanh::LeanObject,
    mut v_h__1_572_: *mut leanh::LeanObject,
    mut v_h__2_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_571_) == 0 {
        let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_573_);
        v___x_574_ = leanh::lean_box(0);
        v___x_575_ = leanh::lean_apply_1(v_h__1_572_, v___x_574_);
        return v___x_575_;
    } else {
        let mut v_head_576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_572_);
        v_head_576_ = leanh::lean_ctor_get(v_x_571_, 0);
        leanh::lean_inc(v_head_576_);
        v_tail_577_ = leanh::lean_ctor_get(v_x_571_, 1);
        leanh::lean_inc(v_tail_577_);
        leanh::lean_dec_ref_known(v_x_571_, 2);
        v___x_578_ = leanh::lean_apply_2(v_h__2_573_, v_head_576_, v_tail_577_);
        return v___x_578_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(
    mut v_00_u03b1_579_: *mut leanh::LeanObject,
    mut v_motive_580_: *mut leanh::LeanObject,
    mut v_x_581_: *mut leanh::LeanObject,
    mut v_h__1_582_: *mut leanh::LeanObject,
    mut v_h__2_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_581_) == 0 {
        let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_583_);
        v___x_584_ = leanh::lean_box(0);
        v___x_585_ = leanh::lean_apply_1(v_h__1_582_, v___x_584_);
        return v___x_585_;
    } else {
        let mut v_head_586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_582_);
        v_head_586_ = leanh::lean_ctor_get(v_x_581_, 0);
        leanh::lean_inc(v_head_586_);
        v_tail_587_ = leanh::lean_ctor_get(v_x_581_, 1);
        leanh::lean_inc(v_tail_587_);
        leanh::lean_dec_ref_known(v_x_581_, 2);
        v___x_588_ = leanh::lean_apply_2(v_h__2_583_, v_head_586_, v_tail_587_);
        return v___x_588_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_589_: *mut leanh::LeanObject,
    mut v_h__1_590_: *mut leanh::LeanObject,
    mut v_h__2_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_589_) == 0 {
        let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_590_);
        v___x_592_ = leanh::lean_box(0);
        v___x_593_ = leanh::lean_apply_1(v_h__2_591_, v___x_592_);
        return v___x_593_;
    } else {
        let mut v_val_594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_591_);
        v_val_594_ = leanh::lean_ctor_get(v_x_589_, 0);
        leanh::lean_inc(v_val_594_);
        leanh::lean_dec_ref_known(v_x_589_, 1);
        v___x_595_ = leanh::lean_apply_1(v_h__1_590_, v_val_594_);
        return v___x_595_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_596_: *mut leanh::LeanObject,
    mut v_motive_597_: *mut leanh::LeanObject,
    mut v_x_598_: *mut leanh::LeanObject,
    mut v_h__1_599_: *mut leanh::LeanObject,
    mut v_h__2_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_598_) == 0 {
        let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_599_);
        v___x_601_ = leanh::lean_box(0);
        v___x_602_ = leanh::lean_apply_1(v_h__2_600_, v___x_601_);
        return v___x_602_;
    } else {
        let mut v_val_603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_600_);
        v_val_603_ = leanh::lean_ctor_get(v_x_598_, 0);
        leanh::lean_inc(v_val_603_);
        leanh::lean_dec_ref_known(v_x_598_, 1);
        v___x_604_ = leanh::lean_apply_1(v_h__1_599_, v_val_603_);
        return v___x_604_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(
    mut v_x_605_: *mut leanh::LeanObject,
    mut v_h__1_606_: *mut leanh::LeanObject,
    mut v_h__2_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_605_) == 0 {
        let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_607_);
        v___x_608_ = leanh::lean_box(0);
        v___x_609_ = leanh::lean_apply_1(v_h__1_606_, v___x_608_);
        return v___x_609_;
    } else {
        let mut v_val_610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_606_);
        v_val_610_ = leanh::lean_ctor_get(v_x_605_, 0);
        leanh::lean_inc(v_val_610_);
        leanh::lean_dec_ref_known(v_x_605_, 1);
        v___x_611_ = leanh::lean_apply_1(v_h__2_607_, v_val_610_);
        return v___x_611_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(
    mut v_00_u03b2_612_: *mut leanh::LeanObject,
    mut v_motive_613_: *mut leanh::LeanObject,
    mut v_x_614_: *mut leanh::LeanObject,
    mut v_h__1_615_: *mut leanh::LeanObject,
    mut v_h__2_616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_614_) == 0 {
        let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_616_);
        v___x_617_ = leanh::lean_box(0);
        v___x_618_ = leanh::lean_apply_1(v_h__1_615_, v___x_617_);
        return v___x_618_;
    } else {
        let mut v_val_619_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_615_);
        v_val_619_ = leanh::lean_ctor_get(v_x_614_, 0);
        leanh::lean_inc(v_val_619_);
        leanh::lean_dec_ref_known(v_x_614_, 1);
        v___x_620_ = leanh::lean_apply_1(v_h__2_616_, v_val_619_);
        return v___x_620_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(
    mut v_x_621_: *mut leanh::LeanObject,
    mut v_h__1_622_: *mut leanh::LeanObject,
    mut v_h__2_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_621_) == 0 {
        let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_622_);
        v___x_624_ = leanh::lean_box(0);
        v___x_625_ = leanh::lean_apply_1(v_h__2_623_, v___x_624_);
        return v___x_625_;
    } else {
        let mut v_val_626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_623_);
        v_val_626_ = leanh::lean_ctor_get(v_x_621_, 0);
        leanh::lean_inc(v_val_626_);
        leanh::lean_dec_ref_known(v_x_621_, 1);
        v___x_627_ = leanh::lean_apply_1(v_h__1_622_, v_val_626_);
        return v___x_627_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(
    mut v_00_u03b2_628_: *mut leanh::LeanObject,
    mut v_motive_629_: *mut leanh::LeanObject,
    mut v_x_630_: *mut leanh::LeanObject,
    mut v_h__1_631_: *mut leanh::LeanObject,
    mut v_h__2_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_630_) == 0 {
        let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_631_);
        v___x_633_ = leanh::lean_box(0);
        v___x_634_ = leanh::lean_apply_1(v_h__2_632_, v___x_633_);
        return v___x_634_;
    } else {
        let mut v_val_635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_632_);
        v_val_635_ = leanh::lean_ctor_get(v_x_630_, 0);
        leanh::lean_inc(v_val_635_);
        leanh::lean_dec_ref_known(v_x_630_, 1);
        v___x_636_ = leanh::lean_apply_1(v_h__1_631_, v_val_635_);
        return v___x_636_;
    }
}
pub unsafe fn l_List_foldlRecOn___redArg___lam__0(
    mut v_x_637_: *mut leanh::LeanObject,
    mut v_y_638_: *mut leanh::LeanObject,
    mut v_hy_639_: *mut leanh::LeanObject,
    mut v_x_640_: *mut leanh::LeanObject,
    mut v_hx_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = leanh::lean_apply_4(
        v_x_637_,
        v_y_638_,
        v_hy_639_,
        v_x_640_,
        leanh::lean_box(0),
    );
    return v___x_642_;
}
pub unsafe fn l_List_foldlRecOn___redArg(
    mut v_x_643_: *mut leanh::LeanObject,
    mut v_x_644_: *mut leanh::LeanObject,
    mut v_x_645_: *mut leanh::LeanObject,
    mut v_x_646_: *mut leanh::LeanObject,
    mut v_x_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_643_) == 0 {
                    leanh::lean_dec(v_x_647_);
                    leanh::lean_dec(v_x_645_);
                    leanh::lean_dec(v_x_644_);
                    return v_x_646_;
                } else {
                    v_head_648_ = leanh::lean_ctor_get(v_x_643_, 0);
                    leanh::lean_inc_n(v_head_648_, 2);
                    v_tail_649_ = leanh::lean_ctor_get(v_x_643_, 1);
                    leanh::lean_inc(v_tail_649_);
                    leanh::lean_dec_ref_known(v_x_643_, 2);
                    leanh::lean_inc(v_x_647_);
                    v___f_650_ = leanh::lean_alloc_closure(
                        l_List_foldlRecOn___redArg___lam__0 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    leanh::lean_closure_set(v___f_650_, 0, v_x_647_);
                    leanh::lean_inc(v_x_644_);
                    leanh::lean_inc(v_x_645_);
                    v___x_651_ = leanh::lean_apply_2(v_x_644_, v_x_645_, v_head_648_);
                    v___x_652_ = leanh::lean_apply_4(
                        v_x_647_,
                        v_x_645_,
                        v_x_646_,
                        v_head_648_,
                        leanh::lean_box(0),
                    );
                    v_x_643_ = v_tail_649_;
                    v_x_645_ = v___x_651_;
                    v_x_646_ = v___x_652_;
                    v_x_647_ = v___f_650_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlRecOn(
    mut v_00_u03b2_654_: *mut leanh::LeanObject,
    mut v_00_u03b1_655_: *mut leanh::LeanObject,
    mut v_motive_656_: *mut leanh::LeanObject,
    mut v_x_657_: *mut leanh::LeanObject,
    mut v_x_658_: *mut leanh::LeanObject,
    mut v_x_659_: *mut leanh::LeanObject,
    mut v_x_660_: *mut leanh::LeanObject,
    mut v_x_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_List_foldlRecOn___redArg(v_x_657_, v_x_658_, v_x_659_, v_x_660_, v_x_661_);
    return v___x_662_;
}
pub unsafe fn l_List_foldrRecOn___redArg___lam__0(
    mut v_x_663_: *mut leanh::LeanObject,
    mut v_b_664_: *mut leanh::LeanObject,
    mut v_c_665_: *mut leanh::LeanObject,
    mut v_a_666_: *mut leanh::LeanObject,
    mut v_m_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = leanh::lean_apply_4(
        v_x_663_,
        v_b_664_,
        v_c_665_,
        v_a_666_,
        leanh::lean_box(0),
    );
    return v___x_668_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(
    mut v_x_669_: *mut leanh::LeanObject,
    mut v_init_670_: *mut leanh::LeanObject,
    mut v_x_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_671_) == 0 {
        leanh::lean_dec(v_x_669_);
        leanh::lean_inc(v_init_670_);
        return v_init_670_;
    } else {
        let mut v_head_672_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_673_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_672_ = leanh::lean_ctor_get(v_x_671_, 0);
        leanh::lean_inc(v_head_672_);
        v_tail_673_ = leanh::lean_ctor_get(v_x_671_, 1);
        leanh::lean_inc(v_tail_673_);
        leanh::lean_dec_ref_known(v_x_671_, 2);
        leanh::lean_inc(v_x_669_);
        v___x_674_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(
            v_x_669_,
            v_init_670_,
            v_tail_673_,
        );
        v___x_675_ = leanh::lean_apply_2(v_x_669_, v_head_672_, v___x_674_);
        return v___x_675_;
    }
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(
    mut v_x_676_: *mut leanh::LeanObject,
    mut v_init_677_: *mut leanh::LeanObject,
    mut v_x_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ =
        l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_676_, v_init_677_, v_x_678_);
    leanh::lean_dec(v_init_677_);
    return v_res_679_;
}
pub unsafe fn l_List_foldrRecOn___redArg(
    mut v_x_680_: *mut leanh::LeanObject,
    mut v_x_681_: *mut leanh::LeanObject,
    mut v_x_682_: *mut leanh::LeanObject,
    mut v_x_683_: *mut leanh::LeanObject,
    mut v_x_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_680_) == 0 {
        leanh::lean_dec(v_x_684_);
        leanh::lean_dec(v_x_681_);
        leanh::lean_inc(v_x_683_);
        return v_x_683_;
    } else {
        let mut v_head_685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_686_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_685_ = leanh::lean_ctor_get(v_x_680_, 0);
        leanh::lean_inc(v_head_685_);
        v_tail_686_ = leanh::lean_ctor_get(v_x_680_, 1);
        leanh::lean_inc_n(v_tail_686_, 2);
        leanh::lean_dec_ref_known(v_x_680_, 2);
        leanh::lean_inc(v_x_684_);
        v___f_687_ = leanh::lean_alloc_closure(
            l_List_foldrRecOn___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            1,
        );
        leanh::lean_closure_set(v___f_687_, 0, v_x_684_);
        leanh::lean_inc(v_x_681_);
        v___x_688_ =
            l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_681_, v_x_682_, v_tail_686_);
        v___x_689_ =
            l_List_foldrRecOn___redArg(v_tail_686_, v_x_681_, v_x_682_, v_x_683_, v___f_687_);
        v___x_690_ = leanh::lean_apply_4(
            v_x_684_,
            v___x_688_,
            v___x_689_,
            v_head_685_,
            leanh::lean_box(0),
        );
        return v___x_690_;
    }
}
pub unsafe fn l_List_foldrRecOn___redArg___boxed(
    mut v_x_691_: *mut leanh::LeanObject,
    mut v_x_692_: *mut leanh::LeanObject,
    mut v_x_693_: *mut leanh::LeanObject,
    mut v_x_694_: *mut leanh::LeanObject,
    mut v_x_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_List_foldrRecOn___redArg(v_x_691_, v_x_692_, v_x_693_, v_x_694_, v_x_695_);
    leanh::lean_dec(v_x_694_);
    leanh::lean_dec(v_x_693_);
    return v_res_696_;
}
pub unsafe fn l_List_foldrRecOn(
    mut v_00_u03b2_697_: *mut leanh::LeanObject,
    mut v_00_u03b1_698_: *mut leanh::LeanObject,
    mut v_motive_699_: *mut leanh::LeanObject,
    mut v_x_700_: *mut leanh::LeanObject,
    mut v_x_701_: *mut leanh::LeanObject,
    mut v_x_702_: *mut leanh::LeanObject,
    mut v_x_703_: *mut leanh::LeanObject,
    mut v_x_704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_705_ = l_List_foldrRecOn___redArg(v_x_700_, v_x_701_, v_x_702_, v_x_703_, v_x_704_);
    return v___x_705_;
}
pub unsafe fn l_List_foldrRecOn___boxed(
    mut v_00_u03b2_706_: *mut leanh::LeanObject,
    mut v_00_u03b1_707_: *mut leanh::LeanObject,
    mut v_motive_708_: *mut leanh::LeanObject,
    mut v_x_709_: *mut leanh::LeanObject,
    mut v_x_710_: *mut leanh::LeanObject,
    mut v_x_711_: *mut leanh::LeanObject,
    mut v_x_712_: *mut leanh::LeanObject,
    mut v_x_713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_List_foldrRecOn(
        v_00_u03b2_706_,
        v_00_u03b1_707_,
        v_motive_708_,
        v_x_709_,
        v_x_710_,
        v_x_711_,
        v_x_712_,
        v_x_713_,
    );
    leanh::lean_dec(v_x_712_);
    leanh::lean_dec(v_x_711_);
    return v_res_714_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0(
    mut v_00_u03b1_715_: *mut leanh::LeanObject,
    mut v_00_u03b2_716_: *mut leanh::LeanObject,
    mut v_x_717_: *mut leanh::LeanObject,
    mut v_init_718_: *mut leanh::LeanObject,
    mut v_x_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ =
        l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_717_, v_init_718_, v_x_719_);
    return v___x_720_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(
    mut v_00_u03b1_721_: *mut leanh::LeanObject,
    mut v_00_u03b2_722_: *mut leanh::LeanObject,
    mut v_x_723_: *mut leanh::LeanObject,
    mut v_init_724_: *mut leanh::LeanObject,
    mut v_x_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_List_foldr___at___00List_foldrRecOn_spec__0(
        v_00_u03b1_721_,
        v_00_u03b2_722_,
        v_x_723_,
        v_init_724_,
        v_x_725_,
    );
    leanh::lean_dec(v_init_724_);
    return v_res_726_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(
    mut v_x_727_: *mut leanh::LeanObject,
    mut v_x_728_: *mut leanh::LeanObject,
    mut v_h__1_729_: *mut leanh::LeanObject,
    mut v_h__2_730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_727_) == 0 {
        let mut v_fst_731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_730_);
        v_fst_731_ = leanh::lean_ctor_get(v_x_728_, 0);
        leanh::lean_inc(v_fst_731_);
        v_snd_732_ = leanh::lean_ctor_get(v_x_728_, 1);
        leanh::lean_inc(v_snd_732_);
        leanh::lean_dec_ref(v_x_728_);
        v___x_733_ = leanh::lean_apply_2(v_h__1_729_, v_fst_731_, v_snd_732_);
        return v___x_733_;
    } else {
        let mut v_head_734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_729_);
        v_head_734_ = leanh::lean_ctor_get(v_x_727_, 0);
        leanh::lean_inc(v_head_734_);
        v_tail_735_ = leanh::lean_ctor_get(v_x_727_, 1);
        leanh::lean_inc(v_tail_735_);
        leanh::lean_dec_ref_known(v_x_727_, 2);
        v_fst_736_ = leanh::lean_ctor_get(v_x_728_, 0);
        leanh::lean_inc(v_fst_736_);
        v_snd_737_ = leanh::lean_ctor_get(v_x_728_, 1);
        leanh::lean_inc(v_snd_737_);
        leanh::lean_dec_ref(v_x_728_);
        v___x_738_ = leanh::lean_apply_4(
            v_h__2_730_,
            v_head_734_,
            v_tail_735_,
            v_fst_736_,
            v_snd_737_,
        );
        return v___x_738_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter(
    mut v_00_u03b1_739_: *mut leanh::LeanObject,
    mut v_motive_740_: *mut leanh::LeanObject,
    mut v_x_741_: *mut leanh::LeanObject,
    mut v_x_742_: *mut leanh::LeanObject,
    mut v_h__1_743_: *mut leanh::LeanObject,
    mut v_h__2_744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_741_) == 0 {
        let mut v_fst_745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_744_);
        v_fst_745_ = leanh::lean_ctor_get(v_x_742_, 0);
        leanh::lean_inc(v_fst_745_);
        v_snd_746_ = leanh::lean_ctor_get(v_x_742_, 1);
        leanh::lean_inc(v_snd_746_);
        leanh::lean_dec_ref(v_x_742_);
        v___x_747_ = leanh::lean_apply_2(v_h__1_743_, v_fst_745_, v_snd_746_);
        return v___x_747_;
    } else {
        let mut v_head_748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_743_);
        v_head_748_ = leanh::lean_ctor_get(v_x_741_, 0);
        leanh::lean_inc(v_head_748_);
        v_tail_749_ = leanh::lean_ctor_get(v_x_741_, 1);
        leanh::lean_inc(v_tail_749_);
        leanh::lean_dec_ref_known(v_x_741_, 2);
        v_fst_750_ = leanh::lean_ctor_get(v_x_742_, 0);
        leanh::lean_inc(v_fst_750_);
        v_snd_751_ = leanh::lean_ctor_get(v_x_742_, 1);
        leanh::lean_inc(v_snd_751_);
        leanh::lean_dec_ref(v_x_742_);
        v___x_752_ = leanh::lean_apply_4(
            v_h__2_744_,
            v_head_748_,
            v_tail_749_,
            v_fst_750_,
            v_snd_751_,
        );
        return v___x_752_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter___redArg(
    mut v_x_753_: *mut leanh::LeanObject,
    mut v_x_754_: *mut leanh::LeanObject,
    mut v_x_755_: *mut leanh::LeanObject,
    mut v_h__1_756_: *mut leanh::LeanObject,
    mut v_h__2_757_: *mut leanh::LeanObject,
    mut v_h__3_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_753_) == 0 {
        let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_758_);
        leanh::lean_dec(v_h__2_757_);
        v___x_759_ = leanh::lean_apply_2(v_h__1_756_, v_x_754_, v_x_755_);
        return v___x_759_;
    } else {
        let mut v_head_760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_763_: u8 = 0;
        leanh::lean_dec(v_h__1_756_);
        v_head_760_ = leanh::lean_ctor_get(v_x_753_, 0);
        v_tail_761_ = leanh::lean_ctor_get(v_x_753_, 1);
        v_zero_762_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_763_ = lean_nat_dec_eq(v_x_754_, v_zero_762_);
        if v_isZero_763_ == 0 {
            let mut v_one_764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_765_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_761_);
            leanh::lean_inc(v_head_760_);
            leanh::lean_dec_ref_known(v_x_753_, 2);
            leanh::lean_dec(v_h__3_758_);
            v_one_764_ = leanh::lean_unsigned_to_nat(1);
            v_n_765_ = lean_nat_sub(v_x_754_, v_one_764_);
            leanh::lean_dec(v_x_754_);
            v___x_766_ = leanh::lean_apply_4(
                v_h__2_757_,
                v_head_760_,
                v_tail_761_,
                v_n_765_,
                v_x_755_,
            );
            return v___x_766_;
        } else {
            let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_757_);
            v___x_767_ = leanh::lean_apply_5(
                v_h__3_758_,
                v_x_753_,
                v_x_754_,
                v_x_755_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_767_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(
    mut v_00_u03b1_768_: *mut leanh::LeanObject,
    mut v_motive_769_: *mut leanh::LeanObject,
    mut v_x_770_: *mut leanh::LeanObject,
    mut v_x_771_: *mut leanh::LeanObject,
    mut v_x_772_: *mut leanh::LeanObject,
    mut v_h__1_773_: *mut leanh::LeanObject,
    mut v_h__2_774_: *mut leanh::LeanObject,
    mut v_h__3_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_770_) == 0 {
        let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_775_);
        leanh::lean_dec(v_h__2_774_);
        v___x_776_ = leanh::lean_apply_2(v_h__1_773_, v_x_771_, v_x_772_);
        return v___x_776_;
    } else {
        let mut v_head_777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_778_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_779_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_780_: u8 = 0;
        leanh::lean_dec(v_h__1_773_);
        v_head_777_ = leanh::lean_ctor_get(v_x_770_, 0);
        v_tail_778_ = leanh::lean_ctor_get(v_x_770_, 1);
        v_zero_779_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_780_ = lean_nat_dec_eq(v_x_771_, v_zero_779_);
        if v_isZero_780_ == 0 {
            let mut v_one_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_782_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_778_);
            leanh::lean_inc(v_head_777_);
            leanh::lean_dec_ref_known(v_x_770_, 2);
            leanh::lean_dec(v_h__3_775_);
            v_one_781_ = leanh::lean_unsigned_to_nat(1);
            v_n_782_ = lean_nat_sub(v_x_771_, v_one_781_);
            leanh::lean_dec(v_x_771_);
            v___x_783_ = leanh::lean_apply_4(
                v_h__2_774_,
                v_head_777_,
                v_tail_778_,
                v_n_782_,
                v_x_772_,
            );
            return v___x_783_;
        } else {
            let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_774_);
            v___x_784_ = leanh::lean_apply_5(
                v_h__3_775_,
                v_x_770_,
                v_x_771_,
                v_x_772_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_784_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_785_: *mut leanh::LeanObject,
    mut v_x_786_: *mut leanh::LeanObject,
    mut v_h__1_787_: *mut leanh::LeanObject,
    mut v_h__2_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_785_) == 0 {
        let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_788_);
        v___x_789_ = leanh::lean_apply_1(v_h__1_787_, v_x_786_);
        return v___x_789_;
    } else {
        let mut v_head_790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_787_);
        v_head_790_ = leanh::lean_ctor_get(v_x_785_, 0);
        leanh::lean_inc(v_head_790_);
        v_tail_791_ = leanh::lean_ctor_get(v_x_785_, 1);
        leanh::lean_inc(v_tail_791_);
        leanh::lean_dec_ref_known(v_x_785_, 2);
        v___x_792_ = leanh::lean_apply_3(v_h__2_788_, v_head_790_, v_tail_791_, v_x_786_);
        return v___x_792_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_793_: *mut leanh::LeanObject,
    mut v_motive_794_: *mut leanh::LeanObject,
    mut v_x_795_: *mut leanh::LeanObject,
    mut v_x_796_: *mut leanh::LeanObject,
    mut v_h__1_797_: *mut leanh::LeanObject,
    mut v_h__2_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_795_) == 0 {
        let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_798_);
        v___x_799_ = leanh::lean_apply_1(v_h__1_797_, v_x_796_);
        return v___x_799_;
    } else {
        let mut v_head_800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_797_);
        v_head_800_ = leanh::lean_ctor_get(v_x_795_, 0);
        leanh::lean_inc(v_head_800_);
        v_tail_801_ = leanh::lean_ctor_get(v_x_795_, 1);
        leanh::lean_inc(v_tail_801_);
        leanh::lean_dec_ref_known(v_x_795_, 2);
        v___x_802_ = leanh::lean_apply_3(v_h__2_798_, v_head_800_, v_tail_801_, v_x_796_);
        return v___x_802_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Annotated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Annotated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Lemmas(builtin);
}