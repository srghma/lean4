// Lean compiler output
// Module: Init.Data.List.Lemmas
// Imports: Init.Data.List.BasicAux Init.Data.List.BasicAux Init.Data.List.Control Init.Data.List.Control Init.BinderPredicates Init.Grind.Annotated Init.Data.BEq Init.Data.Option.Instances Init.Data.Bool Init.Data.Option.Lemmas Init.TacticsExtra
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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_402_: *mut crate::leanh::LeanObject,
    mut v_h__1_403_: *mut crate::leanh::LeanObject,
    mut v_h__2_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_402_) == 0 {
        let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_403_);
        v___x_405_ = crate::leanh::lean_box(0);
        v___x_406_ = crate::leanh::lean_apply_1(v_h__2_404_, v___x_405_);
        return v___x_406_;
    } else {
        let mut v_val_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_404_);
        v_val_407_ = crate::leanh::lean_ctor_get(v_x_402_, 0);
        crate::leanh::lean_inc(v_val_407_);
        crate::leanh::lean_dec_ref_known(v_x_402_, 1);
        v___x_408_ = crate::leanh::lean_apply_1(v_h__1_403_, v_val_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_409_: *mut crate::leanh::LeanObject,
    mut v_motive_410_: *mut crate::leanh::LeanObject,
    mut v_x_411_: *mut crate::leanh::LeanObject,
    mut v_h__1_412_: *mut crate::leanh::LeanObject,
    mut v_h__2_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_411_) == 0 {
        let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_412_);
        v___x_414_ = crate::leanh::lean_box(0);
        v___x_415_ = crate::leanh::lean_apply_1(v_h__2_413_, v___x_414_);
        return v___x_415_;
    } else {
        let mut v_val_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_413_);
        v_val_416_ = crate::leanh::lean_ctor_get(v_x_411_, 0);
        crate::leanh::lean_inc(v_val_416_);
        crate::leanh::lean_dec_ref_known(v_x_411_, 1);
        v___x_417_ = crate::leanh::lean_apply_1(v_h__1_412_, v_val_416_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(
    mut v_x_418_: u8,
    mut v_h__1_419_: *mut crate::leanh::LeanObject,
    mut v_h__2_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_418_ == 0 {
        let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_419_);
        v___x_421_ = crate::leanh::lean_box(0);
        v___x_422_ = crate::leanh::lean_apply_1(v_h__2_420_, v___x_421_);
        return v___x_422_;
    } else {
        let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_420_);
        v___x_423_ = crate::leanh::lean_box(0);
        v___x_424_ = crate::leanh::lean_apply_1(v_h__1_419_, v___x_423_);
        return v___x_424_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_425_: *mut crate::leanh::LeanObject,
    mut v_h__1_426_: *mut crate::leanh::LeanObject,
    mut v_h__2_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_428_: u8 = 0;
    let mut v_res_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_428_ = (crate::leanh::lean_unbox(v_x_425_) as u8);
    v_res_429_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_428_,
        v_h__1_426_,
        v_h__2_427_,
    );
    return v_res_429_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(
    mut v_motive_430_: *mut crate::leanh::LeanObject,
    mut v_x_431_: u8,
    mut v_h__1_432_: *mut crate::leanh::LeanObject,
    mut v_h__2_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_431_ == 0 {
        let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_432_);
        v___x_434_ = crate::leanh::lean_box(0);
        v___x_435_ = crate::leanh::lean_apply_1(v_h__2_433_, v___x_434_);
        return v___x_435_;
    } else {
        let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_433_);
        v___x_436_ = crate::leanh::lean_box(0);
        v___x_437_ = crate::leanh::lean_apply_1(v_h__1_432_, v___x_436_);
        return v___x_437_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(
    mut v_motive_438_: *mut crate::leanh::LeanObject,
    mut v_x_439_: *mut crate::leanh::LeanObject,
    mut v_h__1_440_: *mut crate::leanh::LeanObject,
    mut v_h__2_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_442_: u8 = 0;
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_442_ = (crate::leanh::lean_unbox(v_x_439_) as u8);
    v_res_443_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(
        v_motive_438_,
        v_x_37__boxed_442_,
        v_h__1_440_,
        v_h__2_441_,
    );
    return v_res_443_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(
    mut v_x_444_: *mut crate::leanh::LeanObject,
    mut v_x_445_: *mut crate::leanh::LeanObject,
    mut v_x_446_: *mut crate::leanh::LeanObject,
    mut v_h__1_447_: *mut crate::leanh::LeanObject,
    mut v_h__2_448_: *mut crate::leanh::LeanObject,
    mut v_h__3_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_444_) == 0 {
        crate::leanh::lean_dec(v_h__2_448_);
        if crate::leanh::lean_obj_tag(v_x_445_) == 0 {
            let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_449_);
            v___x_450_ = crate::leanh::lean_apply_1(v_h__1_447_, v_x_446_);
            return v___x_450_;
        } else {
            let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_447_);
            v___x_451_ = crate::leanh::lean_apply_5(
                v_h__3_449_,
                v_x_444_,
                v_x_445_,
                v_x_446_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_451_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_447_);
        if crate::leanh::lean_obj_tag(v_x_445_) == 1 {
            let mut v_head_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_449_);
            v_head_452_ = crate::leanh::lean_ctor_get(v_x_444_, 0);
            crate::leanh::lean_inc(v_head_452_);
            v_tail_453_ = crate::leanh::lean_ctor_get(v_x_444_, 1);
            crate::leanh::lean_inc(v_tail_453_);
            crate::leanh::lean_dec_ref_known(v_x_444_, 2);
            v_head_454_ = crate::leanh::lean_ctor_get(v_x_445_, 0);
            crate::leanh::lean_inc(v_head_454_);
            v_tail_455_ = crate::leanh::lean_ctor_get(v_x_445_, 1);
            crate::leanh::lean_inc(v_tail_455_);
            crate::leanh::lean_dec_ref_known(v_x_445_, 2);
            v___x_456_ = crate::leanh::lean_apply_5(
                v_h__2_448_,
                v_head_452_,
                v_tail_453_,
                v_head_454_,
                v_tail_455_,
                v_x_446_,
            );
            return v___x_456_;
        } else {
            let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_448_);
            v___x_457_ = crate::leanh::lean_apply_5(
                v_h__3_449_,
                v_x_444_,
                v_x_445_,
                v_x_446_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_457_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(
    mut v_00_u03b1_458_: *mut crate::leanh::LeanObject,
    mut v_motive_459_: *mut crate::leanh::LeanObject,
    mut v_x_460_: *mut crate::leanh::LeanObject,
    mut v_x_461_: *mut crate::leanh::LeanObject,
    mut v_x_462_: *mut crate::leanh::LeanObject,
    mut v_h__1_463_: *mut crate::leanh::LeanObject,
    mut v_h__2_464_: *mut crate::leanh::LeanObject,
    mut v_h__3_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_460_) == 0 {
        crate::leanh::lean_dec(v_h__2_464_);
        if crate::leanh::lean_obj_tag(v_x_461_) == 0 {
            let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_465_);
            v___x_466_ = crate::leanh::lean_apply_1(v_h__1_463_, v_x_462_);
            return v___x_466_;
        } else {
            let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_463_);
            v___x_467_ = crate::leanh::lean_apply_5(
                v_h__3_465_,
                v_x_460_,
                v_x_461_,
                v_x_462_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_467_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_463_);
        if crate::leanh::lean_obj_tag(v_x_461_) == 1 {
            let mut v_head_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_465_);
            v_head_468_ = crate::leanh::lean_ctor_get(v_x_460_, 0);
            crate::leanh::lean_inc(v_head_468_);
            v_tail_469_ = crate::leanh::lean_ctor_get(v_x_460_, 1);
            crate::leanh::lean_inc(v_tail_469_);
            crate::leanh::lean_dec_ref_known(v_x_460_, 2);
            v_head_470_ = crate::leanh::lean_ctor_get(v_x_461_, 0);
            crate::leanh::lean_inc(v_head_470_);
            v_tail_471_ = crate::leanh::lean_ctor_get(v_x_461_, 1);
            crate::leanh::lean_inc(v_tail_471_);
            crate::leanh::lean_dec_ref_known(v_x_461_, 2);
            v___x_472_ = crate::leanh::lean_apply_5(
                v_h__2_464_,
                v_head_468_,
                v_tail_469_,
                v_head_470_,
                v_tail_471_,
                v_x_462_,
            );
            return v___x_472_;
        } else {
            let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_464_);
            v___x_473_ = crate::leanh::lean_apply_5(
                v_h__3_465_,
                v_x_460_,
                v_x_461_,
                v_x_462_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_473_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(
    mut v_x_474_: *mut crate::leanh::LeanObject,
    mut v_h__1_475_: *mut crate::leanh::LeanObject,
    mut v_h__2_476_: *mut crate::leanh::LeanObject,
    mut v_h__3_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_474_) == 0 {
        let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_477_);
        crate::leanh::lean_dec(v_h__2_476_);
        v___x_478_ = crate::leanh::lean_apply_1(v_h__1_475_, crate::leanh::lean_box(0));
        return v___x_478_;
    } else {
        let mut v_tail_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_475_);
        v_tail_479_ = crate::leanh::lean_ctor_get(v_x_474_, 1);
        if crate::leanh::lean_obj_tag(v_tail_479_) == 0 {
            let mut v_head_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_477_);
            v_head_480_ = crate::leanh::lean_ctor_get(v_x_474_, 0);
            crate::leanh::lean_inc(v_head_480_);
            crate::leanh::lean_dec_ref_known(v_x_474_, 2);
            v___x_481_ =
                crate::leanh::lean_apply_2(v_h__2_476_, v_head_480_, crate::leanh::lean_box(0));
            return v___x_481_;
        } else {
            let mut v_head_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_479_);
            crate::leanh::lean_dec(v_h__2_476_);
            v_head_482_ = crate::leanh::lean_ctor_get(v_x_474_, 0);
            crate::leanh::lean_inc(v_head_482_);
            crate::leanh::lean_dec_ref_known(v_x_474_, 2);
            v_head_483_ = crate::leanh::lean_ctor_get(v_tail_479_, 0);
            crate::leanh::lean_inc(v_head_483_);
            v_tail_484_ = crate::leanh::lean_ctor_get(v_tail_479_, 1);
            crate::leanh::lean_inc(v_tail_484_);
            crate::leanh::lean_dec_ref_known(v_tail_479_, 2);
            v___x_485_ = crate::leanh::lean_apply_4(
                v_h__3_477_,
                v_head_482_,
                v_head_483_,
                v_tail_484_,
                crate::leanh::lean_box(0),
            );
            return v___x_485_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(
    mut v_00_u03b1_486_: *mut crate::leanh::LeanObject,
    mut v_motive_487_: *mut crate::leanh::LeanObject,
    mut v_x_488_: *mut crate::leanh::LeanObject,
    mut v_x_489_: *mut crate::leanh::LeanObject,
    mut v_h__1_490_: *mut crate::leanh::LeanObject,
    mut v_h__2_491_: *mut crate::leanh::LeanObject,
    mut v_h__3_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_488_) == 0 {
        let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_492_);
        crate::leanh::lean_dec(v_h__2_491_);
        v___x_493_ = crate::leanh::lean_apply_1(v_h__1_490_, crate::leanh::lean_box(0));
        return v___x_493_;
    } else {
        let mut v_tail_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_490_);
        v_tail_494_ = crate::leanh::lean_ctor_get(v_x_488_, 1);
        if crate::leanh::lean_obj_tag(v_tail_494_) == 0 {
            let mut v_head_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_492_);
            v_head_495_ = crate::leanh::lean_ctor_get(v_x_488_, 0);
            crate::leanh::lean_inc(v_head_495_);
            crate::leanh::lean_dec_ref_known(v_x_488_, 2);
            v___x_496_ =
                crate::leanh::lean_apply_2(v_h__2_491_, v_head_495_, crate::leanh::lean_box(0));
            return v___x_496_;
        } else {
            let mut v_head_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_494_);
            crate::leanh::lean_dec(v_h__2_491_);
            v_head_497_ = crate::leanh::lean_ctor_get(v_x_488_, 0);
            crate::leanh::lean_inc(v_head_497_);
            crate::leanh::lean_dec_ref_known(v_x_488_, 2);
            v_head_498_ = crate::leanh::lean_ctor_get(v_tail_494_, 0);
            crate::leanh::lean_inc(v_head_498_);
            v_tail_499_ = crate::leanh::lean_ctor_get(v_tail_494_, 1);
            crate::leanh::lean_inc(v_tail_499_);
            crate::leanh::lean_dec_ref_known(v_tail_494_, 2);
            v___x_500_ = crate::leanh::lean_apply_4(
                v_h__3_492_,
                v_head_497_,
                v_head_498_,
                v_tail_499_,
                crate::leanh::lean_box(0),
            );
            return v___x_500_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(
    mut v_x_501_: *mut crate::leanh::LeanObject,
    mut v_h__1_502_: *mut crate::leanh::LeanObject,
    mut v_h__2_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_501_) == 0 {
        let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_503_);
        v___x_504_ = crate::leanh::lean_box(0);
        v___x_505_ = crate::leanh::lean_apply_1(v_h__1_502_, v___x_504_);
        return v___x_505_;
    } else {
        let mut v_head_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_502_);
        v_head_506_ = crate::leanh::lean_ctor_get(v_x_501_, 0);
        crate::leanh::lean_inc(v_head_506_);
        v_tail_507_ = crate::leanh::lean_ctor_get(v_x_501_, 1);
        crate::leanh::lean_inc(v_tail_507_);
        crate::leanh::lean_dec_ref_known(v_x_501_, 2);
        v___x_508_ = crate::leanh::lean_apply_2(v_h__2_503_, v_head_506_, v_tail_507_);
        return v___x_508_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(
    mut v_00_u03b1_509_: *mut crate::leanh::LeanObject,
    mut v_motive_510_: *mut crate::leanh::LeanObject,
    mut v_x_511_: *mut crate::leanh::LeanObject,
    mut v_h__1_512_: *mut crate::leanh::LeanObject,
    mut v_h__2_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_511_) == 0 {
        let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_513_);
        v___x_514_ = crate::leanh::lean_box(0);
        v___x_515_ = crate::leanh::lean_apply_1(v_h__1_512_, v___x_514_);
        return v___x_515_;
    } else {
        let mut v_head_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_512_);
        v_head_516_ = crate::leanh::lean_ctor_get(v_x_511_, 0);
        crate::leanh::lean_inc(v_head_516_);
        v_tail_517_ = crate::leanh::lean_ctor_get(v_x_511_, 1);
        crate::leanh::lean_inc(v_tail_517_);
        crate::leanh::lean_dec_ref_known(v_x_511_, 2);
        v___x_518_ = crate::leanh::lean_apply_2(v_h__2_513_, v_head_516_, v_tail_517_);
        return v___x_518_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_519_: *mut crate::leanh::LeanObject,
    mut v_h__1_520_: *mut crate::leanh::LeanObject,
    mut v_h__2_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_519_) == 0 {
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_521_);
        v___x_522_ = crate::leanh::lean_box(0);
        v___x_523_ = crate::leanh::lean_apply_1(v_h__1_520_, v___x_522_);
        return v___x_523_;
    } else {
        let mut v_head_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_520_);
        v_head_524_ = crate::leanh::lean_ctor_get(v_x_519_, 0);
        crate::leanh::lean_inc(v_head_524_);
        v_tail_525_ = crate::leanh::lean_ctor_get(v_x_519_, 1);
        crate::leanh::lean_inc(v_tail_525_);
        crate::leanh::lean_dec_ref_known(v_x_519_, 2);
        v___x_526_ = crate::leanh::lean_apply_2(v_h__2_521_, v_head_524_, v_tail_525_);
        return v___x_526_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_527_: *mut crate::leanh::LeanObject,
    mut v_motive_528_: *mut crate::leanh::LeanObject,
    mut v_x_529_: *mut crate::leanh::LeanObject,
    mut v_h__1_530_: *mut crate::leanh::LeanObject,
    mut v_h__2_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_529_) == 0 {
        let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_531_);
        v___x_532_ = crate::leanh::lean_box(0);
        v___x_533_ = crate::leanh::lean_apply_1(v_h__1_530_, v___x_532_);
        return v___x_533_;
    } else {
        let mut v_head_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_530_);
        v_head_534_ = crate::leanh::lean_ctor_get(v_x_529_, 0);
        crate::leanh::lean_inc(v_head_534_);
        v_tail_535_ = crate::leanh::lean_ctor_get(v_x_529_, 1);
        crate::leanh::lean_inc(v_tail_535_);
        crate::leanh::lean_dec_ref_known(v_x_529_, 2);
        v___x_536_ = crate::leanh::lean_apply_2(v_h__2_531_, v_head_534_, v_tail_535_);
        return v___x_536_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(
    mut v_x_537_: *mut crate::leanh::LeanObject,
    mut v_x_538_: *mut crate::leanh::LeanObject,
    mut v_h__1_539_: *mut crate::leanh::LeanObject,
    mut v_h__2_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_537_) == 0 {
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_540_);
        v___x_541_ = crate::leanh::lean_apply_1(v_h__1_539_, v_x_538_);
        return v___x_541_;
    } else {
        let mut v_head_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_539_);
        v_head_542_ = crate::leanh::lean_ctor_get(v_x_537_, 0);
        crate::leanh::lean_inc(v_head_542_);
        v_tail_543_ = crate::leanh::lean_ctor_get(v_x_537_, 1);
        crate::leanh::lean_inc(v_tail_543_);
        crate::leanh::lean_dec_ref_known(v_x_537_, 2);
        v___x_544_ = crate::leanh::lean_apply_3(v_h__2_540_, v_head_542_, v_tail_543_, v_x_538_);
        return v___x_544_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(
    mut v_00_u03b1_545_: *mut crate::leanh::LeanObject,
    mut v_motive_546_: *mut crate::leanh::LeanObject,
    mut v_x_547_: *mut crate::leanh::LeanObject,
    mut v_x_548_: *mut crate::leanh::LeanObject,
    mut v_h__1_549_: *mut crate::leanh::LeanObject,
    mut v_h__2_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_547_) == 0 {
        let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_550_);
        v___x_551_ = crate::leanh::lean_apply_1(v_h__1_549_, v_x_548_);
        return v___x_551_;
    } else {
        let mut v_head_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_549_);
        v_head_552_ = crate::leanh::lean_ctor_get(v_x_547_, 0);
        crate::leanh::lean_inc(v_head_552_);
        v_tail_553_ = crate::leanh::lean_ctor_get(v_x_547_, 1);
        crate::leanh::lean_inc(v_tail_553_);
        crate::leanh::lean_dec_ref_known(v_x_547_, 2);
        v___x_554_ = crate::leanh::lean_apply_3(v_h__2_550_, v_head_552_, v_tail_553_, v_x_548_);
        return v___x_554_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_555_: *mut crate::leanh::LeanObject,
    mut v_h__1_556_: *mut crate::leanh::LeanObject,
    mut v_h__2_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_555_) == 0 {
        let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_557_);
        v___x_558_ = crate::leanh::lean_box(0);
        v___x_559_ = crate::leanh::lean_apply_1(v_h__1_556_, v___x_558_);
        return v___x_559_;
    } else {
        let mut v_val_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_556_);
        v_val_560_ = crate::leanh::lean_ctor_get(v_x_555_, 0);
        crate::leanh::lean_inc(v_val_560_);
        crate::leanh::lean_dec_ref_known(v_x_555_, 1);
        v___x_561_ = crate::leanh::lean_apply_1(v_h__2_557_, v_val_560_);
        return v___x_561_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_562_: *mut crate::leanh::LeanObject,
    mut v_motive_563_: *mut crate::leanh::LeanObject,
    mut v_x_564_: *mut crate::leanh::LeanObject,
    mut v_h__1_565_: *mut crate::leanh::LeanObject,
    mut v_h__2_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_564_) == 0 {
        let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_566_);
        v___x_567_ = crate::leanh::lean_box(0);
        v___x_568_ = crate::leanh::lean_apply_1(v_h__1_565_, v___x_567_);
        return v___x_568_;
    } else {
        let mut v_val_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_565_);
        v_val_569_ = crate::leanh::lean_ctor_get(v_x_564_, 0);
        crate::leanh::lean_inc(v_val_569_);
        crate::leanh::lean_dec_ref_known(v_x_564_, 1);
        v___x_570_ = crate::leanh::lean_apply_1(v_h__2_566_, v_val_569_);
        return v___x_570_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(
    mut v_x_571_: *mut crate::leanh::LeanObject,
    mut v_h__1_572_: *mut crate::leanh::LeanObject,
    mut v_h__2_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_571_) == 0 {
        let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_573_);
        v___x_574_ = crate::leanh::lean_box(0);
        v___x_575_ = crate::leanh::lean_apply_1(v_h__1_572_, v___x_574_);
        return v___x_575_;
    } else {
        let mut v_head_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_572_);
        v_head_576_ = crate::leanh::lean_ctor_get(v_x_571_, 0);
        crate::leanh::lean_inc(v_head_576_);
        v_tail_577_ = crate::leanh::lean_ctor_get(v_x_571_, 1);
        crate::leanh::lean_inc(v_tail_577_);
        crate::leanh::lean_dec_ref_known(v_x_571_, 2);
        v___x_578_ = crate::leanh::lean_apply_2(v_h__2_573_, v_head_576_, v_tail_577_);
        return v___x_578_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(
    mut v_00_u03b1_579_: *mut crate::leanh::LeanObject,
    mut v_motive_580_: *mut crate::leanh::LeanObject,
    mut v_x_581_: *mut crate::leanh::LeanObject,
    mut v_h__1_582_: *mut crate::leanh::LeanObject,
    mut v_h__2_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_581_) == 0 {
        let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_583_);
        v___x_584_ = crate::leanh::lean_box(0);
        v___x_585_ = crate::leanh::lean_apply_1(v_h__1_582_, v___x_584_);
        return v___x_585_;
    } else {
        let mut v_head_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_582_);
        v_head_586_ = crate::leanh::lean_ctor_get(v_x_581_, 0);
        crate::leanh::lean_inc(v_head_586_);
        v_tail_587_ = crate::leanh::lean_ctor_get(v_x_581_, 1);
        crate::leanh::lean_inc(v_tail_587_);
        crate::leanh::lean_dec_ref_known(v_x_581_, 2);
        v___x_588_ = crate::leanh::lean_apply_2(v_h__2_583_, v_head_586_, v_tail_587_);
        return v___x_588_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_589_: *mut crate::leanh::LeanObject,
    mut v_h__1_590_: *mut crate::leanh::LeanObject,
    mut v_h__2_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_589_) == 0 {
        let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_590_);
        v___x_592_ = crate::leanh::lean_box(0);
        v___x_593_ = crate::leanh::lean_apply_1(v_h__2_591_, v___x_592_);
        return v___x_593_;
    } else {
        let mut v_val_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_591_);
        v_val_594_ = crate::leanh::lean_ctor_get(v_x_589_, 0);
        crate::leanh::lean_inc(v_val_594_);
        crate::leanh::lean_dec_ref_known(v_x_589_, 1);
        v___x_595_ = crate::leanh::lean_apply_1(v_h__1_590_, v_val_594_);
        return v___x_595_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_596_: *mut crate::leanh::LeanObject,
    mut v_motive_597_: *mut crate::leanh::LeanObject,
    mut v_x_598_: *mut crate::leanh::LeanObject,
    mut v_h__1_599_: *mut crate::leanh::LeanObject,
    mut v_h__2_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_598_) == 0 {
        let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_599_);
        v___x_601_ = crate::leanh::lean_box(0);
        v___x_602_ = crate::leanh::lean_apply_1(v_h__2_600_, v___x_601_);
        return v___x_602_;
    } else {
        let mut v_val_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_600_);
        v_val_603_ = crate::leanh::lean_ctor_get(v_x_598_, 0);
        crate::leanh::lean_inc(v_val_603_);
        crate::leanh::lean_dec_ref_known(v_x_598_, 1);
        v___x_604_ = crate::leanh::lean_apply_1(v_h__1_599_, v_val_603_);
        return v___x_604_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(
    mut v_x_605_: *mut crate::leanh::LeanObject,
    mut v_h__1_606_: *mut crate::leanh::LeanObject,
    mut v_h__2_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_605_) == 0 {
        let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_607_);
        v___x_608_ = crate::leanh::lean_box(0);
        v___x_609_ = crate::leanh::lean_apply_1(v_h__1_606_, v___x_608_);
        return v___x_609_;
    } else {
        let mut v_val_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_606_);
        v_val_610_ = crate::leanh::lean_ctor_get(v_x_605_, 0);
        crate::leanh::lean_inc(v_val_610_);
        crate::leanh::lean_dec_ref_known(v_x_605_, 1);
        v___x_611_ = crate::leanh::lean_apply_1(v_h__2_607_, v_val_610_);
        return v___x_611_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(
    mut v_00_u03b2_612_: *mut crate::leanh::LeanObject,
    mut v_motive_613_: *mut crate::leanh::LeanObject,
    mut v_x_614_: *mut crate::leanh::LeanObject,
    mut v_h__1_615_: *mut crate::leanh::LeanObject,
    mut v_h__2_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_614_) == 0 {
        let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_616_);
        v___x_617_ = crate::leanh::lean_box(0);
        v___x_618_ = crate::leanh::lean_apply_1(v_h__1_615_, v___x_617_);
        return v___x_618_;
    } else {
        let mut v_val_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_615_);
        v_val_619_ = crate::leanh::lean_ctor_get(v_x_614_, 0);
        crate::leanh::lean_inc(v_val_619_);
        crate::leanh::lean_dec_ref_known(v_x_614_, 1);
        v___x_620_ = crate::leanh::lean_apply_1(v_h__2_616_, v_val_619_);
        return v___x_620_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(
    mut v_x_621_: *mut crate::leanh::LeanObject,
    mut v_h__1_622_: *mut crate::leanh::LeanObject,
    mut v_h__2_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_621_) == 0 {
        let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_622_);
        v___x_624_ = crate::leanh::lean_box(0);
        v___x_625_ = crate::leanh::lean_apply_1(v_h__2_623_, v___x_624_);
        return v___x_625_;
    } else {
        let mut v_val_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_623_);
        v_val_626_ = crate::leanh::lean_ctor_get(v_x_621_, 0);
        crate::leanh::lean_inc(v_val_626_);
        crate::leanh::lean_dec_ref_known(v_x_621_, 1);
        v___x_627_ = crate::leanh::lean_apply_1(v_h__1_622_, v_val_626_);
        return v___x_627_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(
    mut v_00_u03b2_628_: *mut crate::leanh::LeanObject,
    mut v_motive_629_: *mut crate::leanh::LeanObject,
    mut v_x_630_: *mut crate::leanh::LeanObject,
    mut v_h__1_631_: *mut crate::leanh::LeanObject,
    mut v_h__2_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_630_) == 0 {
        let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_631_);
        v___x_633_ = crate::leanh::lean_box(0);
        v___x_634_ = crate::leanh::lean_apply_1(v_h__2_632_, v___x_633_);
        return v___x_634_;
    } else {
        let mut v_val_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_632_);
        v_val_635_ = crate::leanh::lean_ctor_get(v_x_630_, 0);
        crate::leanh::lean_inc(v_val_635_);
        crate::leanh::lean_dec_ref_known(v_x_630_, 1);
        v___x_636_ = crate::leanh::lean_apply_1(v_h__1_631_, v_val_635_);
        return v___x_636_;
    }
}
pub unsafe fn l_List_foldlRecOn___redArg___lam__0(
    mut v_x_637_: *mut crate::leanh::LeanObject,
    mut v_y_638_: *mut crate::leanh::LeanObject,
    mut v_hy_639_: *mut crate::leanh::LeanObject,
    mut v_x_640_: *mut crate::leanh::LeanObject,
    mut v_hx_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = crate::leanh::lean_apply_4(
        v_x_637_,
        v_y_638_,
        v_hy_639_,
        v_x_640_,
        crate::leanh::lean_box(0),
    );
    return v___x_642_;
}
pub unsafe fn l_List_foldlRecOn___redArg(
    mut v_x_643_: *mut crate::leanh::LeanObject,
    mut v_x_644_: *mut crate::leanh::LeanObject,
    mut v_x_645_: *mut crate::leanh::LeanObject,
    mut v_x_646_: *mut crate::leanh::LeanObject,
    mut v_x_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_643_) == 0 {
                    crate::leanh::lean_dec(v_x_647_);
                    crate::leanh::lean_dec(v_x_645_);
                    crate::leanh::lean_dec(v_x_644_);
                    return v_x_646_;
                } else {
                    v_head_648_ = crate::leanh::lean_ctor_get(v_x_643_, 0);
                    crate::leanh::lean_inc_n(v_head_648_, 2);
                    v_tail_649_ = crate::leanh::lean_ctor_get(v_x_643_, 1);
                    crate::leanh::lean_inc(v_tail_649_);
                    crate::leanh::lean_dec_ref_known(v_x_643_, 2);
                    crate::leanh::lean_inc(v_x_647_);
                    v___f_650_ = crate::leanh::lean_alloc_closure(
                        l_List_foldlRecOn___redArg___lam__0 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_650_, 0, v_x_647_);
                    crate::leanh::lean_inc(v_x_644_);
                    crate::leanh::lean_inc(v_x_645_);
                    v___x_651_ = crate::leanh::lean_apply_2(v_x_644_, v_x_645_, v_head_648_);
                    v___x_652_ = crate::leanh::lean_apply_4(
                        v_x_647_,
                        v_x_645_,
                        v_x_646_,
                        v_head_648_,
                        crate::leanh::lean_box(0),
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
    mut v_00_u03b2_654_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_655_: *mut crate::leanh::LeanObject,
    mut v_motive_656_: *mut crate::leanh::LeanObject,
    mut v_x_657_: *mut crate::leanh::LeanObject,
    mut v_x_658_: *mut crate::leanh::LeanObject,
    mut v_x_659_: *mut crate::leanh::LeanObject,
    mut v_x_660_: *mut crate::leanh::LeanObject,
    mut v_x_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_List_foldlRecOn___redArg(v_x_657_, v_x_658_, v_x_659_, v_x_660_, v_x_661_);
    return v___x_662_;
}
pub unsafe fn l_List_foldrRecOn___redArg___lam__0(
    mut v_x_663_: *mut crate::leanh::LeanObject,
    mut v_b_664_: *mut crate::leanh::LeanObject,
    mut v_c_665_: *mut crate::leanh::LeanObject,
    mut v_a_666_: *mut crate::leanh::LeanObject,
    mut v_m_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = crate::leanh::lean_apply_4(
        v_x_663_,
        v_b_664_,
        v_c_665_,
        v_a_666_,
        crate::leanh::lean_box(0),
    );
    return v___x_668_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(
    mut v_x_669_: *mut crate::leanh::LeanObject,
    mut v_init_670_: *mut crate::leanh::LeanObject,
    mut v_x_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_671_) == 0 {
        crate::leanh::lean_dec(v_x_669_);
        crate::leanh::lean_inc(v_init_670_);
        return v_init_670_;
    } else {
        let mut v_head_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_672_ = crate::leanh::lean_ctor_get(v_x_671_, 0);
        crate::leanh::lean_inc(v_head_672_);
        v_tail_673_ = crate::leanh::lean_ctor_get(v_x_671_, 1);
        crate::leanh::lean_inc(v_tail_673_);
        crate::leanh::lean_dec_ref_known(v_x_671_, 2);
        crate::leanh::lean_inc(v_x_669_);
        v___x_674_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(
            v_x_669_,
            v_init_670_,
            v_tail_673_,
        );
        v___x_675_ = crate::leanh::lean_apply_2(v_x_669_, v_head_672_, v___x_674_);
        return v___x_675_;
    }
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(
    mut v_x_676_: *mut crate::leanh::LeanObject,
    mut v_init_677_: *mut crate::leanh::LeanObject,
    mut v_x_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ =
        l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_676_, v_init_677_, v_x_678_);
    crate::leanh::lean_dec(v_init_677_);
    return v_res_679_;
}
pub unsafe fn l_List_foldrRecOn___redArg(
    mut v_x_680_: *mut crate::leanh::LeanObject,
    mut v_x_681_: *mut crate::leanh::LeanObject,
    mut v_x_682_: *mut crate::leanh::LeanObject,
    mut v_x_683_: *mut crate::leanh::LeanObject,
    mut v_x_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_680_) == 0 {
        crate::leanh::lean_dec(v_x_684_);
        crate::leanh::lean_dec(v_x_681_);
        crate::leanh::lean_inc(v_x_683_);
        return v_x_683_;
    } else {
        let mut v_head_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_685_ = crate::leanh::lean_ctor_get(v_x_680_, 0);
        crate::leanh::lean_inc(v_head_685_);
        v_tail_686_ = crate::leanh::lean_ctor_get(v_x_680_, 1);
        crate::leanh::lean_inc_n(v_tail_686_, 2);
        crate::leanh::lean_dec_ref_known(v_x_680_, 2);
        crate::leanh::lean_inc(v_x_684_);
        v___f_687_ = crate::leanh::lean_alloc_closure(
            l_List_foldrRecOn___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            1,
        );
        crate::leanh::lean_closure_set(v___f_687_, 0, v_x_684_);
        crate::leanh::lean_inc(v_x_681_);
        v___x_688_ =
            l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_681_, v_x_682_, v_tail_686_);
        v___x_689_ =
            l_List_foldrRecOn___redArg(v_tail_686_, v_x_681_, v_x_682_, v_x_683_, v___f_687_);
        v___x_690_ = crate::leanh::lean_apply_4(
            v_x_684_,
            v___x_688_,
            v___x_689_,
            v_head_685_,
            crate::leanh::lean_box(0),
        );
        return v___x_690_;
    }
}
pub unsafe fn l_List_foldrRecOn___redArg___boxed(
    mut v_x_691_: *mut crate::leanh::LeanObject,
    mut v_x_692_: *mut crate::leanh::LeanObject,
    mut v_x_693_: *mut crate::leanh::LeanObject,
    mut v_x_694_: *mut crate::leanh::LeanObject,
    mut v_x_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_List_foldrRecOn___redArg(v_x_691_, v_x_692_, v_x_693_, v_x_694_, v_x_695_);
    crate::leanh::lean_dec(v_x_694_);
    crate::leanh::lean_dec(v_x_693_);
    return v_res_696_;
}
pub unsafe fn l_List_foldrRecOn(
    mut v_00_u03b2_697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_698_: *mut crate::leanh::LeanObject,
    mut v_motive_699_: *mut crate::leanh::LeanObject,
    mut v_x_700_: *mut crate::leanh::LeanObject,
    mut v_x_701_: *mut crate::leanh::LeanObject,
    mut v_x_702_: *mut crate::leanh::LeanObject,
    mut v_x_703_: *mut crate::leanh::LeanObject,
    mut v_x_704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_705_ = l_List_foldrRecOn___redArg(v_x_700_, v_x_701_, v_x_702_, v_x_703_, v_x_704_);
    return v___x_705_;
}
pub unsafe fn l_List_foldrRecOn___boxed(
    mut v_00_u03b2_706_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_707_: *mut crate::leanh::LeanObject,
    mut v_motive_708_: *mut crate::leanh::LeanObject,
    mut v_x_709_: *mut crate::leanh::LeanObject,
    mut v_x_710_: *mut crate::leanh::LeanObject,
    mut v_x_711_: *mut crate::leanh::LeanObject,
    mut v_x_712_: *mut crate::leanh::LeanObject,
    mut v_x_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_x_712_);
    crate::leanh::lean_dec(v_x_711_);
    return v_res_714_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0(
    mut v_00_u03b1_715_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_716_: *mut crate::leanh::LeanObject,
    mut v_x_717_: *mut crate::leanh::LeanObject,
    mut v_init_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ =
        l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_717_, v_init_718_, v_x_719_);
    return v___x_720_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(
    mut v_00_u03b1_721_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_722_: *mut crate::leanh::LeanObject,
    mut v_x_723_: *mut crate::leanh::LeanObject,
    mut v_init_724_: *mut crate::leanh::LeanObject,
    mut v_x_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_List_foldr___at___00List_foldrRecOn_spec__0(
        v_00_u03b1_721_,
        v_00_u03b2_722_,
        v_x_723_,
        v_init_724_,
        v_x_725_,
    );
    crate::leanh::lean_dec(v_init_724_);
    return v_res_726_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(
    mut v_x_727_: *mut crate::leanh::LeanObject,
    mut v_x_728_: *mut crate::leanh::LeanObject,
    mut v_h__1_729_: *mut crate::leanh::LeanObject,
    mut v_h__2_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_727_) == 0 {
        let mut v_fst_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_730_);
        v_fst_731_ = crate::leanh::lean_ctor_get(v_x_728_, 0);
        crate::leanh::lean_inc(v_fst_731_);
        v_snd_732_ = crate::leanh::lean_ctor_get(v_x_728_, 1);
        crate::leanh::lean_inc(v_snd_732_);
        crate::leanh::lean_dec_ref(v_x_728_);
        v___x_733_ = crate::leanh::lean_apply_2(v_h__1_729_, v_fst_731_, v_snd_732_);
        return v___x_733_;
    } else {
        let mut v_head_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_729_);
        v_head_734_ = crate::leanh::lean_ctor_get(v_x_727_, 0);
        crate::leanh::lean_inc(v_head_734_);
        v_tail_735_ = crate::leanh::lean_ctor_get(v_x_727_, 1);
        crate::leanh::lean_inc(v_tail_735_);
        crate::leanh::lean_dec_ref_known(v_x_727_, 2);
        v_fst_736_ = crate::leanh::lean_ctor_get(v_x_728_, 0);
        crate::leanh::lean_inc(v_fst_736_);
        v_snd_737_ = crate::leanh::lean_ctor_get(v_x_728_, 1);
        crate::leanh::lean_inc(v_snd_737_);
        crate::leanh::lean_dec_ref(v_x_728_);
        v___x_738_ = crate::leanh::lean_apply_4(
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
    mut v_00_u03b1_739_: *mut crate::leanh::LeanObject,
    mut v_motive_740_: *mut crate::leanh::LeanObject,
    mut v_x_741_: *mut crate::leanh::LeanObject,
    mut v_x_742_: *mut crate::leanh::LeanObject,
    mut v_h__1_743_: *mut crate::leanh::LeanObject,
    mut v_h__2_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_741_) == 0 {
        let mut v_fst_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_744_);
        v_fst_745_ = crate::leanh::lean_ctor_get(v_x_742_, 0);
        crate::leanh::lean_inc(v_fst_745_);
        v_snd_746_ = crate::leanh::lean_ctor_get(v_x_742_, 1);
        crate::leanh::lean_inc(v_snd_746_);
        crate::leanh::lean_dec_ref(v_x_742_);
        v___x_747_ = crate::leanh::lean_apply_2(v_h__1_743_, v_fst_745_, v_snd_746_);
        return v___x_747_;
    } else {
        let mut v_head_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_743_);
        v_head_748_ = crate::leanh::lean_ctor_get(v_x_741_, 0);
        crate::leanh::lean_inc(v_head_748_);
        v_tail_749_ = crate::leanh::lean_ctor_get(v_x_741_, 1);
        crate::leanh::lean_inc(v_tail_749_);
        crate::leanh::lean_dec_ref_known(v_x_741_, 2);
        v_fst_750_ = crate::leanh::lean_ctor_get(v_x_742_, 0);
        crate::leanh::lean_inc(v_fst_750_);
        v_snd_751_ = crate::leanh::lean_ctor_get(v_x_742_, 1);
        crate::leanh::lean_inc(v_snd_751_);
        crate::leanh::lean_dec_ref(v_x_742_);
        v___x_752_ = crate::leanh::lean_apply_4(
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
    mut v_x_753_: *mut crate::leanh::LeanObject,
    mut v_x_754_: *mut crate::leanh::LeanObject,
    mut v_x_755_: *mut crate::leanh::LeanObject,
    mut v_h__1_756_: *mut crate::leanh::LeanObject,
    mut v_h__2_757_: *mut crate::leanh::LeanObject,
    mut v_h__3_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_753_) == 0 {
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_758_);
        crate::leanh::lean_dec(v_h__2_757_);
        v___x_759_ = crate::leanh::lean_apply_2(v_h__1_756_, v_x_754_, v_x_755_);
        return v___x_759_;
    } else {
        let mut v_head_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_763_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_756_);
        v_head_760_ = crate::leanh::lean_ctor_get(v_x_753_, 0);
        v_tail_761_ = crate::leanh::lean_ctor_get(v_x_753_, 1);
        v_zero_762_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_763_ = lean_nat_dec_eq(v_x_754_, v_zero_762_);
        if v_isZero_763_ == 0 {
            let mut v_one_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_761_);
            crate::leanh::lean_inc(v_head_760_);
            crate::leanh::lean_dec_ref_known(v_x_753_, 2);
            crate::leanh::lean_dec(v_h__3_758_);
            v_one_764_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_765_ = lean_nat_sub(v_x_754_, v_one_764_);
            crate::leanh::lean_dec(v_x_754_);
            v___x_766_ = crate::leanh::lean_apply_4(
                v_h__2_757_,
                v_head_760_,
                v_tail_761_,
                v_n_765_,
                v_x_755_,
            );
            return v___x_766_;
        } else {
            let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_757_);
            v___x_767_ = crate::leanh::lean_apply_5(
                v_h__3_758_,
                v_x_753_,
                v_x_754_,
                v_x_755_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_767_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(
    mut v_00_u03b1_768_: *mut crate::leanh::LeanObject,
    mut v_motive_769_: *mut crate::leanh::LeanObject,
    mut v_x_770_: *mut crate::leanh::LeanObject,
    mut v_x_771_: *mut crate::leanh::LeanObject,
    mut v_x_772_: *mut crate::leanh::LeanObject,
    mut v_h__1_773_: *mut crate::leanh::LeanObject,
    mut v_h__2_774_: *mut crate::leanh::LeanObject,
    mut v_h__3_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_770_) == 0 {
        let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_775_);
        crate::leanh::lean_dec(v_h__2_774_);
        v___x_776_ = crate::leanh::lean_apply_2(v_h__1_773_, v_x_771_, v_x_772_);
        return v___x_776_;
    } else {
        let mut v_head_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_780_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_773_);
        v_head_777_ = crate::leanh::lean_ctor_get(v_x_770_, 0);
        v_tail_778_ = crate::leanh::lean_ctor_get(v_x_770_, 1);
        v_zero_779_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_780_ = lean_nat_dec_eq(v_x_771_, v_zero_779_);
        if v_isZero_780_ == 0 {
            let mut v_one_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_778_);
            crate::leanh::lean_inc(v_head_777_);
            crate::leanh::lean_dec_ref_known(v_x_770_, 2);
            crate::leanh::lean_dec(v_h__3_775_);
            v_one_781_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_782_ = lean_nat_sub(v_x_771_, v_one_781_);
            crate::leanh::lean_dec(v_x_771_);
            v___x_783_ = crate::leanh::lean_apply_4(
                v_h__2_774_,
                v_head_777_,
                v_tail_778_,
                v_n_782_,
                v_x_772_,
            );
            return v___x_783_;
        } else {
            let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_774_);
            v___x_784_ = crate::leanh::lean_apply_5(
                v_h__3_775_,
                v_x_770_,
                v_x_771_,
                v_x_772_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_784_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_785_: *mut crate::leanh::LeanObject,
    mut v_x_786_: *mut crate::leanh::LeanObject,
    mut v_h__1_787_: *mut crate::leanh::LeanObject,
    mut v_h__2_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_785_) == 0 {
        let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_788_);
        v___x_789_ = crate::leanh::lean_apply_1(v_h__1_787_, v_x_786_);
        return v___x_789_;
    } else {
        let mut v_head_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_787_);
        v_head_790_ = crate::leanh::lean_ctor_get(v_x_785_, 0);
        crate::leanh::lean_inc(v_head_790_);
        v_tail_791_ = crate::leanh::lean_ctor_get(v_x_785_, 1);
        crate::leanh::lean_inc(v_tail_791_);
        crate::leanh::lean_dec_ref_known(v_x_785_, 2);
        v___x_792_ = crate::leanh::lean_apply_3(v_h__2_788_, v_head_790_, v_tail_791_, v_x_786_);
        return v___x_792_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_793_: *mut crate::leanh::LeanObject,
    mut v_motive_794_: *mut crate::leanh::LeanObject,
    mut v_x_795_: *mut crate::leanh::LeanObject,
    mut v_x_796_: *mut crate::leanh::LeanObject,
    mut v_h__1_797_: *mut crate::leanh::LeanObject,
    mut v_h__2_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_795_) == 0 {
        let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_798_);
        v___x_799_ = crate::leanh::lean_apply_1(v_h__1_797_, v_x_796_);
        return v___x_799_;
    } else {
        let mut v_head_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_797_);
        v_head_800_ = crate::leanh::lean_ctor_get(v_x_795_, 0);
        crate::leanh::lean_inc(v_head_800_);
        v_tail_801_ = crate::leanh::lean_ctor_get(v_x_795_, 1);
        crate::leanh::lean_inc(v_tail_801_);
        crate::leanh::lean_dec_ref_known(v_x_795_, 2);
        v___x_802_ = crate::leanh::lean_apply_3(v_h__2_798_, v_head_800_, v_tail_801_, v_x_796_);
        return v___x_802_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Annotated(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Annotated(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Lemmas(builtin);
}
