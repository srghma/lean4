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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_402_: *mut LeanObject,
    mut v_h__1_403_: *mut LeanObject,
    mut v_h__2_404_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_402_) == 0 {
        let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_403_);
        v___x_405_ = lean_box(0);
        v___x_406_ = lean_apply_1(v_h__2_404_, v___x_405_);
        return v___x_406_;
    } else {
        let mut v_val_407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_404_);
        v_val_407_ = lean_ctor_get(v_x_402_, 0);
        lean_inc(v_val_407_);
        lean_dec_ref_known(v_x_402_, 1);
        v___x_408_ = lean_apply_1(v_h__1_403_, v_val_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_409_: *mut LeanObject,
    mut v_motive_410_: *mut LeanObject,
    mut v_x_411_: *mut LeanObject,
    mut v_h__1_412_: *mut LeanObject,
    mut v_h__2_413_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_411_) == 0 {
        let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_412_);
        v___x_414_ = lean_box(0);
        v___x_415_ = lean_apply_1(v_h__2_413_, v___x_414_);
        return v___x_415_;
    } else {
        let mut v_val_416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_413_);
        v_val_416_ = lean_ctor_get(v_x_411_, 0);
        lean_inc(v_val_416_);
        lean_dec_ref_known(v_x_411_, 1);
        v___x_417_ = lean_apply_1(v_h__1_412_, v_val_416_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(
    mut v_x_418_: u8,
    mut v_h__1_419_: *mut LeanObject,
    mut v_h__2_420_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_418_ == 0 {
        let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_419_);
        v___x_421_ = lean_box(0);
        v___x_422_ = lean_apply_1(v_h__2_420_, v___x_421_);
        return v___x_422_;
    } else {
        let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_420_);
        v___x_423_ = lean_box(0);
        v___x_424_ = lean_apply_1(v_h__1_419_, v___x_423_);
        return v___x_424_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_425_: *mut LeanObject,
    mut v_h__1_426_: *mut LeanObject,
    mut v_h__2_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_428_: u8 = 0;
    let mut v_res_429_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_428_ = (lean_unbox(v_x_425_) as u8);
    v_res_429_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_428_,
        v_h__1_426_,
        v_h__2_427_,
    );
    return v_res_429_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(
    mut v_motive_430_: *mut LeanObject,
    mut v_x_431_: u8,
    mut v_h__1_432_: *mut LeanObject,
    mut v_h__2_433_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_431_ == 0 {
        let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_432_);
        v___x_434_ = lean_box(0);
        v___x_435_ = lean_apply_1(v_h__2_433_, v___x_434_);
        return v___x_435_;
    } else {
        let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_433_);
        v___x_436_ = lean_box(0);
        v___x_437_ = lean_apply_1(v_h__1_432_, v___x_436_);
        return v___x_437_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter___boxed(
    mut v_motive_438_: *mut LeanObject,
    mut v_x_439_: *mut LeanObject,
    mut v_h__1_440_: *mut LeanObject,
    mut v_h__2_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_442_: u8 = 0;
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_442_ = (lean_unbox(v_x_439_) as u8);
    v_res_443_ = l___private_Init_Data_List_Lemmas_0__List_filter_match__1_splitter(
        v_motive_438_,
        v_x_37__boxed_442_,
        v_h__1_440_,
        v_h__2_441_,
    );
    return v_res_443_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter___redArg(
    mut v_x_444_: *mut LeanObject,
    mut v_x_445_: *mut LeanObject,
    mut v_x_446_: *mut LeanObject,
    mut v_h__1_447_: *mut LeanObject,
    mut v_h__2_448_: *mut LeanObject,
    mut v_h__3_449_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_444_) == 0 {
        lean_dec(v_h__2_448_);
        if lean_obj_tag(v_x_445_) == 0 {
            let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_449_);
            v___x_450_ = lean_apply_1(v_h__1_447_, v_x_446_);
            return v___x_450_;
        } else {
            let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_447_);
            v___x_451_ = lean_apply_5(
                v_h__3_449_,
                v_x_444_,
                v_x_445_,
                v_x_446_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_451_;
        }
    } else {
        lean_dec(v_h__1_447_);
        if lean_obj_tag(v_x_445_) == 1 {
            let mut v_head_452_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_453_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_454_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_449_);
            v_head_452_ = lean_ctor_get(v_x_444_, 0);
            lean_inc(v_head_452_);
            v_tail_453_ = lean_ctor_get(v_x_444_, 1);
            lean_inc(v_tail_453_);
            lean_dec_ref_known(v_x_444_, 2);
            v_head_454_ = lean_ctor_get(v_x_445_, 0);
            lean_inc(v_head_454_);
            v_tail_455_ = lean_ctor_get(v_x_445_, 1);
            lean_inc(v_tail_455_);
            lean_dec_ref_known(v_x_445_, 2);
            v___x_456_ = lean_apply_5(
                v_h__2_448_,
                v_head_452_,
                v_tail_453_,
                v_head_454_,
                v_tail_455_,
                v_x_446_,
            );
            return v___x_456_;
        } else {
            let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_448_);
            v___x_457_ = lean_apply_5(
                v_h__3_449_,
                v_x_444_,
                v_x_445_,
                v_x_446_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_457_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_isEqv_match__1_splitter(
    mut v_00_u03b1_458_: *mut LeanObject,
    mut v_motive_459_: *mut LeanObject,
    mut v_x_460_: *mut LeanObject,
    mut v_x_461_: *mut LeanObject,
    mut v_x_462_: *mut LeanObject,
    mut v_h__1_463_: *mut LeanObject,
    mut v_h__2_464_: *mut LeanObject,
    mut v_h__3_465_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_460_) == 0 {
        lean_dec(v_h__2_464_);
        if lean_obj_tag(v_x_461_) == 0 {
            let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_465_);
            v___x_466_ = lean_apply_1(v_h__1_463_, v_x_462_);
            return v___x_466_;
        } else {
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_463_);
            v___x_467_ = lean_apply_5(
                v_h__3_465_,
                v_x_460_,
                v_x_461_,
                v_x_462_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_467_;
        }
    } else {
        lean_dec(v_h__1_463_);
        if lean_obj_tag(v_x_461_) == 1 {
            let mut v_head_468_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_469_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_470_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_471_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_465_);
            v_head_468_ = lean_ctor_get(v_x_460_, 0);
            lean_inc(v_head_468_);
            v_tail_469_ = lean_ctor_get(v_x_460_, 1);
            lean_inc(v_tail_469_);
            lean_dec_ref_known(v_x_460_, 2);
            v_head_470_ = lean_ctor_get(v_x_461_, 0);
            lean_inc(v_head_470_);
            v_tail_471_ = lean_ctor_get(v_x_461_, 1);
            lean_inc(v_tail_471_);
            lean_dec_ref_known(v_x_461_, 2);
            v___x_472_ = lean_apply_5(
                v_h__2_464_,
                v_head_468_,
                v_tail_469_,
                v_head_470_,
                v_tail_471_,
                v_x_462_,
            );
            return v___x_472_;
        } else {
            let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_464_);
            v___x_473_ = lean_apply_5(
                v_h__3_465_,
                v_x_460_,
                v_x_461_,
                v_x_462_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_473_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter___redArg(
    mut v_x_474_: *mut LeanObject,
    mut v_h__1_475_: *mut LeanObject,
    mut v_h__2_476_: *mut LeanObject,
    mut v_h__3_477_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_474_) == 0 {
        let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_477_);
        lean_dec(v_h__2_476_);
        v___x_478_ = lean_apply_1(v_h__1_475_, lean_box(0));
        return v___x_478_;
    } else {
        let mut v_tail_479_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_475_);
        v_tail_479_ = lean_ctor_get(v_x_474_, 1);
        if lean_obj_tag(v_tail_479_) == 0 {
            let mut v_head_480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_477_);
            v_head_480_ = lean_ctor_get(v_x_474_, 0);
            lean_inc(v_head_480_);
            lean_dec_ref_known(v_x_474_, 2);
            v___x_481_ = lean_apply_2(v_h__2_476_, v_head_480_, lean_box(0));
            return v___x_481_;
        } else {
            let mut v_head_482_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_483_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_479_);
            lean_dec(v_h__2_476_);
            v_head_482_ = lean_ctor_get(v_x_474_, 0);
            lean_inc(v_head_482_);
            lean_dec_ref_known(v_x_474_, 2);
            v_head_483_ = lean_ctor_get(v_tail_479_, 0);
            lean_inc(v_head_483_);
            v_tail_484_ = lean_ctor_get(v_tail_479_, 1);
            lean_inc(v_tail_484_);
            lean_dec_ref_known(v_tail_479_, 2);
            v___x_485_ = lean_apply_4(
                v_h__3_477_,
                v_head_482_,
                v_head_483_,
                v_tail_484_,
                lean_box(0),
            );
            return v___x_485_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_match__1_splitter(
    mut v_00_u03b1_486_: *mut LeanObject,
    mut v_motive_487_: *mut LeanObject,
    mut v_x_488_: *mut LeanObject,
    mut v_x_489_: *mut LeanObject,
    mut v_h__1_490_: *mut LeanObject,
    mut v_h__2_491_: *mut LeanObject,
    mut v_h__3_492_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_488_) == 0 {
        let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_492_);
        lean_dec(v_h__2_491_);
        v___x_493_ = lean_apply_1(v_h__1_490_, lean_box(0));
        return v___x_493_;
    } else {
        let mut v_tail_494_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_490_);
        v_tail_494_ = lean_ctor_get(v_x_488_, 1);
        if lean_obj_tag(v_tail_494_) == 0 {
            let mut v_head_495_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_492_);
            v_head_495_ = lean_ctor_get(v_x_488_, 0);
            lean_inc(v_head_495_);
            lean_dec_ref_known(v_x_488_, 2);
            v___x_496_ = lean_apply_2(v_h__2_491_, v_head_495_, lean_box(0));
            return v___x_496_;
        } else {
            let mut v_head_497_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_498_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_499_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_494_);
            lean_dec(v_h__2_491_);
            v_head_497_ = lean_ctor_get(v_x_488_, 0);
            lean_inc(v_head_497_);
            lean_dec_ref_known(v_x_488_, 2);
            v_head_498_ = lean_ctor_get(v_tail_494_, 0);
            lean_inc(v_head_498_);
            v_tail_499_ = lean_ctor_get(v_tail_494_, 1);
            lean_inc(v_tail_499_);
            lean_dec_ref_known(v_tail_494_, 2);
            v___x_500_ = lean_apply_4(
                v_h__3_492_,
                v_head_497_,
                v_head_498_,
                v_tail_499_,
                lean_box(0),
            );
            return v___x_500_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter___redArg(
    mut v_x_501_: *mut LeanObject,
    mut v_h__1_502_: *mut LeanObject,
    mut v_h__2_503_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_501_) == 0 {
        let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_503_);
        v___x_504_ = lean_box(0);
        v___x_505_ = lean_apply_1(v_h__1_502_, v___x_504_);
        return v___x_505_;
    } else {
        let mut v_head_506_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_502_);
        v_head_506_ = lean_ctor_get(v_x_501_, 0);
        lean_inc(v_head_506_);
        v_tail_507_ = lean_ctor_get(v_x_501_, 1);
        lean_inc(v_tail_507_);
        lean_dec_ref_known(v_x_501_, 2);
        v___x_508_ = lean_apply_2(v_h__2_503_, v_head_506_, v_tail_507_);
        return v___x_508_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x21_match__1_splitter(
    mut v_00_u03b1_509_: *mut LeanObject,
    mut v_motive_510_: *mut LeanObject,
    mut v_x_511_: *mut LeanObject,
    mut v_h__1_512_: *mut LeanObject,
    mut v_h__2_513_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_511_) == 0 {
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_513_);
        v___x_514_ = lean_box(0);
        v___x_515_ = lean_apply_1(v_h__1_512_, v___x_514_);
        return v___x_515_;
    } else {
        let mut v_head_516_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_512_);
        v_head_516_ = lean_ctor_get(v_x_511_, 0);
        lean_inc(v_head_516_);
        v_tail_517_ = lean_ctor_get(v_x_511_, 1);
        lean_inc(v_tail_517_);
        lean_dec_ref_known(v_x_511_, 2);
        v___x_518_ = lean_apply_2(v_h__2_513_, v_head_516_, v_tail_517_);
        return v___x_518_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_519_: *mut LeanObject,
    mut v_h__1_520_: *mut LeanObject,
    mut v_h__2_521_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_519_) == 0 {
        let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_521_);
        v___x_522_ = lean_box(0);
        v___x_523_ = lean_apply_1(v_h__1_520_, v___x_522_);
        return v___x_523_;
    } else {
        let mut v_head_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_520_);
        v_head_524_ = lean_ctor_get(v_x_519_, 0);
        lean_inc(v_head_524_);
        v_tail_525_ = lean_ctor_get(v_x_519_, 1);
        lean_inc(v_tail_525_);
        lean_dec_ref_known(v_x_519_, 2);
        v___x_526_ = lean_apply_2(v_h__2_521_, v_head_524_, v_tail_525_);
        return v___x_526_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_527_: *mut LeanObject,
    mut v_motive_528_: *mut LeanObject,
    mut v_x_529_: *mut LeanObject,
    mut v_h__1_530_: *mut LeanObject,
    mut v_h__2_531_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_529_) == 0 {
        let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_531_);
        v___x_532_ = lean_box(0);
        v___x_533_ = lean_apply_1(v_h__1_530_, v___x_532_);
        return v___x_533_;
    } else {
        let mut v_head_534_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_530_);
        v_head_534_ = lean_ctor_get(v_x_529_, 0);
        lean_inc(v_head_534_);
        v_tail_535_ = lean_ctor_get(v_x_529_, 1);
        lean_inc(v_tail_535_);
        lean_dec_ref_known(v_x_529_, 2);
        v___x_536_ = lean_apply_2(v_h__2_531_, v_head_534_, v_tail_535_);
        return v___x_536_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter___redArg(
    mut v_x_537_: *mut LeanObject,
    mut v_x_538_: *mut LeanObject,
    mut v_h__1_539_: *mut LeanObject,
    mut v_h__2_540_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_537_) == 0 {
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_540_);
        v___x_541_ = lean_apply_1(v_h__1_539_, v_x_538_);
        return v___x_541_;
    } else {
        let mut v_head_542_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_539_);
        v_head_542_ = lean_ctor_get(v_x_537_, 0);
        lean_inc(v_head_542_);
        v_tail_543_ = lean_ctor_get(v_x_537_, 1);
        lean_inc(v_tail_543_);
        lean_dec_ref_known(v_x_537_, 2);
        v___x_544_ = lean_apply_3(v_h__2_540_, v_head_542_, v_tail_543_, v_x_538_);
        return v___x_544_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_getLastD_match__1_splitter(
    mut v_00_u03b1_545_: *mut LeanObject,
    mut v_motive_546_: *mut LeanObject,
    mut v_x_547_: *mut LeanObject,
    mut v_x_548_: *mut LeanObject,
    mut v_h__1_549_: *mut LeanObject,
    mut v_h__2_550_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_547_) == 0 {
        let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_550_);
        v___x_551_ = lean_apply_1(v_h__1_549_, v_x_548_);
        return v___x_551_;
    } else {
        let mut v_head_552_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_549_);
        v_head_552_ = lean_ctor_get(v_x_547_, 0);
        lean_inc(v_head_552_);
        v_tail_553_ = lean_ctor_get(v_x_547_, 1);
        lean_inc(v_tail_553_);
        lean_dec_ref_known(v_x_547_, 2);
        v___x_554_ = lean_apply_3(v_h__2_550_, v_head_552_, v_tail_553_, v_x_548_);
        return v___x_554_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_555_: *mut LeanObject,
    mut v_h__1_556_: *mut LeanObject,
    mut v_h__2_557_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_555_) == 0 {
        let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_557_);
        v___x_558_ = lean_box(0);
        v___x_559_ = lean_apply_1(v_h__1_556_, v___x_558_);
        return v___x_559_;
    } else {
        let mut v_val_560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_556_);
        v_val_560_ = lean_ctor_get(v_x_555_, 0);
        lean_inc(v_val_560_);
        lean_dec_ref_known(v_x_555_, 1);
        v___x_561_ = lean_apply_1(v_h__2_557_, v_val_560_);
        return v___x_561_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_562_: *mut LeanObject,
    mut v_motive_563_: *mut LeanObject,
    mut v_x_564_: *mut LeanObject,
    mut v_h__1_565_: *mut LeanObject,
    mut v_h__2_566_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_564_) == 0 {
        let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_566_);
        v___x_567_ = lean_box(0);
        v___x_568_ = lean_apply_1(v_h__1_565_, v___x_567_);
        return v___x_568_;
    } else {
        let mut v_val_569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_565_);
        v_val_569_ = lean_ctor_get(v_x_564_, 0);
        lean_inc(v_val_569_);
        lean_dec_ref_known(v_x_564_, 1);
        v___x_570_ = lean_apply_1(v_h__2_566_, v_val_569_);
        return v___x_570_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter___redArg(
    mut v_x_571_: *mut LeanObject,
    mut v_h__1_572_: *mut LeanObject,
    mut v_h__2_573_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_571_) == 0 {
        let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_573_);
        v___x_574_ = lean_box(0);
        v___x_575_ = lean_apply_1(v_h__1_572_, v___x_574_);
        return v___x_575_;
    } else {
        let mut v_head_576_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_572_);
        v_head_576_ = lean_ctor_get(v_x_571_, 0);
        lean_inc(v_head_576_);
        v_tail_577_ = lean_ctor_get(v_x_571_, 1);
        lean_inc(v_tail_577_);
        lean_dec_ref_known(v_x_571_, 2);
        v___x_578_ = lean_apply_2(v_h__2_573_, v_head_576_, v_tail_577_);
        return v___x_578_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_flatten_match__1_splitter(
    mut v_00_u03b1_579_: *mut LeanObject,
    mut v_motive_580_: *mut LeanObject,
    mut v_x_581_: *mut LeanObject,
    mut v_h__1_582_: *mut LeanObject,
    mut v_h__2_583_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_581_) == 0 {
        let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_583_);
        v___x_584_ = lean_box(0);
        v___x_585_ = lean_apply_1(v_h__1_582_, v___x_584_);
        return v___x_585_;
    } else {
        let mut v_head_586_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_582_);
        v_head_586_ = lean_ctor_get(v_x_581_, 0);
        lean_inc(v_head_586_);
        v_tail_587_ = lean_ctor_get(v_x_581_, 1);
        lean_inc(v_tail_587_);
        lean_dec_ref_known(v_x_581_, 2);
        v___x_588_ = lean_apply_2(v_h__2_583_, v_head_586_, v_tail_587_);
        return v___x_588_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_589_: *mut LeanObject,
    mut v_h__1_590_: *mut LeanObject,
    mut v_h__2_591_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_589_) == 0 {
        let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_590_);
        v___x_592_ = lean_box(0);
        v___x_593_ = lean_apply_1(v_h__2_591_, v___x_592_);
        return v___x_593_;
    } else {
        let mut v_val_594_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_591_);
        v_val_594_ = lean_ctor_get(v_x_589_, 0);
        lean_inc(v_val_594_);
        lean_dec_ref_known(v_x_589_, 1);
        v___x_595_ = lean_apply_1(v_h__1_590_, v_val_594_);
        return v___x_595_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_596_: *mut LeanObject,
    mut v_motive_597_: *mut LeanObject,
    mut v_x_598_: *mut LeanObject,
    mut v_h__1_599_: *mut LeanObject,
    mut v_h__2_600_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_598_) == 0 {
        let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_599_);
        v___x_601_ = lean_box(0);
        v___x_602_ = lean_apply_1(v_h__2_600_, v___x_601_);
        return v___x_602_;
    } else {
        let mut v_val_603_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_600_);
        v_val_603_ = lean_ctor_get(v_x_598_, 0);
        lean_inc(v_val_603_);
        lean_dec_ref_known(v_x_598_, 1);
        v___x_604_ = lean_apply_1(v_h__1_599_, v_val_603_);
        return v___x_604_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(
    mut v_x_605_: *mut LeanObject,
    mut v_h__1_606_: *mut LeanObject,
    mut v_h__2_607_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_605_) == 0 {
        let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_607_);
        v___x_608_ = lean_box(0);
        v___x_609_ = lean_apply_1(v_h__1_606_, v___x_608_);
        return v___x_609_;
    } else {
        let mut v_val_610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_606_);
        v_val_610_ = lean_ctor_get(v_x_605_, 0);
        lean_inc(v_val_610_);
        lean_dec_ref_known(v_x_605_, 1);
        v___x_611_ = lean_apply_1(v_h__2_607_, v_val_610_);
        return v___x_611_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_filterMap__replicate_match__1_splitter(
    mut v_00_u03b2_612_: *mut LeanObject,
    mut v_motive_613_: *mut LeanObject,
    mut v_x_614_: *mut LeanObject,
    mut v_h__1_615_: *mut LeanObject,
    mut v_h__2_616_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_614_) == 0 {
        let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_616_);
        v___x_617_ = lean_box(0);
        v___x_618_ = lean_apply_1(v_h__1_615_, v___x_617_);
        return v___x_618_;
    } else {
        let mut v_val_619_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_615_);
        v_val_619_ = lean_ctor_get(v_x_614_, 0);
        lean_inc(v_val_619_);
        lean_dec_ref_known(v_x_614_, 1);
        v___x_620_ = lean_apply_1(v_h__2_616_, v_val_619_);
        return v___x_620_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(
    mut v_x_621_: *mut LeanObject,
    mut v_h__1_622_: *mut LeanObject,
    mut v_h__2_623_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_621_) == 0 {
        let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_622_);
        v___x_624_ = lean_box(0);
        v___x_625_ = lean_apply_1(v_h__2_623_, v___x_624_);
        return v___x_625_;
    } else {
        let mut v_val_626_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_623_);
        v_val_626_ = lean_ctor_get(v_x_621_, 0);
        lean_inc(v_val_626_);
        lean_dec_ref_known(v_x_621_, 1);
        v___x_627_ = lean_apply_1(v_h__1_622_, v_val_626_);
        return v___x_627_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_foldl__filterMap_match__1_splitter(
    mut v_00_u03b2_628_: *mut LeanObject,
    mut v_motive_629_: *mut LeanObject,
    mut v_x_630_: *mut LeanObject,
    mut v_h__1_631_: *mut LeanObject,
    mut v_h__2_632_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_630_) == 0 {
        let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_631_);
        v___x_633_ = lean_box(0);
        v___x_634_ = lean_apply_1(v_h__2_632_, v___x_633_);
        return v___x_634_;
    } else {
        let mut v_val_635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_632_);
        v_val_635_ = lean_ctor_get(v_x_630_, 0);
        lean_inc(v_val_635_);
        lean_dec_ref_known(v_x_630_, 1);
        v___x_636_ = lean_apply_1(v_h__1_631_, v_val_635_);
        return v___x_636_;
    }
}
pub unsafe fn l_List_foldlRecOn___redArg___lam__0(
    mut v_x_637_: *mut LeanObject,
    mut v_y_638_: *mut LeanObject,
    mut v_hy_639_: *mut LeanObject,
    mut v_x_640_: *mut LeanObject,
    mut v_hx_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    v___x_642_ = lean_apply_4(v_x_637_, v_y_638_, v_hy_639_, v_x_640_, lean_box(0));
    return v___x_642_;
}
pub unsafe fn l_List_foldlRecOn___redArg(
    mut v_x_643_: *mut LeanObject,
    mut v_x_644_: *mut LeanObject,
    mut v_x_645_: *mut LeanObject,
    mut v_x_646_: *mut LeanObject,
    mut v_x_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_643_) == 0 {
                    lean_dec(v_x_647_);
                    lean_dec(v_x_645_);
                    lean_dec(v_x_644_);
                    return v_x_646_;
                } else {
                    v_head_648_ = lean_ctor_get(v_x_643_, 0);
                    lean_inc_n(v_head_648_, 2);
                    v_tail_649_ = lean_ctor_get(v_x_643_, 1);
                    lean_inc(v_tail_649_);
                    lean_dec_ref_known(v_x_643_, 2);
                    lean_inc(v_x_647_);
                    v___f_650_ = lean_alloc_closure(
                        l_List_foldlRecOn___redArg___lam__0 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    lean_closure_set(v___f_650_, 0, v_x_647_);
                    lean_inc(v_x_644_);
                    lean_inc(v_x_645_);
                    v___x_651_ = lean_apply_2(v_x_644_, v_x_645_, v_head_648_);
                    v___x_652_ =
                        lean_apply_4(v_x_647_, v_x_645_, v_x_646_, v_head_648_, lean_box(0));
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
    mut v_00_u03b2_654_: *mut LeanObject,
    mut v_00_u03b1_655_: *mut LeanObject,
    mut v_motive_656_: *mut LeanObject,
    mut v_x_657_: *mut LeanObject,
    mut v_x_658_: *mut LeanObject,
    mut v_x_659_: *mut LeanObject,
    mut v_x_660_: *mut LeanObject,
    mut v_x_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_662_ = l_List_foldlRecOn___redArg(v_x_657_, v_x_658_, v_x_659_, v_x_660_, v_x_661_);
    return v___x_662_;
}
pub unsafe fn l_List_foldrRecOn___redArg___lam__0(
    mut v_x_663_: *mut LeanObject,
    mut v_b_664_: *mut LeanObject,
    mut v_c_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
    mut v_m_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v___x_668_ = lean_apply_4(v_x_663_, v_b_664_, v_c_665_, v_a_666_, lean_box(0));
    return v___x_668_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(
    mut v_x_669_: *mut LeanObject,
    mut v_init_670_: *mut LeanObject,
    mut v_x_671_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_671_) == 0 {
        lean_dec(v_x_669_);
        lean_inc(v_init_670_);
        return v_init_670_;
    } else {
        let mut v_head_672_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
        v_head_672_ = lean_ctor_get(v_x_671_, 0);
        lean_inc(v_head_672_);
        v_tail_673_ = lean_ctor_get(v_x_671_, 1);
        lean_inc(v_tail_673_);
        lean_dec_ref_known(v_x_671_, 2);
        lean_inc(v_x_669_);
        v___x_674_ = l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(
            v_x_669_,
            v_init_670_,
            v_tail_673_,
        );
        v___x_675_ = lean_apply_2(v_x_669_, v_head_672_, v___x_674_);
        return v___x_675_;
    }
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___redArg___boxed(
    mut v_x_676_: *mut LeanObject,
    mut v_init_677_: *mut LeanObject,
    mut v_x_678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_679_: *mut LeanObject = core::ptr::null_mut();
    v_res_679_ =
        l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_676_, v_init_677_, v_x_678_);
    lean_dec(v_init_677_);
    return v_res_679_;
}
pub unsafe fn l_List_foldrRecOn___redArg(
    mut v_x_680_: *mut LeanObject,
    mut v_x_681_: *mut LeanObject,
    mut v_x_682_: *mut LeanObject,
    mut v_x_683_: *mut LeanObject,
    mut v_x_684_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_680_) == 0 {
        lean_dec(v_x_684_);
        lean_dec(v_x_681_);
        lean_inc(v_x_683_);
        return v_x_683_;
    } else {
        let mut v_head_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        v_head_685_ = lean_ctor_get(v_x_680_, 0);
        lean_inc(v_head_685_);
        v_tail_686_ = lean_ctor_get(v_x_680_, 1);
        lean_inc_n(v_tail_686_, 2);
        lean_dec_ref_known(v_x_680_, 2);
        lean_inc(v_x_684_);
        v___f_687_ = lean_alloc_closure(
            l_List_foldrRecOn___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            1,
        );
        lean_closure_set(v___f_687_, 0, v_x_684_);
        lean_inc(v_x_681_);
        v___x_688_ =
            l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_681_, v_x_682_, v_tail_686_);
        v___x_689_ =
            l_List_foldrRecOn___redArg(v_tail_686_, v_x_681_, v_x_682_, v_x_683_, v___f_687_);
        v___x_690_ = lean_apply_4(v_x_684_, v___x_688_, v___x_689_, v_head_685_, lean_box(0));
        return v___x_690_;
    }
}
pub unsafe fn l_List_foldrRecOn___redArg___boxed(
    mut v_x_691_: *mut LeanObject,
    mut v_x_692_: *mut LeanObject,
    mut v_x_693_: *mut LeanObject,
    mut v_x_694_: *mut LeanObject,
    mut v_x_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ = l_List_foldrRecOn___redArg(v_x_691_, v_x_692_, v_x_693_, v_x_694_, v_x_695_);
    lean_dec(v_x_694_);
    lean_dec(v_x_693_);
    return v_res_696_;
}
pub unsafe fn l_List_foldrRecOn(
    mut v_00_u03b2_697_: *mut LeanObject,
    mut v_00_u03b1_698_: *mut LeanObject,
    mut v_motive_699_: *mut LeanObject,
    mut v_x_700_: *mut LeanObject,
    mut v_x_701_: *mut LeanObject,
    mut v_x_702_: *mut LeanObject,
    mut v_x_703_: *mut LeanObject,
    mut v_x_704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    v___x_705_ = l_List_foldrRecOn___redArg(v_x_700_, v_x_701_, v_x_702_, v_x_703_, v_x_704_);
    return v___x_705_;
}
pub unsafe fn l_List_foldrRecOn___boxed(
    mut v_00_u03b2_706_: *mut LeanObject,
    mut v_00_u03b1_707_: *mut LeanObject,
    mut v_motive_708_: *mut LeanObject,
    mut v_x_709_: *mut LeanObject,
    mut v_x_710_: *mut LeanObject,
    mut v_x_711_: *mut LeanObject,
    mut v_x_712_: *mut LeanObject,
    mut v_x_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_714_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x_712_);
    lean_dec(v_x_711_);
    return v_res_714_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0(
    mut v_00_u03b1_715_: *mut LeanObject,
    mut v_00_u03b2_716_: *mut LeanObject,
    mut v_x_717_: *mut LeanObject,
    mut v_init_718_: *mut LeanObject,
    mut v_x_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    v___x_720_ =
        l_List_foldr___at___00List_foldrRecOn_spec__0___redArg(v_x_717_, v_init_718_, v_x_719_);
    return v___x_720_;
}
pub unsafe fn l_List_foldr___at___00List_foldrRecOn_spec__0___boxed(
    mut v_00_u03b1_721_: *mut LeanObject,
    mut v_00_u03b2_722_: *mut LeanObject,
    mut v_x_723_: *mut LeanObject,
    mut v_init_724_: *mut LeanObject,
    mut v_x_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_726_: *mut LeanObject = core::ptr::null_mut();
    v_res_726_ = l_List_foldr___at___00List_foldrRecOn_spec__0(
        v_00_u03b1_721_,
        v_00_u03b2_722_,
        v_x_723_,
        v_init_724_,
        v_x_725_,
    );
    lean_dec(v_init_724_);
    return v_res_726_;
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_partition_loop_match__1_splitter___redArg(
    mut v_x_727_: *mut LeanObject,
    mut v_x_728_: *mut LeanObject,
    mut v_h__1_729_: *mut LeanObject,
    mut v_h__2_730_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_727_) == 0 {
        let mut v_fst_731_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_730_);
        v_fst_731_ = lean_ctor_get(v_x_728_, 0);
        lean_inc(v_fst_731_);
        v_snd_732_ = lean_ctor_get(v_x_728_, 1);
        lean_inc(v_snd_732_);
        lean_dec_ref(v_x_728_);
        v___x_733_ = lean_apply_2(v_h__1_729_, v_fst_731_, v_snd_732_);
        return v___x_733_;
    } else {
        let mut v_head_734_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_735_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_736_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_729_);
        v_head_734_ = lean_ctor_get(v_x_727_, 0);
        lean_inc(v_head_734_);
        v_tail_735_ = lean_ctor_get(v_x_727_, 1);
        lean_inc(v_tail_735_);
        lean_dec_ref_known(v_x_727_, 2);
        v_fst_736_ = lean_ctor_get(v_x_728_, 0);
        lean_inc(v_fst_736_);
        v_snd_737_ = lean_ctor_get(v_x_728_, 1);
        lean_inc(v_snd_737_);
        lean_dec_ref(v_x_728_);
        v___x_738_ = lean_apply_4(
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
    mut v_00_u03b1_739_: *mut LeanObject,
    mut v_motive_740_: *mut LeanObject,
    mut v_x_741_: *mut LeanObject,
    mut v_x_742_: *mut LeanObject,
    mut v_h__1_743_: *mut LeanObject,
    mut v_h__2_744_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_741_) == 0 {
        let mut v_fst_745_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_744_);
        v_fst_745_ = lean_ctor_get(v_x_742_, 0);
        lean_inc(v_fst_745_);
        v_snd_746_ = lean_ctor_get(v_x_742_, 1);
        lean_inc(v_snd_746_);
        lean_dec_ref(v_x_742_);
        v___x_747_ = lean_apply_2(v_h__1_743_, v_fst_745_, v_snd_746_);
        return v___x_747_;
    } else {
        let mut v_head_748_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_749_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_750_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_743_);
        v_head_748_ = lean_ctor_get(v_x_741_, 0);
        lean_inc(v_head_748_);
        v_tail_749_ = lean_ctor_get(v_x_741_, 1);
        lean_inc(v_tail_749_);
        lean_dec_ref_known(v_x_741_, 2);
        v_fst_750_ = lean_ctor_get(v_x_742_, 0);
        lean_inc(v_fst_750_);
        v_snd_751_ = lean_ctor_get(v_x_742_, 1);
        lean_inc(v_snd_751_);
        lean_dec_ref(v_x_742_);
        v___x_752_ = lean_apply_4(
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
    mut v_x_753_: *mut LeanObject,
    mut v_x_754_: *mut LeanObject,
    mut v_x_755_: *mut LeanObject,
    mut v_h__1_756_: *mut LeanObject,
    mut v_h__2_757_: *mut LeanObject,
    mut v_h__3_758_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_753_) == 0 {
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_758_);
        lean_dec(v_h__2_757_);
        v___x_759_ = lean_apply_2(v_h__1_756_, v_x_754_, v_x_755_);
        return v___x_759_;
    } else {
        let mut v_head_760_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_761_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_763_: u8 = 0;
        lean_dec(v_h__1_756_);
        v_head_760_ = lean_ctor_get(v_x_753_, 0);
        v_tail_761_ = lean_ctor_get(v_x_753_, 1);
        v_zero_762_ = lean_unsigned_to_nat(0);
        v_isZero_763_ = lean_nat_dec_eq(v_x_754_, v_zero_762_);
        if v_isZero_763_ == 0 {
            let mut v_one_764_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_765_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_761_);
            lean_inc(v_head_760_);
            lean_dec_ref_known(v_x_753_, 2);
            lean_dec(v_h__3_758_);
            v_one_764_ = lean_unsigned_to_nat(1);
            v_n_765_ = lean_nat_sub(v_x_754_, v_one_764_);
            lean_dec(v_x_754_);
            v___x_766_ = lean_apply_4(v_h__2_757_, v_head_760_, v_tail_761_, v_n_765_, v_x_755_);
            return v___x_766_;
        } else {
            let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_757_);
            v___x_767_ = lean_apply_5(
                v_h__3_758_,
                v_x_753_,
                v_x_754_,
                v_x_755_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_767_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_splitAt_go_match__1_splitter(
    mut v_00_u03b1_768_: *mut LeanObject,
    mut v_motive_769_: *mut LeanObject,
    mut v_x_770_: *mut LeanObject,
    mut v_x_771_: *mut LeanObject,
    mut v_x_772_: *mut LeanObject,
    mut v_h__1_773_: *mut LeanObject,
    mut v_h__2_774_: *mut LeanObject,
    mut v_h__3_775_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_770_) == 0 {
        let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_775_);
        lean_dec(v_h__2_774_);
        v___x_776_ = lean_apply_2(v_h__1_773_, v_x_771_, v_x_772_);
        return v___x_776_;
    } else {
        let mut v_head_777_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_778_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_779_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_780_: u8 = 0;
        lean_dec(v_h__1_773_);
        v_head_777_ = lean_ctor_get(v_x_770_, 0);
        v_tail_778_ = lean_ctor_get(v_x_770_, 1);
        v_zero_779_ = lean_unsigned_to_nat(0);
        v_isZero_780_ = lean_nat_dec_eq(v_x_771_, v_zero_779_);
        if v_isZero_780_ == 0 {
            let mut v_one_781_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_782_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_778_);
            lean_inc(v_head_777_);
            lean_dec_ref_known(v_x_770_, 2);
            lean_dec(v_h__3_775_);
            v_one_781_ = lean_unsigned_to_nat(1);
            v_n_782_ = lean_nat_sub(v_x_771_, v_one_781_);
            lean_dec(v_x_771_);
            v___x_783_ = lean_apply_4(v_h__2_774_, v_head_777_, v_tail_778_, v_n_782_, v_x_772_);
            return v___x_783_;
        } else {
            let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_774_);
            v___x_784_ = lean_apply_5(
                v_h__3_775_,
                v_x_770_,
                v_x_771_,
                v_x_772_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_784_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_785_: *mut LeanObject,
    mut v_x_786_: *mut LeanObject,
    mut v_h__1_787_: *mut LeanObject,
    mut v_h__2_788_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_785_) == 0 {
        let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_788_);
        v___x_789_ = lean_apply_1(v_h__1_787_, v_x_786_);
        return v___x_789_;
    } else {
        let mut v_head_790_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_787_);
        v_head_790_ = lean_ctor_get(v_x_785_, 0);
        lean_inc(v_head_790_);
        v_tail_791_ = lean_ctor_get(v_x_785_, 1);
        lean_inc(v_tail_791_);
        lean_dec_ref_known(v_x_785_, 2);
        v___x_792_ = lean_apply_3(v_h__2_788_, v_head_790_, v_tail_791_, v_x_786_);
        return v___x_792_;
    }
}
pub unsafe fn l___private_Init_Data_List_Lemmas_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_793_: *mut LeanObject,
    mut v_motive_794_: *mut LeanObject,
    mut v_x_795_: *mut LeanObject,
    mut v_x_796_: *mut LeanObject,
    mut v_h__1_797_: *mut LeanObject,
    mut v_h__2_798_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_795_) == 0 {
        let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_798_);
        v___x_799_ = lean_apply_1(v_h__1_797_, v_x_796_);
        return v___x_799_;
    } else {
        let mut v_head_800_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_797_);
        v_head_800_ = lean_ctor_get(v_x_795_, 0);
        lean_inc(v_head_800_);
        v_tail_801_ = lean_ctor_get(v_x_795_, 1);
        lean_inc(v_tail_801_);
        lean_dec_ref_known(v_x_795_, 2);
        v___x_802_ = lean_apply_3(v_h__2_798_, v_head_800_, v_tail_801_, v_x_796_);
        return v___x_802_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Annotated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Annotated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Lemmas(builtin);
}
