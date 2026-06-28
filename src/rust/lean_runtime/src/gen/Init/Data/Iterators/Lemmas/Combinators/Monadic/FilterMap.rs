// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
// Imports: Init.Data.Iterators.Combinators.Monadic.FilterMap Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Array.Monadic Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.List.Control Init.Data.Bool Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop Init.Data.Iterators.Lemmas.Monadic.Basic
use crate::r#gen::Init::Data::Array::Monadic::{
    initialize_Init_Data_Array_Monadic, runtime_initialize_Init_Data_Array_Monadic,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___redArg(
    mut v_____do__lift_439_: *mut crate::leanh::LeanObject,
    mut v_h__1_440_: *mut crate::leanh::LeanObject,
    mut v_h__2_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_439_) == 0 {
        let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_441_);
        v___x_442_ = crate::leanh::lean_apply_1(v_h__1_440_, crate::leanh::lean_box(0));
        return v___x_442_;
    } else {
        let mut v_val_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_440_);
        v_val_443_ = crate::leanh::lean_ctor_get(v_____do__lift_439_, 0);
        crate::leanh::lean_inc(v_val_443_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_439_, 1);
        v___x_444_ = crate::leanh::lean_apply_2(v_h__2_441_, v_val_443_, crate::leanh::lean_box(0));
        return v___x_444_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(
    mut v_00_u03b2_445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_446_: *mut crate::leanh::LeanObject,
    mut v_n_447_: *mut crate::leanh::LeanObject,
    mut v_f_448_: *mut crate::leanh::LeanObject,
    mut v_out_449_: *mut crate::leanh::LeanObject,
    mut v_motive_450_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_451_: *mut crate::leanh::LeanObject,
    mut v_h__1_452_: *mut crate::leanh::LeanObject,
    mut v_h__2_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_451_) == 0 {
        let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_453_);
        v___x_454_ = crate::leanh::lean_apply_1(v_h__1_452_, crate::leanh::lean_box(0));
        return v___x_454_;
    } else {
        let mut v_val_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_452_);
        v_val_455_ = crate::leanh::lean_ctor_get(v_____do__lift_451_, 0);
        crate::leanh::lean_inc(v_val_455_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_451_, 1);
        v___x_456_ = crate::leanh::lean_apply_2(v_h__2_453_, v_val_455_, crate::leanh::lean_box(0));
        return v___x_456_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___boxed(
    mut v_00_u03b2_457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_458_: *mut crate::leanh::LeanObject,
    mut v_n_459_: *mut crate::leanh::LeanObject,
    mut v_f_460_: *mut crate::leanh::LeanObject,
    mut v_out_461_: *mut crate::leanh::LeanObject,
    mut v_motive_462_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_463_: *mut crate::leanh::LeanObject,
    mut v_h__1_464_: *mut crate::leanh::LeanObject,
    mut v_h__2_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_466_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(v_00_u03b2_457_, v_00_u03b3_458_, v_n_459_, v_f_460_, v_out_461_, v_motive_462_, v_____do__lift_463_, v_h__1_464_, v_h__2_465_);
    crate::leanh::lean_dec(v_out_461_);
    crate::leanh::lean_dec(v_f_460_);
    return v_res_466_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_467_: *mut crate::leanh::LeanObject,
    mut v_h__1_468_: *mut crate::leanh::LeanObject,
    mut v_h__2_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_467_) == 0 {
        let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_469_);
        v___x_470_ = crate::leanh::lean_apply_1(v_h__1_468_, crate::leanh::lean_box(0));
        return v___x_470_;
    } else {
        let mut v_val_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_468_);
        v_val_471_ = crate::leanh::lean_ctor_get(v_____do__lift_467_, 0);
        crate::leanh::lean_inc(v_val_471_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_467_, 1);
        v___x_472_ = crate::leanh::lean_apply_2(v_h__2_469_, v_val_471_, crate::leanh::lean_box(0));
        return v___x_472_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_474_: *mut crate::leanh::LeanObject,
    mut v_n_475_: *mut crate::leanh::LeanObject,
    mut v_f_476_: *mut crate::leanh::LeanObject,
    mut v_out_477_: *mut crate::leanh::LeanObject,
    mut v_motive_478_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_479_: *mut crate::leanh::LeanObject,
    mut v_h__1_480_: *mut crate::leanh::LeanObject,
    mut v_h__2_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_479_) == 0 {
        let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_481_);
        v___x_482_ = crate::leanh::lean_apply_1(v_h__1_480_, crate::leanh::lean_box(0));
        return v___x_482_;
    } else {
        let mut v_val_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_480_);
        v_val_483_ = crate::leanh::lean_ctor_get(v_____do__lift_479_, 0);
        crate::leanh::lean_inc(v_val_483_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_479_, 1);
        v___x_484_ = crate::leanh::lean_apply_2(v_h__2_481_, v_val_483_, crate::leanh::lean_box(0));
        return v___x_484_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_485_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_486_: *mut crate::leanh::LeanObject,
    mut v_n_487_: *mut crate::leanh::LeanObject,
    mut v_f_488_: *mut crate::leanh::LeanObject,
    mut v_out_489_: *mut crate::leanh::LeanObject,
    mut v_motive_490_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_491_: *mut crate::leanh::LeanObject,
    mut v_h__1_492_: *mut crate::leanh::LeanObject,
    mut v_h__2_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_485_, v_00_u03b2_x27_486_, v_n_487_, v_f_488_, v_out_489_, v_motive_490_, v_____do__lift_491_, v_h__1_492_, v_h__2_493_);
    crate::leanh::lean_dec(v_out_489_);
    crate::leanh::lean_dec(v_f_488_);
    return v_res_494_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_495_: u8,
    mut v_h__1_496_: *mut crate::leanh::LeanObject,
    mut v_h__2_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_495_ == 0 {
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_497_);
        v___x_498_ = crate::leanh::lean_apply_1(v_h__1_496_, crate::leanh::lean_box(0));
        return v___x_498_;
    } else {
        let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_496_);
        v___x_499_ = crate::leanh::lean_apply_1(v_h__2_497_, crate::leanh::lean_box(0));
        return v___x_499_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_500_: *mut crate::leanh::LeanObject,
    mut v_h__1_501_: *mut crate::leanh::LeanObject,
    mut v_h__2_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_72__boxed_503_: u8 = 0;
    let mut v_res_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_503_ = (crate::leanh::lean_unbox(v_____do__lift_500_) as u8);
    v_res_504_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_503_, v_h__1_501_, v_h__2_502_);
    return v_res_504_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_505_: *mut crate::leanh::LeanObject,
    mut v_n_506_: *mut crate::leanh::LeanObject,
    mut v_f_507_: *mut crate::leanh::LeanObject,
    mut v_out_508_: *mut crate::leanh::LeanObject,
    mut v_motive_509_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_510_: u8,
    mut v_h__1_511_: *mut crate::leanh::LeanObject,
    mut v_h__2_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_510_ == 0 {
        let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_512_);
        v___x_513_ = crate::leanh::lean_apply_1(v_h__1_511_, crate::leanh::lean_box(0));
        return v___x_513_;
    } else {
        let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_511_);
        v___x_514_ = crate::leanh::lean_apply_1(v_h__2_512_, crate::leanh::lean_box(0));
        return v___x_514_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_515_: *mut crate::leanh::LeanObject,
    mut v_n_516_: *mut crate::leanh::LeanObject,
    mut v_f_517_: *mut crate::leanh::LeanObject,
    mut v_out_518_: *mut crate::leanh::LeanObject,
    mut v_motive_519_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_520_: *mut crate::leanh::LeanObject,
    mut v_h__1_521_: *mut crate::leanh::LeanObject,
    mut v_h__2_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_79__boxed_523_: u8 = 0;
    let mut v_res_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_523_ = (crate::leanh::lean_unbox(v_____do__lift_520_) as u8);
    v_res_524_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_515_, v_n_516_, v_f_517_, v_out_518_, v_motive_519_, v_____do__lift_79__boxed_523_, v_h__1_521_, v_h__2_522_);
    crate::leanh::lean_dec(v_out_518_);
    crate::leanh::lean_dec(v_f_517_);
    return v_res_524_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_525_: u8,
    mut v_h__1_526_: *mut crate::leanh::LeanObject,
    mut v_h__2_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_525_ == 0 {
        let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_527_);
        v___x_528_ = crate::leanh::lean_apply_1(v_h__1_526_, crate::leanh::lean_box(0));
        return v___x_528_;
    } else {
        let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_526_);
        v___x_529_ = crate::leanh::lean_apply_1(v_h__2_527_, crate::leanh::lean_box(0));
        return v___x_529_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_530_: *mut crate::leanh::LeanObject,
    mut v_h__1_531_: *mut crate::leanh::LeanObject,
    mut v_h__2_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_74__boxed_533_: u8 = 0;
    let mut v_res_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_533_ = (crate::leanh::lean_unbox(v_____do__lift_530_) as u8);
    v_res_534_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_533_, v_h__1_531_, v_h__2_532_);
    return v_res_534_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(
    mut v_00_u03b2_535_: *mut crate::leanh::LeanObject,
    mut v_n_536_: *mut crate::leanh::LeanObject,
    mut v_f_537_: *mut crate::leanh::LeanObject,
    mut v_inst_538_: *mut crate::leanh::LeanObject,
    mut v_out_539_: *mut crate::leanh::LeanObject,
    mut v_motive_540_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_541_: u8,
    mut v_h__1_542_: *mut crate::leanh::LeanObject,
    mut v_h__2_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_541_ == 0 {
        let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_543_);
        v___x_544_ = crate::leanh::lean_apply_1(v_h__1_542_, crate::leanh::lean_box(0));
        return v___x_544_;
    } else {
        let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_542_);
        v___x_545_ = crate::leanh::lean_apply_1(v_h__2_543_, crate::leanh::lean_box(0));
        return v___x_545_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_546_: *mut crate::leanh::LeanObject,
    mut v_n_547_: *mut crate::leanh::LeanObject,
    mut v_f_548_: *mut crate::leanh::LeanObject,
    mut v_inst_549_: *mut crate::leanh::LeanObject,
    mut v_out_550_: *mut crate::leanh::LeanObject,
    mut v_motive_551_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_552_: *mut crate::leanh::LeanObject,
    mut v_h__1_553_: *mut crate::leanh::LeanObject,
    mut v_h__2_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_82__boxed_555_: u8 = 0;
    let mut v_res_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_555_ = (crate::leanh::lean_unbox(v_____do__lift_552_) as u8);
    v_res_556_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_546_, v_n_547_, v_f_548_, v_inst_549_, v_out_550_, v_motive_551_, v_____do__lift_82__boxed_555_, v_h__1_553_, v_h__2_554_);
    crate::leanh::lean_dec(v_out_550_);
    crate::leanh::lean_dec(v_inst_549_);
    crate::leanh::lean_dec(v_f_548_);
    return v_res_556_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_557_: *mut crate::leanh::LeanObject,
    mut v_h__1_558_: *mut crate::leanh::LeanObject,
    mut v_h__2_559_: *mut crate::leanh::LeanObject,
    mut v_h__3_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_557_) {
        0 => {
            let mut v_it_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_560_);
            crate::leanh::lean_dec(v_h__2_559_);
            v_it_561_ = crate::leanh::lean_ctor_get(v_x_557_, 0);
            crate::leanh::lean_inc(v_it_561_);
            v_out_562_ = crate::leanh::lean_ctor_get(v_x_557_, 1);
            crate::leanh::lean_inc(v_out_562_);
            crate::leanh::lean_dec_ref_known(v_x_557_, 2);
            v___x_563_ = crate::leanh::lean_apply_3(
                v_h__1_558_,
                v_it_561_,
                v_out_562_,
                crate::leanh::lean_box(0),
            );
            return v___x_563_;
        }
        1 => {
            let mut v_it_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_560_);
            crate::leanh::lean_dec(v_h__1_558_);
            v_it_564_ = crate::leanh::lean_ctor_get(v_x_557_, 0);
            crate::leanh::lean_inc(v_it_564_);
            crate::leanh::lean_dec_ref_known(v_x_557_, 1);
            v___x_565_ =
                crate::leanh::lean_apply_2(v_h__2_559_, v_it_564_, crate::leanh::lean_box(0));
            return v___x_565_;
        }
        _ => {
            let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_559_);
            crate::leanh::lean_dec(v_h__1_558_);
            v___x_566_ = crate::leanh::lean_apply_1(v_h__3_560_, crate::leanh::lean_box(0));
            return v___x_566_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_568_: *mut crate::leanh::LeanObject,
    mut v_m_569_: *mut crate::leanh::LeanObject,
    mut v_inst_570_: *mut crate::leanh::LeanObject,
    mut v_it_571_: *mut crate::leanh::LeanObject,
    mut v_motive_572_: *mut crate::leanh::LeanObject,
    mut v_x_573_: *mut crate::leanh::LeanObject,
    mut v_h__1_574_: *mut crate::leanh::LeanObject,
    mut v_h__2_575_: *mut crate::leanh::LeanObject,
    mut v_h__3_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_573_) {
        0 => {
            let mut v_it_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_576_);
            crate::leanh::lean_dec(v_h__2_575_);
            v_it_577_ = crate::leanh::lean_ctor_get(v_x_573_, 0);
            crate::leanh::lean_inc(v_it_577_);
            v_out_578_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
            crate::leanh::lean_inc(v_out_578_);
            crate::leanh::lean_dec_ref_known(v_x_573_, 2);
            v___x_579_ = crate::leanh::lean_apply_3(
                v_h__1_574_,
                v_it_577_,
                v_out_578_,
                crate::leanh::lean_box(0),
            );
            return v___x_579_;
        }
        1 => {
            let mut v_it_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_576_);
            crate::leanh::lean_dec(v_h__1_574_);
            v_it_580_ = crate::leanh::lean_ctor_get(v_x_573_, 0);
            crate::leanh::lean_inc(v_it_580_);
            crate::leanh::lean_dec_ref_known(v_x_573_, 1);
            v___x_581_ =
                crate::leanh::lean_apply_2(v_h__2_575_, v_it_580_, crate::leanh::lean_box(0));
            return v___x_581_;
        }
        _ => {
            let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_575_);
            crate::leanh::lean_dec(v_h__1_574_);
            v___x_582_ = crate::leanh::lean_apply_1(v_h__3_576_, crate::leanh::lean_box(0));
            return v___x_582_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_583_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_584_: *mut crate::leanh::LeanObject,
    mut v_m_585_: *mut crate::leanh::LeanObject,
    mut v_inst_586_: *mut crate::leanh::LeanObject,
    mut v_it_587_: *mut crate::leanh::LeanObject,
    mut v_motive_588_: *mut crate::leanh::LeanObject,
    mut v_x_589_: *mut crate::leanh::LeanObject,
    mut v_h__1_590_: *mut crate::leanh::LeanObject,
    mut v_h__2_591_: *mut crate::leanh::LeanObject,
    mut v_h__3_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_593_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_583_, v_00_u03b2_584_, v_m_585_, v_inst_586_, v_it_587_, v_motive_588_, v_x_589_, v_h__1_590_, v_h__2_591_, v_h__3_592_);
    crate::leanh::lean_dec(v_it_587_);
    crate::leanh::lean_dec(v_inst_586_);
    return v_res_593_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(
    mut v_x_594_: *mut crate::leanh::LeanObject,
    mut v_h__1_595_: *mut crate::leanh::LeanObject,
    mut v_h__2_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_594_) == 0 {
        let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_596_);
        v___x_597_ = crate::leanh::lean_apply_1(v_h__1_595_, crate::leanh::lean_box(0));
        return v___x_597_;
    } else {
        let mut v_val_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_595_);
        v_val_598_ = crate::leanh::lean_ctor_get(v_x_594_, 0);
        crate::leanh::lean_inc(v_val_598_);
        crate::leanh::lean_dec_ref_known(v_x_594_, 1);
        v___x_599_ = crate::leanh::lean_apply_2(v_h__2_596_, v_val_598_, crate::leanh::lean_box(0));
        return v___x_599_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(
    mut v_00_u03b2_x27_600_: *mut crate::leanh::LeanObject,
    mut v_motive_601_: *mut crate::leanh::LeanObject,
    mut v_x_602_: *mut crate::leanh::LeanObject,
    mut v_h__1_603_: *mut crate::leanh::LeanObject,
    mut v_h__2_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_602_) == 0 {
        let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_604_);
        v___x_605_ = crate::leanh::lean_apply_1(v_h__1_603_, crate::leanh::lean_box(0));
        return v___x_605_;
    } else {
        let mut v_val_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_603_);
        v_val_606_ = crate::leanh::lean_ctor_get(v_x_602_, 0);
        crate::leanh::lean_inc(v_val_606_);
        crate::leanh::lean_dec_ref_known(v_x_602_, 1);
        v___x_607_ = crate::leanh::lean_apply_2(v_h__2_604_, v_val_606_, crate::leanh::lean_box(0));
        return v___x_607_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_608_: *mut crate::leanh::LeanObject,
    mut v_h__1_609_: *mut crate::leanh::LeanObject,
    mut v_h__2_610_: *mut crate::leanh::LeanObject,
    mut v_h__3_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_608_) {
        0 => {
            let mut v_it_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_611_);
            crate::leanh::lean_dec(v_h__2_610_);
            v_it_612_ = crate::leanh::lean_ctor_get(v_x_608_, 0);
            crate::leanh::lean_inc(v_it_612_);
            v_out_613_ = crate::leanh::lean_ctor_get(v_x_608_, 1);
            crate::leanh::lean_inc(v_out_613_);
            crate::leanh::lean_dec_ref_known(v_x_608_, 2);
            v___x_614_ = crate::leanh::lean_apply_2(v_h__1_609_, v_it_612_, v_out_613_);
            return v___x_614_;
        }
        1 => {
            let mut v_it_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_611_);
            crate::leanh::lean_dec(v_h__1_609_);
            v_it_615_ = crate::leanh::lean_ctor_get(v_x_608_, 0);
            crate::leanh::lean_inc(v_it_615_);
            crate::leanh::lean_dec_ref_known(v_x_608_, 1);
            v___x_616_ = crate::leanh::lean_apply_1(v_h__2_610_, v_it_615_);
            return v___x_616_;
        }
        _ => {
            let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_610_);
            crate::leanh::lean_dec(v_h__1_609_);
            v___x_617_ = crate::leanh::lean_box(0);
            v___x_618_ = crate::leanh::lean_apply_1(v_h__3_611_, v___x_617_);
            return v___x_618_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_620_: *mut crate::leanh::LeanObject,
    mut v_m_621_: *mut crate::leanh::LeanObject,
    mut v_motive_622_: *mut crate::leanh::LeanObject,
    mut v_x_623_: *mut crate::leanh::LeanObject,
    mut v_h__1_624_: *mut crate::leanh::LeanObject,
    mut v_h__2_625_: *mut crate::leanh::LeanObject,
    mut v_h__3_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_623_) {
        0 => {
            let mut v_it_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_626_);
            crate::leanh::lean_dec(v_h__2_625_);
            v_it_627_ = crate::leanh::lean_ctor_get(v_x_623_, 0);
            crate::leanh::lean_inc(v_it_627_);
            v_out_628_ = crate::leanh::lean_ctor_get(v_x_623_, 1);
            crate::leanh::lean_inc(v_out_628_);
            crate::leanh::lean_dec_ref_known(v_x_623_, 2);
            v___x_629_ = crate::leanh::lean_apply_2(v_h__1_624_, v_it_627_, v_out_628_);
            return v___x_629_;
        }
        1 => {
            let mut v_it_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_626_);
            crate::leanh::lean_dec(v_h__1_624_);
            v_it_630_ = crate::leanh::lean_ctor_get(v_x_623_, 0);
            crate::leanh::lean_inc(v_it_630_);
            crate::leanh::lean_dec_ref_known(v_x_623_, 1);
            v___x_631_ = crate::leanh::lean_apply_1(v_h__2_625_, v_it_630_);
            return v___x_631_;
        }
        _ => {
            let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_625_);
            crate::leanh::lean_dec(v_h__1_624_);
            v___x_632_ = crate::leanh::lean_box(0);
            v___x_633_ = crate::leanh::lean_apply_1(v_h__3_626_, v___x_632_);
            return v___x_633_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_634_: *mut crate::leanh::LeanObject,
    mut v_h__1_635_: *mut crate::leanh::LeanObject,
    mut v_h__2_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_634_) == 0 {
        let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_636_);
        v___x_637_ = crate::leanh::lean_box(0);
        v___x_638_ = crate::leanh::lean_apply_1(v_h__1_635_, v___x_637_);
        return v___x_638_;
    } else {
        let mut v_val_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_635_);
        v_val_639_ = crate::leanh::lean_ctor_get(v_x_634_, 0);
        crate::leanh::lean_inc(v_val_639_);
        crate::leanh::lean_dec_ref_known(v_x_634_, 1);
        v___x_640_ = crate::leanh::lean_apply_1(v_h__2_636_, v_val_639_);
        return v___x_640_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_641_: *mut crate::leanh::LeanObject,
    mut v_motive_642_: *mut crate::leanh::LeanObject,
    mut v_x_643_: *mut crate::leanh::LeanObject,
    mut v_h__1_644_: *mut crate::leanh::LeanObject,
    mut v_h__2_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_643_) == 0 {
        let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_645_);
        v___x_646_ = crate::leanh::lean_box(0);
        v___x_647_ = crate::leanh::lean_apply_1(v_h__1_644_, v___x_646_);
        return v___x_647_;
    } else {
        let mut v_val_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_644_);
        v_val_648_ = crate::leanh::lean_ctor_get(v_x_643_, 0);
        crate::leanh::lean_inc(v_val_648_);
        crate::leanh::lean_dec_ref_known(v_x_643_, 1);
        v___x_649_ = crate::leanh::lean_apply_1(v_h__2_645_, v_val_648_);
        return v___x_649_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27___redArg(
    mut v_t_650_: *mut crate::leanh::LeanObject,
    mut v_mk_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = crate::leanh::lean_apply_2(v_mk_651_, v_t_650_, crate::leanh::lean_box(0));
    return v___x_652_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27(
    mut v_00_u03b1_653_: *mut crate::leanh::LeanObject,
    mut v_p_654_: *mut crate::leanh::LeanObject,
    mut v_motive_655_: *mut crate::leanh::LeanObject,
    mut v_t_656_: *mut crate::leanh::LeanObject,
    mut v_mk_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = crate::leanh::lean_apply_2(v_mk_657_, v_t_656_, crate::leanh::lean_box(0));
    return v___x_658_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(
    mut v_t_659_: *mut crate::leanh::LeanObject,
    mut v_n_660_: *mut crate::leanh::LeanObject,
    mut v_s_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_659_) == 0 {
        let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_s_661_);
        v___x_662_ = crate::leanh::lean_apply_1(v_n_660_, crate::leanh::lean_box(0));
        return v___x_662_;
    } else {
        let mut v_val_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_n_660_);
        v_val_663_ = crate::leanh::lean_ctor_get(v_t_659_, 0);
        crate::leanh::lean_inc(v_val_663_);
        crate::leanh::lean_dec_ref_known(v_t_659_, 1);
        v___x_664_ = crate::leanh::lean_apply_2(v_s_661_, v_val_663_, crate::leanh::lean_box(0));
        return v___x_664_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27(
    mut v_00_u03b1_665_: *mut crate::leanh::LeanObject,
    mut v_t_666_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_667_: *mut crate::leanh::LeanObject,
    mut v_n_668_: *mut crate::leanh::LeanObject,
    mut v_s_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(v_t_666_, v_n_668_, v_s_669_);
    return v___x_670_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(
    mut v_t_671_: *mut crate::leanh::LeanObject,
    mut v_n_672_: *mut crate::leanh::LeanObject,
    mut v_s_673_: *mut crate::leanh::LeanObject,
    mut v_h__1_674_: *mut crate::leanh::LeanObject,
    mut v_h__2_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_671_) == 0 {
        let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_674_);
        v___x_676_ = crate::leanh::lean_apply_2(v_h__2_675_, v_n_672_, v_s_673_);
        return v___x_676_;
    } else {
        let mut v_val_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_675_);
        v_val_677_ = crate::leanh::lean_ctor_get(v_t_671_, 0);
        crate::leanh::lean_inc(v_val_677_);
        crate::leanh::lean_dec_ref_known(v_t_671_, 1);
        v___x_678_ = crate::leanh::lean_apply_3(v_h__1_674_, v_val_677_, v_n_672_, v_s_673_);
        return v___x_678_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter(
    mut v_00_u03b1_679_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_680_: *mut crate::leanh::LeanObject,
    mut v_motive_681_: *mut crate::leanh::LeanObject,
    mut v_t_682_: *mut crate::leanh::LeanObject,
    mut v_n_683_: *mut crate::leanh::LeanObject,
    mut v_s_684_: *mut crate::leanh::LeanObject,
    mut v_h__1_685_: *mut crate::leanh::LeanObject,
    mut v_h__2_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_682_) == 0 {
        let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_685_);
        v___x_687_ = crate::leanh::lean_apply_2(v_h__2_686_, v_n_683_, v_s_684_);
        return v___x_687_;
    } else {
        let mut v_val_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_686_);
        v_val_688_ = crate::leanh::lean_ctor_get(v_t_682_, 0);
        crate::leanh::lean_inc(v_val_688_);
        crate::leanh::lean_dec_ref_known(v_t_682_, 1);
        v___x_689_ = crate::leanh::lean_apply_3(v_h__1_685_, v_val_688_, v_n_683_, v_s_684_);
        return v___x_689_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_690_: *mut crate::leanh::LeanObject,
    mut v_h__1_691_: *mut crate::leanh::LeanObject,
    mut v_h__2_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_690_) == 0 {
        let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_692_);
        v___x_693_ = crate::leanh::lean_apply_1(v_h__1_691_, crate::leanh::lean_box(0));
        return v___x_693_;
    } else {
        let mut v_val_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_691_);
        v_val_694_ = crate::leanh::lean_ctor_get(v_____do__lift_690_, 0);
        crate::leanh::lean_inc(v_val_694_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_690_, 1);
        v___x_695_ = crate::leanh::lean_apply_2(v_h__2_692_, v_val_694_, crate::leanh::lean_box(0));
        return v___x_695_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_696_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_697_: *mut crate::leanh::LeanObject,
    mut v_n_698_: *mut crate::leanh::LeanObject,
    mut v_f_699_: *mut crate::leanh::LeanObject,
    mut v_inst_700_: *mut crate::leanh::LeanObject,
    mut v_out_701_: *mut crate::leanh::LeanObject,
    mut v_motive_702_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_703_: *mut crate::leanh::LeanObject,
    mut v_h__1_704_: *mut crate::leanh::LeanObject,
    mut v_h__2_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_703_) == 0 {
        let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_705_);
        v___x_706_ = crate::leanh::lean_apply_1(v_h__1_704_, crate::leanh::lean_box(0));
        return v___x_706_;
    } else {
        let mut v_val_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_704_);
        v_val_707_ = crate::leanh::lean_ctor_get(v_____do__lift_703_, 0);
        crate::leanh::lean_inc(v_val_707_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_703_, 1);
        v___x_708_ = crate::leanh::lean_apply_2(v_h__2_705_, v_val_707_, crate::leanh::lean_box(0));
        return v___x_708_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_709_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_710_: *mut crate::leanh::LeanObject,
    mut v_n_711_: *mut crate::leanh::LeanObject,
    mut v_f_712_: *mut crate::leanh::LeanObject,
    mut v_inst_713_: *mut crate::leanh::LeanObject,
    mut v_out_714_: *mut crate::leanh::LeanObject,
    mut v_motive_715_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_716_: *mut crate::leanh::LeanObject,
    mut v_h__1_717_: *mut crate::leanh::LeanObject,
    mut v_h__2_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_719_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_709_, v_00_u03b2_x27_710_, v_n_711_, v_f_712_, v_inst_713_, v_out_714_, v_motive_715_, v_____do__lift_716_, v_h__1_717_, v_h__2_718_);
    crate::leanh::lean_dec(v_out_714_);
    crate::leanh::lean_dec(v_inst_713_);
    crate::leanh::lean_dec(v_f_712_);
    return v_res_719_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(
    mut v_____do__lift_720_: *mut crate::leanh::LeanObject,
    mut v_h__1_721_: *mut crate::leanh::LeanObject,
    mut v_h__2_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_720_) == 0 {
        let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_722_);
        v___x_723_ = crate::leanh::lean_box(0);
        v___x_724_ = crate::leanh::lean_apply_1(v_h__1_721_, v___x_723_);
        return v___x_724_;
    } else {
        let mut v_val_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_721_);
        v_val_725_ = crate::leanh::lean_ctor_get(v_____do__lift_720_, 0);
        crate::leanh::lean_inc(v_val_725_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_720_, 1);
        v___x_726_ = crate::leanh::lean_apply_1(v_h__2_722_, v_val_725_);
        return v___x_726_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter(
    mut v_00_u03b3_727_: *mut crate::leanh::LeanObject,
    mut v_motive_728_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_729_: *mut crate::leanh::LeanObject,
    mut v_h__1_730_: *mut crate::leanh::LeanObject,
    mut v_h__2_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_729_) == 0 {
        let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_731_);
        v___x_732_ = crate::leanh::lean_box(0);
        v___x_733_ = crate::leanh::lean_apply_1(v_h__1_730_, v___x_732_);
        return v___x_733_;
    } else {
        let mut v_val_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_730_);
        v_val_734_ = crate::leanh::lean_ctor_get(v_____do__lift_729_, 0);
        crate::leanh::lean_inc(v_val_734_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_729_, 1);
        v___x_735_ = crate::leanh::lean_apply_1(v_h__2_731_, v_val_734_);
        return v___x_735_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_736_: *mut crate::leanh::LeanObject,
    mut v_h__1_737_: *mut crate::leanh::LeanObject,
    mut v_h__2_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_736_) == 0 {
        let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_738_);
        v___x_739_ = crate::leanh::lean_box(0);
        v___x_740_ = crate::leanh::lean_apply_1(v_h__1_737_, v___x_739_);
        return v___x_740_;
    } else {
        let mut v_val_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_737_);
        v_val_741_ = crate::leanh::lean_ctor_get(v_____do__lift_736_, 0);
        crate::leanh::lean_inc(v_val_741_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_736_, 1);
        v___x_742_ = crate::leanh::lean_apply_1(v_h__2_738_, v_val_741_);
        return v___x_742_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_743_: *mut crate::leanh::LeanObject,
    mut v_motive_744_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_745_: *mut crate::leanh::LeanObject,
    mut v_h__1_746_: *mut crate::leanh::LeanObject,
    mut v_h__2_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_745_) == 0 {
        let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_747_);
        v___x_748_ = crate::leanh::lean_box(0);
        v___x_749_ = crate::leanh::lean_apply_1(v_h__1_746_, v___x_748_);
        return v___x_749_;
    } else {
        let mut v_val_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_746_);
        v_val_750_ = crate::leanh::lean_ctor_get(v_____do__lift_745_, 0);
        crate::leanh::lean_inc(v_val_750_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_745_, 1);
        v___x_751_ = crate::leanh::lean_apply_1(v_h__2_747_, v_val_750_);
        return v___x_751_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(
    mut v_____do__lift_752_: *mut crate::leanh::LeanObject,
    mut v_h__1_753_: *mut crate::leanh::LeanObject,
    mut v_h__2_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_752_) == 0 {
        let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_754_);
        v___x_755_ = crate::leanh::lean_box(0);
        v___x_756_ = crate::leanh::lean_apply_1(v_h__1_753_, v___x_755_);
        return v___x_756_;
    } else {
        let mut v_val_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_753_);
        v_val_757_ = crate::leanh::lean_ctor_get(v_____do__lift_752_, 0);
        crate::leanh::lean_inc(v_val_757_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_752_, 1);
        v___x_758_ = crate::leanh::lean_apply_1(v_h__2_754_, v_val_757_);
        return v___x_758_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter(
    mut v_00_u03b2_759_: *mut crate::leanh::LeanObject,
    mut v_motive_760_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_761_: *mut crate::leanh::LeanObject,
    mut v_h__1_762_: *mut crate::leanh::LeanObject,
    mut v_h__2_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_761_) == 0 {
        let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_763_);
        v___x_764_ = crate::leanh::lean_box(0);
        v___x_765_ = crate::leanh::lean_apply_1(v_h__1_762_, v___x_764_);
        return v___x_765_;
    } else {
        let mut v_val_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_762_);
        v_val_766_ = crate::leanh::lean_ctor_get(v_____do__lift_761_, 0);
        crate::leanh::lean_inc(v_val_766_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_761_, 1);
        v___x_767_ = crate::leanh::lean_apply_1(v_h__2_763_, v_val_766_);
        return v___x_767_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_768_: *mut crate::leanh::LeanObject,
    mut v_h__1_769_: *mut crate::leanh::LeanObject,
    mut v_h__2_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_768_) == 0 {
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_769_);
        v___x_771_ = crate::leanh::lean_box(0);
        v___x_772_ = crate::leanh::lean_apply_1(v_h__2_770_, v___x_771_);
        return v___x_772_;
    } else {
        let mut v_val_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_770_);
        v_val_773_ = crate::leanh::lean_ctor_get(v_____do__lift_768_, 0);
        crate::leanh::lean_inc(v_val_773_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_768_, 1);
        v___x_774_ = crate::leanh::lean_apply_1(v_h__1_769_, v_val_773_);
        return v___x_774_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_775_: *mut crate::leanh::LeanObject,
    mut v_motive_776_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_777_: *mut crate::leanh::LeanObject,
    mut v_h__1_778_: *mut crate::leanh::LeanObject,
    mut v_h__2_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_777_) == 0 {
        let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_778_);
        v___x_780_ = crate::leanh::lean_box(0);
        v___x_781_ = crate::leanh::lean_apply_1(v_h__2_779_, v___x_780_);
        return v___x_781_;
    } else {
        let mut v_val_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_779_);
        v_val_782_ = crate::leanh::lean_ctor_get(v_____do__lift_777_, 0);
        crate::leanh::lean_inc(v_val_782_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_777_, 1);
        v___x_783_ = crate::leanh::lean_apply_1(v_h__1_778_, v_val_782_);
        return v___x_783_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_784_: *mut crate::leanh::LeanObject,
    mut v_h__1_785_: *mut crate::leanh::LeanObject,
    mut v_h__2_786_: *mut crate::leanh::LeanObject,
    mut v_h__3_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_784_) {
        0 => {
            let mut v_it_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_787_);
            crate::leanh::lean_dec(v_h__2_786_);
            v_it_788_ = crate::leanh::lean_ctor_get(v_x_784_, 0);
            crate::leanh::lean_inc(v_it_788_);
            v_out_789_ = crate::leanh::lean_ctor_get(v_x_784_, 1);
            crate::leanh::lean_inc(v_out_789_);
            crate::leanh::lean_dec_ref_known(v_x_784_, 2);
            v___x_790_ = crate::leanh::lean_apply_3(
                v_h__1_785_,
                v_it_788_,
                v_out_789_,
                crate::leanh::lean_box(0),
            );
            return v___x_790_;
        }
        1 => {
            let mut v_it_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_787_);
            crate::leanh::lean_dec(v_h__1_785_);
            v_it_791_ = crate::leanh::lean_ctor_get(v_x_784_, 0);
            crate::leanh::lean_inc(v_it_791_);
            crate::leanh::lean_dec_ref_known(v_x_784_, 1);
            v___x_792_ =
                crate::leanh::lean_apply_2(v_h__2_786_, v_it_791_, crate::leanh::lean_box(0));
            return v___x_792_;
        }
        _ => {
            let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_786_);
            crate::leanh::lean_dec(v_h__1_785_);
            v___x_793_ = crate::leanh::lean_apply_1(v_h__3_787_, crate::leanh::lean_box(0));
            return v___x_793_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_794_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_795_: *mut crate::leanh::LeanObject,
    mut v_m_796_: *mut crate::leanh::LeanObject,
    mut v_inst_797_: *mut crate::leanh::LeanObject,
    mut v_it_798_: *mut crate::leanh::LeanObject,
    mut v_motive_799_: *mut crate::leanh::LeanObject,
    mut v_x_800_: *mut crate::leanh::LeanObject,
    mut v_h__1_801_: *mut crate::leanh::LeanObject,
    mut v_h__2_802_: *mut crate::leanh::LeanObject,
    mut v_h__3_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_800_) {
        0 => {
            let mut v_it_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_803_);
            crate::leanh::lean_dec(v_h__2_802_);
            v_it_804_ = crate::leanh::lean_ctor_get(v_x_800_, 0);
            crate::leanh::lean_inc(v_it_804_);
            v_out_805_ = crate::leanh::lean_ctor_get(v_x_800_, 1);
            crate::leanh::lean_inc(v_out_805_);
            crate::leanh::lean_dec_ref_known(v_x_800_, 2);
            v___x_806_ = crate::leanh::lean_apply_3(
                v_h__1_801_,
                v_it_804_,
                v_out_805_,
                crate::leanh::lean_box(0),
            );
            return v___x_806_;
        }
        1 => {
            let mut v_it_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_803_);
            crate::leanh::lean_dec(v_h__1_801_);
            v_it_807_ = crate::leanh::lean_ctor_get(v_x_800_, 0);
            crate::leanh::lean_inc(v_it_807_);
            crate::leanh::lean_dec_ref_known(v_x_800_, 1);
            v___x_808_ =
                crate::leanh::lean_apply_2(v_h__2_802_, v_it_807_, crate::leanh::lean_box(0));
            return v___x_808_;
        }
        _ => {
            let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_802_);
            crate::leanh::lean_dec(v_h__1_801_);
            v___x_809_ = crate::leanh::lean_apply_1(v_h__3_803_, crate::leanh::lean_box(0));
            return v___x_809_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_810_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_811_: *mut crate::leanh::LeanObject,
    mut v_m_812_: *mut crate::leanh::LeanObject,
    mut v_inst_813_: *mut crate::leanh::LeanObject,
    mut v_it_814_: *mut crate::leanh::LeanObject,
    mut v_motive_815_: *mut crate::leanh::LeanObject,
    mut v_x_816_: *mut crate::leanh::LeanObject,
    mut v_h__1_817_: *mut crate::leanh::LeanObject,
    mut v_h__2_818_: *mut crate::leanh::LeanObject,
    mut v_h__3_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_810_, v_00_u03b2_811_, v_m_812_, v_inst_813_, v_it_814_, v_motive_815_, v_x_816_, v_h__1_817_, v_h__2_818_, v_h__3_819_);
    crate::leanh::lean_dec(v_it_814_);
    crate::leanh::lean_dec(v_inst_813_);
    return v_res_820_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_821_: *mut crate::leanh::LeanObject,
    mut v_h__1_822_: *mut crate::leanh::LeanObject,
    mut v_h__2_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_821_) == 0 {
        let mut v_a_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_822_);
        v_a_824_ = crate::leanh::lean_ctor_get(v_____do__lift_821_, 0);
        crate::leanh::lean_inc(v_a_824_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_821_, 1);
        v___x_825_ = crate::leanh::lean_apply_1(v_h__2_823_, v_a_824_);
        return v___x_825_;
    } else {
        let mut v_a_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_823_);
        v_a_826_ = crate::leanh::lean_ctor_get(v_____do__lift_821_, 0);
        crate::leanh::lean_inc(v_a_826_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_821_, 1);
        v___x_827_ = crate::leanh::lean_apply_1(v_h__1_822_, v_a_826_);
        return v___x_827_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_828_: *mut crate::leanh::LeanObject,
    mut v_motive_829_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_830_: *mut crate::leanh::LeanObject,
    mut v_h__1_831_: *mut crate::leanh::LeanObject,
    mut v_h__2_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_830_) == 0 {
        let mut v_a_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_831_);
        v_a_833_ = crate::leanh::lean_ctor_get(v_____do__lift_830_, 0);
        crate::leanh::lean_inc(v_a_833_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_830_, 1);
        v___x_834_ = crate::leanh::lean_apply_1(v_h__2_832_, v_a_833_);
        return v___x_834_;
    } else {
        let mut v_a_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_832_);
        v_a_835_ = crate::leanh::lean_ctor_get(v_____do__lift_830_, 0);
        crate::leanh::lean_inc(v_a_835_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_830_, 1);
        v___x_836_ = crate::leanh::lean_apply_1(v_h__1_831_, v_a_835_);
        return v___x_836_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_837_: *mut crate::leanh::LeanObject,
    mut v_h__1_838_: *mut crate::leanh::LeanObject,
    mut v_h__2_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_837_) == 1 {
        let mut v_val_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_839_);
        v_val_840_ = crate::leanh::lean_ctor_get(v_____x_837_, 0);
        crate::leanh::lean_inc(v_val_840_);
        crate::leanh::lean_dec_ref_known(v_____x_837_, 1);
        v___x_841_ = crate::leanh::lean_apply_1(v_h__1_838_, v_val_840_);
        return v___x_841_;
    } else {
        let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_838_);
        v___x_842_ =
            crate::leanh::lean_apply_2(v_h__2_839_, v_____x_837_, crate::leanh::lean_box(0));
        return v___x_842_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_843_: *mut crate::leanh::LeanObject,
    mut v_motive_844_: *mut crate::leanh::LeanObject,
    mut v_____x_845_: *mut crate::leanh::LeanObject,
    mut v_h__1_846_: *mut crate::leanh::LeanObject,
    mut v_h__2_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_845_) == 1 {
        let mut v_val_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_847_);
        v_val_848_ = crate::leanh::lean_ctor_get(v_____x_845_, 0);
        crate::leanh::lean_inc(v_val_848_);
        crate::leanh::lean_dec_ref_known(v_____x_845_, 1);
        v___x_849_ = crate::leanh::lean_apply_1(v_h__1_846_, v_val_848_);
        return v___x_849_;
    } else {
        let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_846_);
        v___x_850_ =
            crate::leanh::lean_apply_2(v_h__2_847_, v_____x_845_, crate::leanh::lean_box(0));
        return v___x_850_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_851_: *mut crate::leanh::LeanObject,
    mut v_h__1_852_: *mut crate::leanh::LeanObject,
    mut v_h__2_853_: *mut crate::leanh::LeanObject,
    mut v_h__3_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_851_) {
        0 => {
            let mut v_it_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_854_);
            crate::leanh::lean_dec(v_h__2_853_);
            v_it_855_ = crate::leanh::lean_ctor_get(v_x_851_, 0);
            crate::leanh::lean_inc(v_it_855_);
            v_out_856_ = crate::leanh::lean_ctor_get(v_x_851_, 1);
            crate::leanh::lean_inc(v_out_856_);
            crate::leanh::lean_dec_ref_known(v_x_851_, 2);
            v___x_857_ = crate::leanh::lean_apply_2(v_h__1_852_, v_it_855_, v_out_856_);
            return v___x_857_;
        }
        1 => {
            let mut v_it_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_854_);
            crate::leanh::lean_dec(v_h__1_852_);
            v_it_858_ = crate::leanh::lean_ctor_get(v_x_851_, 0);
            crate::leanh::lean_inc(v_it_858_);
            crate::leanh::lean_dec_ref_known(v_x_851_, 1);
            v___x_859_ = crate::leanh::lean_apply_1(v_h__2_853_, v_it_858_);
            return v___x_859_;
        }
        _ => {
            let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_853_);
            crate::leanh::lean_dec(v_h__1_852_);
            v___x_860_ = crate::leanh::lean_box(0);
            v___x_861_ = crate::leanh::lean_apply_1(v_h__3_854_, v___x_860_);
            return v___x_861_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_863_: *mut crate::leanh::LeanObject,
    mut v_m_864_: *mut crate::leanh::LeanObject,
    mut v_motive_865_: *mut crate::leanh::LeanObject,
    mut v_x_866_: *mut crate::leanh::LeanObject,
    mut v_h__1_867_: *mut crate::leanh::LeanObject,
    mut v_h__2_868_: *mut crate::leanh::LeanObject,
    mut v_h__3_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_866_) {
        0 => {
            let mut v_it_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_869_);
            crate::leanh::lean_dec(v_h__2_868_);
            v_it_870_ = crate::leanh::lean_ctor_get(v_x_866_, 0);
            crate::leanh::lean_inc(v_it_870_);
            v_out_871_ = crate::leanh::lean_ctor_get(v_x_866_, 1);
            crate::leanh::lean_inc(v_out_871_);
            crate::leanh::lean_dec_ref_known(v_x_866_, 2);
            v___x_872_ = crate::leanh::lean_apply_2(v_h__1_867_, v_it_870_, v_out_871_);
            return v___x_872_;
        }
        1 => {
            let mut v_it_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_869_);
            crate::leanh::lean_dec(v_h__1_867_);
            v_it_873_ = crate::leanh::lean_ctor_get(v_x_866_, 0);
            crate::leanh::lean_inc(v_it_873_);
            crate::leanh::lean_dec_ref_known(v_x_866_, 1);
            v___x_874_ = crate::leanh::lean_apply_1(v_h__2_868_, v_it_873_);
            return v___x_874_;
        }
        _ => {
            let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_868_);
            crate::leanh::lean_dec(v_h__1_867_);
            v___x_875_ = crate::leanh::lean_box(0);
            v___x_876_ = crate::leanh::lean_apply_1(v_h__3_869_, v___x_875_);
            return v___x_876_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}
