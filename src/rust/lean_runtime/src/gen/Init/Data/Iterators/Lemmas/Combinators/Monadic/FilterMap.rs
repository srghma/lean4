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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___redArg(
    mut v_____do__lift_439_: *mut LeanObject,
    mut v_h__1_440_: *mut LeanObject,
    mut v_h__2_441_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_439_) == 0 {
        let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_441_);
        v___x_442_ = lean_apply_1(v_h__1_440_, lean_box(0));
        return v___x_442_;
    } else {
        let mut v_val_443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_440_);
        v_val_443_ = lean_ctor_get(v_____do__lift_439_, 0);
        lean_inc(v_val_443_);
        lean_dec_ref_known(v_____do__lift_439_, 1);
        v___x_444_ = lean_apply_2(v_h__2_441_, v_val_443_, lean_box(0));
        return v___x_444_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(
    mut v_00_u03b2_445_: *mut LeanObject,
    mut v_00_u03b3_446_: *mut LeanObject,
    mut v_n_447_: *mut LeanObject,
    mut v_f_448_: *mut LeanObject,
    mut v_out_449_: *mut LeanObject,
    mut v_motive_450_: *mut LeanObject,
    mut v_____do__lift_451_: *mut LeanObject,
    mut v_h__1_452_: *mut LeanObject,
    mut v_h__2_453_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_451_) == 0 {
        let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_453_);
        v___x_454_ = lean_apply_1(v_h__1_452_, lean_box(0));
        return v___x_454_;
    } else {
        let mut v_val_455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_452_);
        v_val_455_ = lean_ctor_get(v_____do__lift_451_, 0);
        lean_inc(v_val_455_);
        lean_dec_ref_known(v_____do__lift_451_, 1);
        v___x_456_ = lean_apply_2(v_h__2_453_, v_val_455_, lean_box(0));
        return v___x_456_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___boxed(
    mut v_00_u03b2_457_: *mut LeanObject,
    mut v_00_u03b3_458_: *mut LeanObject,
    mut v_n_459_: *mut LeanObject,
    mut v_f_460_: *mut LeanObject,
    mut v_out_461_: *mut LeanObject,
    mut v_motive_462_: *mut LeanObject,
    mut v_____do__lift_463_: *mut LeanObject,
    mut v_h__1_464_: *mut LeanObject,
    mut v_h__2_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_466_: *mut LeanObject = core::ptr::null_mut();
    v_res_466_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(v_00_u03b2_457_, v_00_u03b3_458_, v_n_459_, v_f_460_, v_out_461_, v_motive_462_, v_____do__lift_463_, v_h__1_464_, v_h__2_465_);
    lean_dec(v_out_461_);
    lean_dec(v_f_460_);
    return v_res_466_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_467_: *mut LeanObject,
    mut v_h__1_468_: *mut LeanObject,
    mut v_h__2_469_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_467_) == 0 {
        let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_469_);
        v___x_470_ = lean_apply_1(v_h__1_468_, lean_box(0));
        return v___x_470_;
    } else {
        let mut v_val_471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_468_);
        v_val_471_ = lean_ctor_get(v_____do__lift_467_, 0);
        lean_inc(v_val_471_);
        lean_dec_ref_known(v_____do__lift_467_, 1);
        v___x_472_ = lean_apply_2(v_h__2_469_, v_val_471_, lean_box(0));
        return v___x_472_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_473_: *mut LeanObject,
    mut v_00_u03b2_x27_474_: *mut LeanObject,
    mut v_n_475_: *mut LeanObject,
    mut v_f_476_: *mut LeanObject,
    mut v_out_477_: *mut LeanObject,
    mut v_motive_478_: *mut LeanObject,
    mut v_____do__lift_479_: *mut LeanObject,
    mut v_h__1_480_: *mut LeanObject,
    mut v_h__2_481_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_479_) == 0 {
        let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_481_);
        v___x_482_ = lean_apply_1(v_h__1_480_, lean_box(0));
        return v___x_482_;
    } else {
        let mut v_val_483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_480_);
        v_val_483_ = lean_ctor_get(v_____do__lift_479_, 0);
        lean_inc(v_val_483_);
        lean_dec_ref_known(v_____do__lift_479_, 1);
        v___x_484_ = lean_apply_2(v_h__2_481_, v_val_483_, lean_box(0));
        return v___x_484_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_485_: *mut LeanObject,
    mut v_00_u03b2_x27_486_: *mut LeanObject,
    mut v_n_487_: *mut LeanObject,
    mut v_f_488_: *mut LeanObject,
    mut v_out_489_: *mut LeanObject,
    mut v_motive_490_: *mut LeanObject,
    mut v_____do__lift_491_: *mut LeanObject,
    mut v_h__1_492_: *mut LeanObject,
    mut v_h__2_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_494_: *mut LeanObject = core::ptr::null_mut();
    v_res_494_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_485_, v_00_u03b2_x27_486_, v_n_487_, v_f_488_, v_out_489_, v_motive_490_, v_____do__lift_491_, v_h__1_492_, v_h__2_493_);
    lean_dec(v_out_489_);
    lean_dec(v_f_488_);
    return v_res_494_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_495_: u8,
    mut v_h__1_496_: *mut LeanObject,
    mut v_h__2_497_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_495_ == 0 {
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_497_);
        v___x_498_ = lean_apply_1(v_h__1_496_, lean_box(0));
        return v___x_498_;
    } else {
        let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_496_);
        v___x_499_ = lean_apply_1(v_h__2_497_, lean_box(0));
        return v___x_499_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_500_: *mut LeanObject,
    mut v_h__1_501_: *mut LeanObject,
    mut v_h__2_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_72__boxed_503_: u8 = 0;
    let mut v_res_504_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_503_ = (lean_unbox(v_____do__lift_500_) as u8);
    v_res_504_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_503_, v_h__1_501_, v_h__2_502_);
    return v_res_504_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_505_: *mut LeanObject,
    mut v_n_506_: *mut LeanObject,
    mut v_f_507_: *mut LeanObject,
    mut v_out_508_: *mut LeanObject,
    mut v_motive_509_: *mut LeanObject,
    mut v_____do__lift_510_: u8,
    mut v_h__1_511_: *mut LeanObject,
    mut v_h__2_512_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_510_ == 0 {
        let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_512_);
        v___x_513_ = lean_apply_1(v_h__1_511_, lean_box(0));
        return v___x_513_;
    } else {
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_511_);
        v___x_514_ = lean_apply_1(v_h__2_512_, lean_box(0));
        return v___x_514_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_515_: *mut LeanObject,
    mut v_n_516_: *mut LeanObject,
    mut v_f_517_: *mut LeanObject,
    mut v_out_518_: *mut LeanObject,
    mut v_motive_519_: *mut LeanObject,
    mut v_____do__lift_520_: *mut LeanObject,
    mut v_h__1_521_: *mut LeanObject,
    mut v_h__2_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_79__boxed_523_: u8 = 0;
    let mut v_res_524_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_523_ = (lean_unbox(v_____do__lift_520_) as u8);
    v_res_524_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_515_, v_n_516_, v_f_517_, v_out_518_, v_motive_519_, v_____do__lift_79__boxed_523_, v_h__1_521_, v_h__2_522_);
    lean_dec(v_out_518_);
    lean_dec(v_f_517_);
    return v_res_524_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_525_: u8,
    mut v_h__1_526_: *mut LeanObject,
    mut v_h__2_527_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_525_ == 0 {
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_527_);
        v___x_528_ = lean_apply_1(v_h__1_526_, lean_box(0));
        return v___x_528_;
    } else {
        let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_526_);
        v___x_529_ = lean_apply_1(v_h__2_527_, lean_box(0));
        return v___x_529_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_530_: *mut LeanObject,
    mut v_h__1_531_: *mut LeanObject,
    mut v_h__2_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_74__boxed_533_: u8 = 0;
    let mut v_res_534_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_533_ = (lean_unbox(v_____do__lift_530_) as u8);
    v_res_534_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_533_, v_h__1_531_, v_h__2_532_);
    return v_res_534_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(
    mut v_00_u03b2_535_: *mut LeanObject,
    mut v_n_536_: *mut LeanObject,
    mut v_f_537_: *mut LeanObject,
    mut v_inst_538_: *mut LeanObject,
    mut v_out_539_: *mut LeanObject,
    mut v_motive_540_: *mut LeanObject,
    mut v_____do__lift_541_: u8,
    mut v_h__1_542_: *mut LeanObject,
    mut v_h__2_543_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_541_ == 0 {
        let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_543_);
        v___x_544_ = lean_apply_1(v_h__1_542_, lean_box(0));
        return v___x_544_;
    } else {
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_542_);
        v___x_545_ = lean_apply_1(v_h__2_543_, lean_box(0));
        return v___x_545_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_546_: *mut LeanObject,
    mut v_n_547_: *mut LeanObject,
    mut v_f_548_: *mut LeanObject,
    mut v_inst_549_: *mut LeanObject,
    mut v_out_550_: *mut LeanObject,
    mut v_motive_551_: *mut LeanObject,
    mut v_____do__lift_552_: *mut LeanObject,
    mut v_h__1_553_: *mut LeanObject,
    mut v_h__2_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_82__boxed_555_: u8 = 0;
    let mut v_res_556_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_555_ = (lean_unbox(v_____do__lift_552_) as u8);
    v_res_556_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_546_, v_n_547_, v_f_548_, v_inst_549_, v_out_550_, v_motive_551_, v_____do__lift_82__boxed_555_, v_h__1_553_, v_h__2_554_);
    lean_dec(v_out_550_);
    lean_dec(v_inst_549_);
    lean_dec(v_f_548_);
    return v_res_556_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_557_: *mut LeanObject,
    mut v_h__1_558_: *mut LeanObject,
    mut v_h__2_559_: *mut LeanObject,
    mut v_h__3_560_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_557_) {
        0 => {
            let mut v_it_561_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_560_);
            lean_dec(v_h__2_559_);
            v_it_561_ = lean_ctor_get(v_x_557_, 0);
            lean_inc(v_it_561_);
            v_out_562_ = lean_ctor_get(v_x_557_, 1);
            lean_inc(v_out_562_);
            lean_dec_ref_known(v_x_557_, 2);
            v___x_563_ = lean_apply_3(v_h__1_558_, v_it_561_, v_out_562_, lean_box(0));
            return v___x_563_;
        }
        1 => {
            let mut v_it_564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_560_);
            lean_dec(v_h__1_558_);
            v_it_564_ = lean_ctor_get(v_x_557_, 0);
            lean_inc(v_it_564_);
            lean_dec_ref_known(v_x_557_, 1);
            v___x_565_ = lean_apply_2(v_h__2_559_, v_it_564_, lean_box(0));
            return v___x_565_;
        }
        _ => {
            let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_559_);
            lean_dec(v_h__1_558_);
            v___x_566_ = lean_apply_1(v_h__3_560_, lean_box(0));
            return v___x_566_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_567_: *mut LeanObject,
    mut v_00_u03b2_568_: *mut LeanObject,
    mut v_m_569_: *mut LeanObject,
    mut v_inst_570_: *mut LeanObject,
    mut v_it_571_: *mut LeanObject,
    mut v_motive_572_: *mut LeanObject,
    mut v_x_573_: *mut LeanObject,
    mut v_h__1_574_: *mut LeanObject,
    mut v_h__2_575_: *mut LeanObject,
    mut v_h__3_576_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_573_) {
        0 => {
            let mut v_it_577_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_576_);
            lean_dec(v_h__2_575_);
            v_it_577_ = lean_ctor_get(v_x_573_, 0);
            lean_inc(v_it_577_);
            v_out_578_ = lean_ctor_get(v_x_573_, 1);
            lean_inc(v_out_578_);
            lean_dec_ref_known(v_x_573_, 2);
            v___x_579_ = lean_apply_3(v_h__1_574_, v_it_577_, v_out_578_, lean_box(0));
            return v___x_579_;
        }
        1 => {
            let mut v_it_580_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_576_);
            lean_dec(v_h__1_574_);
            v_it_580_ = lean_ctor_get(v_x_573_, 0);
            lean_inc(v_it_580_);
            lean_dec_ref_known(v_x_573_, 1);
            v___x_581_ = lean_apply_2(v_h__2_575_, v_it_580_, lean_box(0));
            return v___x_581_;
        }
        _ => {
            let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_575_);
            lean_dec(v_h__1_574_);
            v___x_582_ = lean_apply_1(v_h__3_576_, lean_box(0));
            return v___x_582_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_583_: *mut LeanObject,
    mut v_00_u03b2_584_: *mut LeanObject,
    mut v_m_585_: *mut LeanObject,
    mut v_inst_586_: *mut LeanObject,
    mut v_it_587_: *mut LeanObject,
    mut v_motive_588_: *mut LeanObject,
    mut v_x_589_: *mut LeanObject,
    mut v_h__1_590_: *mut LeanObject,
    mut v_h__2_591_: *mut LeanObject,
    mut v_h__3_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_593_: *mut LeanObject = core::ptr::null_mut();
    v_res_593_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_583_, v_00_u03b2_584_, v_m_585_, v_inst_586_, v_it_587_, v_motive_588_, v_x_589_, v_h__1_590_, v_h__2_591_, v_h__3_592_);
    lean_dec(v_it_587_);
    lean_dec(v_inst_586_);
    return v_res_593_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(
    mut v_x_594_: *mut LeanObject,
    mut v_h__1_595_: *mut LeanObject,
    mut v_h__2_596_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_594_) == 0 {
        let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_596_);
        v___x_597_ = lean_apply_1(v_h__1_595_, lean_box(0));
        return v___x_597_;
    } else {
        let mut v_val_598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_595_);
        v_val_598_ = lean_ctor_get(v_x_594_, 0);
        lean_inc(v_val_598_);
        lean_dec_ref_known(v_x_594_, 1);
        v___x_599_ = lean_apply_2(v_h__2_596_, v_val_598_, lean_box(0));
        return v___x_599_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(
    mut v_00_u03b2_x27_600_: *mut LeanObject,
    mut v_motive_601_: *mut LeanObject,
    mut v_x_602_: *mut LeanObject,
    mut v_h__1_603_: *mut LeanObject,
    mut v_h__2_604_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_602_) == 0 {
        let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_604_);
        v___x_605_ = lean_apply_1(v_h__1_603_, lean_box(0));
        return v___x_605_;
    } else {
        let mut v_val_606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_603_);
        v_val_606_ = lean_ctor_get(v_x_602_, 0);
        lean_inc(v_val_606_);
        lean_dec_ref_known(v_x_602_, 1);
        v___x_607_ = lean_apply_2(v_h__2_604_, v_val_606_, lean_box(0));
        return v___x_607_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_608_: *mut LeanObject,
    mut v_h__1_609_: *mut LeanObject,
    mut v_h__2_610_: *mut LeanObject,
    mut v_h__3_611_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_608_) {
        0 => {
            let mut v_it_612_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_613_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_611_);
            lean_dec(v_h__2_610_);
            v_it_612_ = lean_ctor_get(v_x_608_, 0);
            lean_inc(v_it_612_);
            v_out_613_ = lean_ctor_get(v_x_608_, 1);
            lean_inc(v_out_613_);
            lean_dec_ref_known(v_x_608_, 2);
            v___x_614_ = lean_apply_2(v_h__1_609_, v_it_612_, v_out_613_);
            return v___x_614_;
        }
        1 => {
            let mut v_it_615_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_611_);
            lean_dec(v_h__1_609_);
            v_it_615_ = lean_ctor_get(v_x_608_, 0);
            lean_inc(v_it_615_);
            lean_dec_ref_known(v_x_608_, 1);
            v___x_616_ = lean_apply_1(v_h__2_610_, v_it_615_);
            return v___x_616_;
        }
        _ => {
            let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_610_);
            lean_dec(v_h__1_609_);
            v___x_617_ = lean_box(0);
            v___x_618_ = lean_apply_1(v_h__3_611_, v___x_617_);
            return v___x_618_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_619_: *mut LeanObject,
    mut v_00_u03b2_620_: *mut LeanObject,
    mut v_m_621_: *mut LeanObject,
    mut v_motive_622_: *mut LeanObject,
    mut v_x_623_: *mut LeanObject,
    mut v_h__1_624_: *mut LeanObject,
    mut v_h__2_625_: *mut LeanObject,
    mut v_h__3_626_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_623_) {
        0 => {
            let mut v_it_627_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_628_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_626_);
            lean_dec(v_h__2_625_);
            v_it_627_ = lean_ctor_get(v_x_623_, 0);
            lean_inc(v_it_627_);
            v_out_628_ = lean_ctor_get(v_x_623_, 1);
            lean_inc(v_out_628_);
            lean_dec_ref_known(v_x_623_, 2);
            v___x_629_ = lean_apply_2(v_h__1_624_, v_it_627_, v_out_628_);
            return v___x_629_;
        }
        1 => {
            let mut v_it_630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_626_);
            lean_dec(v_h__1_624_);
            v_it_630_ = lean_ctor_get(v_x_623_, 0);
            lean_inc(v_it_630_);
            lean_dec_ref_known(v_x_623_, 1);
            v___x_631_ = lean_apply_1(v_h__2_625_, v_it_630_);
            return v___x_631_;
        }
        _ => {
            let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_625_);
            lean_dec(v_h__1_624_);
            v___x_632_ = lean_box(0);
            v___x_633_ = lean_apply_1(v_h__3_626_, v___x_632_);
            return v___x_633_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_634_: *mut LeanObject,
    mut v_h__1_635_: *mut LeanObject,
    mut v_h__2_636_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_634_) == 0 {
        let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_636_);
        v___x_637_ = lean_box(0);
        v___x_638_ = lean_apply_1(v_h__1_635_, v___x_637_);
        return v___x_638_;
    } else {
        let mut v_val_639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_635_);
        v_val_639_ = lean_ctor_get(v_x_634_, 0);
        lean_inc(v_val_639_);
        lean_dec_ref_known(v_x_634_, 1);
        v___x_640_ = lean_apply_1(v_h__2_636_, v_val_639_);
        return v___x_640_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_641_: *mut LeanObject,
    mut v_motive_642_: *mut LeanObject,
    mut v_x_643_: *mut LeanObject,
    mut v_h__1_644_: *mut LeanObject,
    mut v_h__2_645_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_643_) == 0 {
        let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_645_);
        v___x_646_ = lean_box(0);
        v___x_647_ = lean_apply_1(v_h__1_644_, v___x_646_);
        return v___x_647_;
    } else {
        let mut v_val_648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_644_);
        v_val_648_ = lean_ctor_get(v_x_643_, 0);
        lean_inc(v_val_648_);
        lean_dec_ref_known(v_x_643_, 1);
        v___x_649_ = lean_apply_1(v_h__2_645_, v_val_648_);
        return v___x_649_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27___redArg(
    mut v_t_650_: *mut LeanObject,
    mut v_mk_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = lean_apply_2(v_mk_651_, v_t_650_, lean_box(0));
    return v___x_652_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27(
    mut v_00_u03b1_653_: *mut LeanObject,
    mut v_p_654_: *mut LeanObject,
    mut v_motive_655_: *mut LeanObject,
    mut v_t_656_: *mut LeanObject,
    mut v_mk_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    v___x_658_ = lean_apply_2(v_mk_657_, v_t_656_, lean_box(0));
    return v___x_658_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(
    mut v_t_659_: *mut LeanObject,
    mut v_n_660_: *mut LeanObject,
    mut v_s_661_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_659_) == 0 {
        let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_s_661_);
        v___x_662_ = lean_apply_1(v_n_660_, lean_box(0));
        return v___x_662_;
    } else {
        let mut v_val_663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_n_660_);
        v_val_663_ = lean_ctor_get(v_t_659_, 0);
        lean_inc(v_val_663_);
        lean_dec_ref_known(v_t_659_, 1);
        v___x_664_ = lean_apply_2(v_s_661_, v_val_663_, lean_box(0));
        return v___x_664_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27(
    mut v_00_u03b1_665_: *mut LeanObject,
    mut v_t_666_: *mut LeanObject,
    mut v_00_u03b2_667_: *mut LeanObject,
    mut v_n_668_: *mut LeanObject,
    mut v_s_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_670_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(v_t_666_, v_n_668_, v_s_669_);
    return v___x_670_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(
    mut v_t_671_: *mut LeanObject,
    mut v_n_672_: *mut LeanObject,
    mut v_s_673_: *mut LeanObject,
    mut v_h__1_674_: *mut LeanObject,
    mut v_h__2_675_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_671_) == 0 {
        let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_674_);
        v___x_676_ = lean_apply_2(v_h__2_675_, v_n_672_, v_s_673_);
        return v___x_676_;
    } else {
        let mut v_val_677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_675_);
        v_val_677_ = lean_ctor_get(v_t_671_, 0);
        lean_inc(v_val_677_);
        lean_dec_ref_known(v_t_671_, 1);
        v___x_678_ = lean_apply_3(v_h__1_674_, v_val_677_, v_n_672_, v_s_673_);
        return v___x_678_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter(
    mut v_00_u03b1_679_: *mut LeanObject,
    mut v_00_u03b2_680_: *mut LeanObject,
    mut v_motive_681_: *mut LeanObject,
    mut v_t_682_: *mut LeanObject,
    mut v_n_683_: *mut LeanObject,
    mut v_s_684_: *mut LeanObject,
    mut v_h__1_685_: *mut LeanObject,
    mut v_h__2_686_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_682_) == 0 {
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_685_);
        v___x_687_ = lean_apply_2(v_h__2_686_, v_n_683_, v_s_684_);
        return v___x_687_;
    } else {
        let mut v_val_688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_686_);
        v_val_688_ = lean_ctor_get(v_t_682_, 0);
        lean_inc(v_val_688_);
        lean_dec_ref_known(v_t_682_, 1);
        v___x_689_ = lean_apply_3(v_h__1_685_, v_val_688_, v_n_683_, v_s_684_);
        return v___x_689_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_690_: *mut LeanObject,
    mut v_h__1_691_: *mut LeanObject,
    mut v_h__2_692_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_690_) == 0 {
        let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_692_);
        v___x_693_ = lean_apply_1(v_h__1_691_, lean_box(0));
        return v___x_693_;
    } else {
        let mut v_val_694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_691_);
        v_val_694_ = lean_ctor_get(v_____do__lift_690_, 0);
        lean_inc(v_val_694_);
        lean_dec_ref_known(v_____do__lift_690_, 1);
        v___x_695_ = lean_apply_2(v_h__2_692_, v_val_694_, lean_box(0));
        return v___x_695_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_696_: *mut LeanObject,
    mut v_00_u03b2_x27_697_: *mut LeanObject,
    mut v_n_698_: *mut LeanObject,
    mut v_f_699_: *mut LeanObject,
    mut v_inst_700_: *mut LeanObject,
    mut v_out_701_: *mut LeanObject,
    mut v_motive_702_: *mut LeanObject,
    mut v_____do__lift_703_: *mut LeanObject,
    mut v_h__1_704_: *mut LeanObject,
    mut v_h__2_705_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_703_) == 0 {
        let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_705_);
        v___x_706_ = lean_apply_1(v_h__1_704_, lean_box(0));
        return v___x_706_;
    } else {
        let mut v_val_707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_704_);
        v_val_707_ = lean_ctor_get(v_____do__lift_703_, 0);
        lean_inc(v_val_707_);
        lean_dec_ref_known(v_____do__lift_703_, 1);
        v___x_708_ = lean_apply_2(v_h__2_705_, v_val_707_, lean_box(0));
        return v___x_708_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_709_: *mut LeanObject,
    mut v_00_u03b2_x27_710_: *mut LeanObject,
    mut v_n_711_: *mut LeanObject,
    mut v_f_712_: *mut LeanObject,
    mut v_inst_713_: *mut LeanObject,
    mut v_out_714_: *mut LeanObject,
    mut v_motive_715_: *mut LeanObject,
    mut v_____do__lift_716_: *mut LeanObject,
    mut v_h__1_717_: *mut LeanObject,
    mut v_h__2_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_719_: *mut LeanObject = core::ptr::null_mut();
    v_res_719_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_709_, v_00_u03b2_x27_710_, v_n_711_, v_f_712_, v_inst_713_, v_out_714_, v_motive_715_, v_____do__lift_716_, v_h__1_717_, v_h__2_718_);
    lean_dec(v_out_714_);
    lean_dec(v_inst_713_);
    lean_dec(v_f_712_);
    return v_res_719_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(
    mut v_____do__lift_720_: *mut LeanObject,
    mut v_h__1_721_: *mut LeanObject,
    mut v_h__2_722_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_720_) == 0 {
        let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_722_);
        v___x_723_ = lean_box(0);
        v___x_724_ = lean_apply_1(v_h__1_721_, v___x_723_);
        return v___x_724_;
    } else {
        let mut v_val_725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_721_);
        v_val_725_ = lean_ctor_get(v_____do__lift_720_, 0);
        lean_inc(v_val_725_);
        lean_dec_ref_known(v_____do__lift_720_, 1);
        v___x_726_ = lean_apply_1(v_h__2_722_, v_val_725_);
        return v___x_726_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter(
    mut v_00_u03b3_727_: *mut LeanObject,
    mut v_motive_728_: *mut LeanObject,
    mut v_____do__lift_729_: *mut LeanObject,
    mut v_h__1_730_: *mut LeanObject,
    mut v_h__2_731_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_729_) == 0 {
        let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_731_);
        v___x_732_ = lean_box(0);
        v___x_733_ = lean_apply_1(v_h__1_730_, v___x_732_);
        return v___x_733_;
    } else {
        let mut v_val_734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_730_);
        v_val_734_ = lean_ctor_get(v_____do__lift_729_, 0);
        lean_inc(v_val_734_);
        lean_dec_ref_known(v_____do__lift_729_, 1);
        v___x_735_ = lean_apply_1(v_h__2_731_, v_val_734_);
        return v___x_735_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_736_: *mut LeanObject,
    mut v_h__1_737_: *mut LeanObject,
    mut v_h__2_738_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_736_) == 0 {
        let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_738_);
        v___x_739_ = lean_box(0);
        v___x_740_ = lean_apply_1(v_h__1_737_, v___x_739_);
        return v___x_740_;
    } else {
        let mut v_val_741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_737_);
        v_val_741_ = lean_ctor_get(v_____do__lift_736_, 0);
        lean_inc(v_val_741_);
        lean_dec_ref_known(v_____do__lift_736_, 1);
        v___x_742_ = lean_apply_1(v_h__2_738_, v_val_741_);
        return v___x_742_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_743_: *mut LeanObject,
    mut v_motive_744_: *mut LeanObject,
    mut v_____do__lift_745_: *mut LeanObject,
    mut v_h__1_746_: *mut LeanObject,
    mut v_h__2_747_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_745_) == 0 {
        let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_747_);
        v___x_748_ = lean_box(0);
        v___x_749_ = lean_apply_1(v_h__1_746_, v___x_748_);
        return v___x_749_;
    } else {
        let mut v_val_750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_746_);
        v_val_750_ = lean_ctor_get(v_____do__lift_745_, 0);
        lean_inc(v_val_750_);
        lean_dec_ref_known(v_____do__lift_745_, 1);
        v___x_751_ = lean_apply_1(v_h__2_747_, v_val_750_);
        return v___x_751_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(
    mut v_____do__lift_752_: *mut LeanObject,
    mut v_h__1_753_: *mut LeanObject,
    mut v_h__2_754_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_752_) == 0 {
        let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_754_);
        v___x_755_ = lean_box(0);
        v___x_756_ = lean_apply_1(v_h__1_753_, v___x_755_);
        return v___x_756_;
    } else {
        let mut v_val_757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_753_);
        v_val_757_ = lean_ctor_get(v_____do__lift_752_, 0);
        lean_inc(v_val_757_);
        lean_dec_ref_known(v_____do__lift_752_, 1);
        v___x_758_ = lean_apply_1(v_h__2_754_, v_val_757_);
        return v___x_758_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter(
    mut v_00_u03b2_759_: *mut LeanObject,
    mut v_motive_760_: *mut LeanObject,
    mut v_____do__lift_761_: *mut LeanObject,
    mut v_h__1_762_: *mut LeanObject,
    mut v_h__2_763_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_761_) == 0 {
        let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_763_);
        v___x_764_ = lean_box(0);
        v___x_765_ = lean_apply_1(v_h__1_762_, v___x_764_);
        return v___x_765_;
    } else {
        let mut v_val_766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_762_);
        v_val_766_ = lean_ctor_get(v_____do__lift_761_, 0);
        lean_inc(v_val_766_);
        lean_dec_ref_known(v_____do__lift_761_, 1);
        v___x_767_ = lean_apply_1(v_h__2_763_, v_val_766_);
        return v___x_767_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_768_: *mut LeanObject,
    mut v_h__1_769_: *mut LeanObject,
    mut v_h__2_770_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_768_) == 0 {
        let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_769_);
        v___x_771_ = lean_box(0);
        v___x_772_ = lean_apply_1(v_h__2_770_, v___x_771_);
        return v___x_772_;
    } else {
        let mut v_val_773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_770_);
        v_val_773_ = lean_ctor_get(v_____do__lift_768_, 0);
        lean_inc(v_val_773_);
        lean_dec_ref_known(v_____do__lift_768_, 1);
        v___x_774_ = lean_apply_1(v_h__1_769_, v_val_773_);
        return v___x_774_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_775_: *mut LeanObject,
    mut v_motive_776_: *mut LeanObject,
    mut v_____do__lift_777_: *mut LeanObject,
    mut v_h__1_778_: *mut LeanObject,
    mut v_h__2_779_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_777_) == 0 {
        let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_778_);
        v___x_780_ = lean_box(0);
        v___x_781_ = lean_apply_1(v_h__2_779_, v___x_780_);
        return v___x_781_;
    } else {
        let mut v_val_782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_779_);
        v_val_782_ = lean_ctor_get(v_____do__lift_777_, 0);
        lean_inc(v_val_782_);
        lean_dec_ref_known(v_____do__lift_777_, 1);
        v___x_783_ = lean_apply_1(v_h__1_778_, v_val_782_);
        return v___x_783_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_784_: *mut LeanObject,
    mut v_h__1_785_: *mut LeanObject,
    mut v_h__2_786_: *mut LeanObject,
    mut v_h__3_787_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_784_) {
        0 => {
            let mut v_it_788_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_787_);
            lean_dec(v_h__2_786_);
            v_it_788_ = lean_ctor_get(v_x_784_, 0);
            lean_inc(v_it_788_);
            v_out_789_ = lean_ctor_get(v_x_784_, 1);
            lean_inc(v_out_789_);
            lean_dec_ref_known(v_x_784_, 2);
            v___x_790_ = lean_apply_3(v_h__1_785_, v_it_788_, v_out_789_, lean_box(0));
            return v___x_790_;
        }
        1 => {
            let mut v_it_791_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_787_);
            lean_dec(v_h__1_785_);
            v_it_791_ = lean_ctor_get(v_x_784_, 0);
            lean_inc(v_it_791_);
            lean_dec_ref_known(v_x_784_, 1);
            v___x_792_ = lean_apply_2(v_h__2_786_, v_it_791_, lean_box(0));
            return v___x_792_;
        }
        _ => {
            let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_786_);
            lean_dec(v_h__1_785_);
            v___x_793_ = lean_apply_1(v_h__3_787_, lean_box(0));
            return v___x_793_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_794_: *mut LeanObject,
    mut v_00_u03b2_795_: *mut LeanObject,
    mut v_m_796_: *mut LeanObject,
    mut v_inst_797_: *mut LeanObject,
    mut v_it_798_: *mut LeanObject,
    mut v_motive_799_: *mut LeanObject,
    mut v_x_800_: *mut LeanObject,
    mut v_h__1_801_: *mut LeanObject,
    mut v_h__2_802_: *mut LeanObject,
    mut v_h__3_803_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_800_) {
        0 => {
            let mut v_it_804_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_805_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_803_);
            lean_dec(v_h__2_802_);
            v_it_804_ = lean_ctor_get(v_x_800_, 0);
            lean_inc(v_it_804_);
            v_out_805_ = lean_ctor_get(v_x_800_, 1);
            lean_inc(v_out_805_);
            lean_dec_ref_known(v_x_800_, 2);
            v___x_806_ = lean_apply_3(v_h__1_801_, v_it_804_, v_out_805_, lean_box(0));
            return v___x_806_;
        }
        1 => {
            let mut v_it_807_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_803_);
            lean_dec(v_h__1_801_);
            v_it_807_ = lean_ctor_get(v_x_800_, 0);
            lean_inc(v_it_807_);
            lean_dec_ref_known(v_x_800_, 1);
            v___x_808_ = lean_apply_2(v_h__2_802_, v_it_807_, lean_box(0));
            return v___x_808_;
        }
        _ => {
            let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_802_);
            lean_dec(v_h__1_801_);
            v___x_809_ = lean_apply_1(v_h__3_803_, lean_box(0));
            return v___x_809_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_810_: *mut LeanObject,
    mut v_00_u03b2_811_: *mut LeanObject,
    mut v_m_812_: *mut LeanObject,
    mut v_inst_813_: *mut LeanObject,
    mut v_it_814_: *mut LeanObject,
    mut v_motive_815_: *mut LeanObject,
    mut v_x_816_: *mut LeanObject,
    mut v_h__1_817_: *mut LeanObject,
    mut v_h__2_818_: *mut LeanObject,
    mut v_h__3_819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_820_: *mut LeanObject = core::ptr::null_mut();
    v_res_820_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_810_, v_00_u03b2_811_, v_m_812_, v_inst_813_, v_it_814_, v_motive_815_, v_x_816_, v_h__1_817_, v_h__2_818_, v_h__3_819_);
    lean_dec(v_it_814_);
    lean_dec(v_inst_813_);
    return v_res_820_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_821_: *mut LeanObject,
    mut v_h__1_822_: *mut LeanObject,
    mut v_h__2_823_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_821_) == 0 {
        let mut v_a_824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_822_);
        v_a_824_ = lean_ctor_get(v_____do__lift_821_, 0);
        lean_inc(v_a_824_);
        lean_dec_ref_known(v_____do__lift_821_, 1);
        v___x_825_ = lean_apply_1(v_h__2_823_, v_a_824_);
        return v___x_825_;
    } else {
        let mut v_a_826_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_823_);
        v_a_826_ = lean_ctor_get(v_____do__lift_821_, 0);
        lean_inc(v_a_826_);
        lean_dec_ref_known(v_____do__lift_821_, 1);
        v___x_827_ = lean_apply_1(v_h__1_822_, v_a_826_);
        return v___x_827_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_828_: *mut LeanObject,
    mut v_motive_829_: *mut LeanObject,
    mut v_____do__lift_830_: *mut LeanObject,
    mut v_h__1_831_: *mut LeanObject,
    mut v_h__2_832_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_830_) == 0 {
        let mut v_a_833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_831_);
        v_a_833_ = lean_ctor_get(v_____do__lift_830_, 0);
        lean_inc(v_a_833_);
        lean_dec_ref_known(v_____do__lift_830_, 1);
        v___x_834_ = lean_apply_1(v_h__2_832_, v_a_833_);
        return v___x_834_;
    } else {
        let mut v_a_835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_832_);
        v_a_835_ = lean_ctor_get(v_____do__lift_830_, 0);
        lean_inc(v_a_835_);
        lean_dec_ref_known(v_____do__lift_830_, 1);
        v___x_836_ = lean_apply_1(v_h__1_831_, v_a_835_);
        return v___x_836_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_837_: *mut LeanObject,
    mut v_h__1_838_: *mut LeanObject,
    mut v_h__2_839_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_837_) == 1 {
        let mut v_val_840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_839_);
        v_val_840_ = lean_ctor_get(v_____x_837_, 0);
        lean_inc(v_val_840_);
        lean_dec_ref_known(v_____x_837_, 1);
        v___x_841_ = lean_apply_1(v_h__1_838_, v_val_840_);
        return v___x_841_;
    } else {
        let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_838_);
        v___x_842_ = lean_apply_2(v_h__2_839_, v_____x_837_, lean_box(0));
        return v___x_842_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_843_: *mut LeanObject,
    mut v_motive_844_: *mut LeanObject,
    mut v_____x_845_: *mut LeanObject,
    mut v_h__1_846_: *mut LeanObject,
    mut v_h__2_847_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_845_) == 1 {
        let mut v_val_848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_847_);
        v_val_848_ = lean_ctor_get(v_____x_845_, 0);
        lean_inc(v_val_848_);
        lean_dec_ref_known(v_____x_845_, 1);
        v___x_849_ = lean_apply_1(v_h__1_846_, v_val_848_);
        return v___x_849_;
    } else {
        let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_846_);
        v___x_850_ = lean_apply_2(v_h__2_847_, v_____x_845_, lean_box(0));
        return v___x_850_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_851_: *mut LeanObject,
    mut v_h__1_852_: *mut LeanObject,
    mut v_h__2_853_: *mut LeanObject,
    mut v_h__3_854_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_851_) {
        0 => {
            let mut v_it_855_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_854_);
            lean_dec(v_h__2_853_);
            v_it_855_ = lean_ctor_get(v_x_851_, 0);
            lean_inc(v_it_855_);
            v_out_856_ = lean_ctor_get(v_x_851_, 1);
            lean_inc(v_out_856_);
            lean_dec_ref_known(v_x_851_, 2);
            v___x_857_ = lean_apply_2(v_h__1_852_, v_it_855_, v_out_856_);
            return v___x_857_;
        }
        1 => {
            let mut v_it_858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_854_);
            lean_dec(v_h__1_852_);
            v_it_858_ = lean_ctor_get(v_x_851_, 0);
            lean_inc(v_it_858_);
            lean_dec_ref_known(v_x_851_, 1);
            v___x_859_ = lean_apply_1(v_h__2_853_, v_it_858_);
            return v___x_859_;
        }
        _ => {
            let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_853_);
            lean_dec(v_h__1_852_);
            v___x_860_ = lean_box(0);
            v___x_861_ = lean_apply_1(v_h__3_854_, v___x_860_);
            return v___x_861_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_862_: *mut LeanObject,
    mut v_00_u03b2_863_: *mut LeanObject,
    mut v_m_864_: *mut LeanObject,
    mut v_motive_865_: *mut LeanObject,
    mut v_x_866_: *mut LeanObject,
    mut v_h__1_867_: *mut LeanObject,
    mut v_h__2_868_: *mut LeanObject,
    mut v_h__3_869_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_866_) {
        0 => {
            let mut v_it_870_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_871_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_869_);
            lean_dec(v_h__2_868_);
            v_it_870_ = lean_ctor_get(v_x_866_, 0);
            lean_inc(v_it_870_);
            v_out_871_ = lean_ctor_get(v_x_866_, 1);
            lean_inc(v_out_871_);
            lean_dec_ref_known(v_x_866_, 2);
            v___x_872_ = lean_apply_2(v_h__1_867_, v_it_870_, v_out_871_);
            return v___x_872_;
        }
        1 => {
            let mut v_it_873_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_869_);
            lean_dec(v_h__1_867_);
            v_it_873_ = lean_ctor_get(v_x_866_, 0);
            lean_inc(v_it_873_);
            lean_dec_ref_known(v_x_866_, 1);
            v___x_874_ = lean_apply_1(v_h__2_868_, v_it_873_);
            return v___x_874_;
        }
        _ => {
            let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_868_);
            lean_dec(v_h__1_867_);
            v___x_875_ = lean_box(0);
            v___x_876_ = lean_apply_1(v_h__3_869_, v___x_875_);
            return v___x_876_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}
