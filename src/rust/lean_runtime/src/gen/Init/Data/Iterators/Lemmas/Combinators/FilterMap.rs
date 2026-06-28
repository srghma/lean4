// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.FilterMap
// Imports: Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.List.Control Init.Data.Array.Lemmas Init.Data.Bool Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_536_: *mut LeanObject,
    mut v_h__1_537_: *mut LeanObject,
    mut v_h__2_538_: *mut LeanObject,
    mut v_h__3_539_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_536_) {
        0 => {
            let mut v_it_540_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_539_);
            lean_dec(v_h__2_538_);
            v_it_540_ = lean_ctor_get(v_x_536_, 0);
            lean_inc(v_it_540_);
            v_out_541_ = lean_ctor_get(v_x_536_, 1);
            lean_inc(v_out_541_);
            lean_dec_ref_known(v_x_536_, 2);
            v___x_542_ = lean_apply_3(v_h__1_537_, v_it_540_, v_out_541_, lean_box(0));
            return v___x_542_;
        }
        1 => {
            let mut v_it_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_539_);
            lean_dec(v_h__1_537_);
            v_it_543_ = lean_ctor_get(v_x_536_, 0);
            lean_inc(v_it_543_);
            lean_dec_ref_known(v_x_536_, 1);
            v___x_544_ = lean_apply_2(v_h__2_538_, v_it_543_, lean_box(0));
            return v___x_544_;
        }
        _ => {
            let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_538_);
            lean_dec(v_h__1_537_);
            v___x_545_ = lean_apply_1(v_h__3_539_, lean_box(0));
            return v___x_545_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_546_: *mut LeanObject,
    mut v_00_u03b2_547_: *mut LeanObject,
    mut v_m_548_: *mut LeanObject,
    mut v_inst_549_: *mut LeanObject,
    mut v_it_550_: *mut LeanObject,
    mut v_motive_551_: *mut LeanObject,
    mut v_x_552_: *mut LeanObject,
    mut v_h__1_553_: *mut LeanObject,
    mut v_h__2_554_: *mut LeanObject,
    mut v_h__3_555_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_552_) {
        0 => {
            let mut v_it_556_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_557_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_555_);
            lean_dec(v_h__2_554_);
            v_it_556_ = lean_ctor_get(v_x_552_, 0);
            lean_inc(v_it_556_);
            v_out_557_ = lean_ctor_get(v_x_552_, 1);
            lean_inc(v_out_557_);
            lean_dec_ref_known(v_x_552_, 2);
            v___x_558_ = lean_apply_3(v_h__1_553_, v_it_556_, v_out_557_, lean_box(0));
            return v___x_558_;
        }
        1 => {
            let mut v_it_559_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_555_);
            lean_dec(v_h__1_553_);
            v_it_559_ = lean_ctor_get(v_x_552_, 0);
            lean_inc(v_it_559_);
            lean_dec_ref_known(v_x_552_, 1);
            v___x_560_ = lean_apply_2(v_h__2_554_, v_it_559_, lean_box(0));
            return v___x_560_;
        }
        _ => {
            let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_554_);
            lean_dec(v_h__1_553_);
            v___x_561_ = lean_apply_1(v_h__3_555_, lean_box(0));
            return v___x_561_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_562_: *mut LeanObject,
    mut v_00_u03b2_563_: *mut LeanObject,
    mut v_m_564_: *mut LeanObject,
    mut v_inst_565_: *mut LeanObject,
    mut v_it_566_: *mut LeanObject,
    mut v_motive_567_: *mut LeanObject,
    mut v_x_568_: *mut LeanObject,
    mut v_h__1_569_: *mut LeanObject,
    mut v_h__2_570_: *mut LeanObject,
    mut v_h__3_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_572_: *mut LeanObject = core::ptr::null_mut();
    v_res_572_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_562_, v_00_u03b2_563_, v_m_564_, v_inst_565_, v_it_566_, v_motive_567_, v_x_568_, v_h__1_569_, v_h__2_570_, v_h__3_571_);
    lean_dec(v_it_566_);
    lean_dec(v_inst_565_);
    return v_res_572_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_573_: *mut LeanObject,
    mut v_h__1_574_: *mut LeanObject,
    mut v_h__2_575_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_573_) == 0 {
        let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_575_);
        v___x_576_ = lean_apply_1(v_h__1_574_, lean_box(0));
        return v___x_576_;
    } else {
        let mut v_val_577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_574_);
        v_val_577_ = lean_ctor_get(v_____do__lift_573_, 0);
        lean_inc(v_val_577_);
        lean_dec_ref_known(v_____do__lift_573_, 1);
        v___x_578_ = lean_apply_2(v_h__2_575_, v_val_577_, lean_box(0));
        return v___x_578_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_579_: *mut LeanObject,
    mut v_00_u03b2_x27_580_: *mut LeanObject,
    mut v_n_581_: *mut LeanObject,
    mut v_f_582_: *mut LeanObject,
    mut v_out_583_: *mut LeanObject,
    mut v_motive_584_: *mut LeanObject,
    mut v_____do__lift_585_: *mut LeanObject,
    mut v_h__1_586_: *mut LeanObject,
    mut v_h__2_587_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_585_) == 0 {
        let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_587_);
        v___x_588_ = lean_apply_1(v_h__1_586_, lean_box(0));
        return v___x_588_;
    } else {
        let mut v_val_589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_586_);
        v_val_589_ = lean_ctor_get(v_____do__lift_585_, 0);
        lean_inc(v_val_589_);
        lean_dec_ref_known(v_____do__lift_585_, 1);
        v___x_590_ = lean_apply_2(v_h__2_587_, v_val_589_, lean_box(0));
        return v___x_590_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_591_: *mut LeanObject,
    mut v_00_u03b2_x27_592_: *mut LeanObject,
    mut v_n_593_: *mut LeanObject,
    mut v_f_594_: *mut LeanObject,
    mut v_out_595_: *mut LeanObject,
    mut v_motive_596_: *mut LeanObject,
    mut v_____do__lift_597_: *mut LeanObject,
    mut v_h__1_598_: *mut LeanObject,
    mut v_h__2_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_600_: *mut LeanObject = core::ptr::null_mut();
    v_res_600_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_591_, v_00_u03b2_x27_592_, v_n_593_, v_f_594_, v_out_595_, v_motive_596_, v_____do__lift_597_, v_h__1_598_, v_h__2_599_);
    lean_dec(v_out_595_);
    lean_dec(v_f_594_);
    return v_res_600_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_601_: *mut LeanObject,
    mut v_h__1_602_: *mut LeanObject,
    mut v_h__2_603_: *mut LeanObject,
    mut v_h__3_604_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_601_) {
        0 => {
            let mut v_it_605_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_606_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_604_);
            lean_dec(v_h__2_603_);
            v_it_605_ = lean_ctor_get(v_x_601_, 0);
            lean_inc(v_it_605_);
            v_out_606_ = lean_ctor_get(v_x_601_, 1);
            lean_inc(v_out_606_);
            lean_dec_ref_known(v_x_601_, 2);
            v___x_607_ = lean_apply_3(v_h__1_602_, v_it_605_, v_out_606_, lean_box(0));
            return v___x_607_;
        }
        1 => {
            let mut v_it_608_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_604_);
            lean_dec(v_h__1_602_);
            v_it_608_ = lean_ctor_get(v_x_601_, 0);
            lean_inc(v_it_608_);
            lean_dec_ref_known(v_x_601_, 1);
            v___x_609_ = lean_apply_2(v_h__2_603_, v_it_608_, lean_box(0));
            return v___x_609_;
        }
        _ => {
            let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_603_);
            lean_dec(v_h__1_602_);
            v___x_610_ = lean_apply_1(v_h__3_604_, lean_box(0));
            return v___x_610_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_611_: *mut LeanObject,
    mut v_00_u03b2_612_: *mut LeanObject,
    mut v_inst_613_: *mut LeanObject,
    mut v_it_614_: *mut LeanObject,
    mut v_motive_615_: *mut LeanObject,
    mut v_x_616_: *mut LeanObject,
    mut v_h__1_617_: *mut LeanObject,
    mut v_h__2_618_: *mut LeanObject,
    mut v_h__3_619_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_616_) {
        0 => {
            let mut v_it_620_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_621_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_619_);
            lean_dec(v_h__2_618_);
            v_it_620_ = lean_ctor_get(v_x_616_, 0);
            lean_inc(v_it_620_);
            v_out_621_ = lean_ctor_get(v_x_616_, 1);
            lean_inc(v_out_621_);
            lean_dec_ref_known(v_x_616_, 2);
            v___x_622_ = lean_apply_3(v_h__1_617_, v_it_620_, v_out_621_, lean_box(0));
            return v___x_622_;
        }
        1 => {
            let mut v_it_623_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_619_);
            lean_dec(v_h__1_617_);
            v_it_623_ = lean_ctor_get(v_x_616_, 0);
            lean_inc(v_it_623_);
            lean_dec_ref_known(v_x_616_, 1);
            v___x_624_ = lean_apply_2(v_h__2_618_, v_it_623_, lean_box(0));
            return v___x_624_;
        }
        _ => {
            let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_618_);
            lean_dec(v_h__1_617_);
            v___x_625_ = lean_apply_1(v_h__3_619_, lean_box(0));
            return v___x_625_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_626_: *mut LeanObject,
    mut v_00_u03b2_627_: *mut LeanObject,
    mut v_inst_628_: *mut LeanObject,
    mut v_it_629_: *mut LeanObject,
    mut v_motive_630_: *mut LeanObject,
    mut v_x_631_: *mut LeanObject,
    mut v_h__1_632_: *mut LeanObject,
    mut v_h__2_633_: *mut LeanObject,
    mut v_h__3_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_635_: *mut LeanObject = core::ptr::null_mut();
    v_res_635_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_626_, v_00_u03b2_627_, v_inst_628_, v_it_629_, v_motive_630_, v_x_631_, v_h__1_632_, v_h__2_633_, v_h__3_634_);
    lean_dec(v_it_629_);
    lean_dec(v_inst_628_);
    return v_res_635_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_636_: *mut LeanObject,
    mut v_h__1_637_: *mut LeanObject,
    mut v_h__2_638_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_636_) == 0 {
        let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_638_);
        v___x_639_ = lean_apply_1(v_h__1_637_, lean_box(0));
        return v___x_639_;
    } else {
        let mut v_val_640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_637_);
        v_val_640_ = lean_ctor_get(v_____do__lift_636_, 0);
        lean_inc(v_val_640_);
        lean_dec_ref_known(v_____do__lift_636_, 1);
        v___x_641_ = lean_apply_2(v_h__2_638_, v_val_640_, lean_box(0));
        return v___x_641_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_642_: *mut LeanObject,
    mut v_00_u03b3_643_: *mut LeanObject,
    mut v_n_644_: *mut LeanObject,
    mut v_f_645_: *mut LeanObject,
    mut v_out_646_: *mut LeanObject,
    mut v_motive_647_: *mut LeanObject,
    mut v_____do__lift_648_: *mut LeanObject,
    mut v_h__1_649_: *mut LeanObject,
    mut v_h__2_650_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_648_) == 0 {
        let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_650_);
        v___x_651_ = lean_apply_1(v_h__1_649_, lean_box(0));
        return v___x_651_;
    } else {
        let mut v_val_652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_649_);
        v_val_652_ = lean_ctor_get(v_____do__lift_648_, 0);
        lean_inc(v_val_652_);
        lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_653_ = lean_apply_2(v_h__2_650_, v_val_652_, lean_box(0));
        return v___x_653_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_654_: *mut LeanObject,
    mut v_00_u03b3_655_: *mut LeanObject,
    mut v_n_656_: *mut LeanObject,
    mut v_f_657_: *mut LeanObject,
    mut v_out_658_: *mut LeanObject,
    mut v_motive_659_: *mut LeanObject,
    mut v_____do__lift_660_: *mut LeanObject,
    mut v_h__1_661_: *mut LeanObject,
    mut v_h__2_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_663_: *mut LeanObject = core::ptr::null_mut();
    v_res_663_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_654_, v_00_u03b3_655_, v_n_656_, v_f_657_, v_out_658_, v_motive_659_, v_____do__lift_660_, v_h__1_661_, v_h__2_662_);
    lean_dec(v_out_658_);
    lean_dec(v_f_657_);
    return v_res_663_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_664_: u8,
    mut v_h__1_665_: *mut LeanObject,
    mut v_h__2_666_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_664_ == 0 {
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_666_);
        v___x_667_ = lean_apply_1(v_h__1_665_, lean_box(0));
        return v___x_667_;
    } else {
        let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_665_);
        v___x_668_ = lean_apply_1(v_h__2_666_, lean_box(0));
        return v___x_668_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_669_: *mut LeanObject,
    mut v_h__1_670_: *mut LeanObject,
    mut v_h__2_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_72__boxed_672_: u8 = 0;
    let mut v_res_673_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_672_ = (lean_unbox(v_____do__lift_669_) as u8);
    v_res_673_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_672_, v_h__1_670_, v_h__2_671_);
    return v_res_673_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_674_: *mut LeanObject,
    mut v_n_675_: *mut LeanObject,
    mut v_f_676_: *mut LeanObject,
    mut v_out_677_: *mut LeanObject,
    mut v_motive_678_: *mut LeanObject,
    mut v_____do__lift_679_: u8,
    mut v_h__1_680_: *mut LeanObject,
    mut v_h__2_681_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_679_ == 0 {
        let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_681_);
        v___x_682_ = lean_apply_1(v_h__1_680_, lean_box(0));
        return v___x_682_;
    } else {
        let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_680_);
        v___x_683_ = lean_apply_1(v_h__2_681_, lean_box(0));
        return v___x_683_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_684_: *mut LeanObject,
    mut v_n_685_: *mut LeanObject,
    mut v_f_686_: *mut LeanObject,
    mut v_out_687_: *mut LeanObject,
    mut v_motive_688_: *mut LeanObject,
    mut v_____do__lift_689_: *mut LeanObject,
    mut v_h__1_690_: *mut LeanObject,
    mut v_h__2_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_79__boxed_692_: u8 = 0;
    let mut v_res_693_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_692_ = (lean_unbox(v_____do__lift_689_) as u8);
    v_res_693_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_684_, v_n_685_, v_f_686_, v_out_687_, v_motive_688_, v_____do__lift_79__boxed_692_, v_h__1_690_, v_h__2_691_);
    lean_dec(v_out_687_);
    lean_dec(v_f_686_);
    return v_res_693_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_694_: u8,
    mut v_h__1_695_: *mut LeanObject,
    mut v_h__2_696_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_694_ == 0 {
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_696_);
        v___x_697_ = lean_apply_1(v_h__1_695_, lean_box(0));
        return v___x_697_;
    } else {
        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_695_);
        v___x_698_ = lean_apply_1(v_h__2_696_, lean_box(0));
        return v___x_698_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_699_: *mut LeanObject,
    mut v_h__1_700_: *mut LeanObject,
    mut v_h__2_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_72__boxed_702_: u8 = 0;
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_702_ = (lean_unbox(v_____do__lift_699_) as u8);
    v_res_703_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_702_, v_h__1_700_, v_h__2_701_);
    return v_res_703_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_704_: *mut LeanObject,
    mut v_n_705_: *mut LeanObject,
    mut v_f_706_: *mut LeanObject,
    mut v_out_707_: *mut LeanObject,
    mut v_motive_708_: *mut LeanObject,
    mut v_____do__lift_709_: u8,
    mut v_h__1_710_: *mut LeanObject,
    mut v_h__2_711_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_709_ == 0 {
        let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_711_);
        v___x_712_ = lean_apply_1(v_h__1_710_, lean_box(0));
        return v___x_712_;
    } else {
        let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_710_);
        v___x_713_ = lean_apply_1(v_h__2_711_, lean_box(0));
        return v___x_713_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_714_: *mut LeanObject,
    mut v_n_715_: *mut LeanObject,
    mut v_f_716_: *mut LeanObject,
    mut v_out_717_: *mut LeanObject,
    mut v_motive_718_: *mut LeanObject,
    mut v_____do__lift_719_: *mut LeanObject,
    mut v_h__1_720_: *mut LeanObject,
    mut v_h__2_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_79__boxed_722_: u8 = 0;
    let mut v_res_723_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_722_ = (lean_unbox(v_____do__lift_719_) as u8);
    v_res_723_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_714_, v_n_715_, v_f_716_, v_out_717_, v_motive_718_, v_____do__lift_79__boxed_722_, v_h__1_720_, v_h__2_721_);
    lean_dec(v_out_717_);
    lean_dec(v_f_716_);
    return v_res_723_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_724_: *mut LeanObject,
    mut v_h__1_725_: *mut LeanObject,
    mut v_h__2_726_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_724_) == 0 {
        let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_726_);
        v___x_727_ = lean_apply_1(v_h__1_725_, lean_box(0));
        return v___x_727_;
    } else {
        let mut v_val_728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_725_);
        v_val_728_ = lean_ctor_get(v_____do__lift_724_, 0);
        lean_inc(v_val_728_);
        lean_dec_ref_known(v_____do__lift_724_, 1);
        v___x_729_ = lean_apply_2(v_h__2_726_, v_val_728_, lean_box(0));
        return v___x_729_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_730_: *mut LeanObject,
    mut v_00_u03b2_x27_731_: *mut LeanObject,
    mut v_n_732_: *mut LeanObject,
    mut v_f_733_: *mut LeanObject,
    mut v_inst_734_: *mut LeanObject,
    mut v_out_735_: *mut LeanObject,
    mut v_motive_736_: *mut LeanObject,
    mut v_____do__lift_737_: *mut LeanObject,
    mut v_h__1_738_: *mut LeanObject,
    mut v_h__2_739_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_737_) == 0 {
        let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_739_);
        v___x_740_ = lean_apply_1(v_h__1_738_, lean_box(0));
        return v___x_740_;
    } else {
        let mut v_val_741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_738_);
        v_val_741_ = lean_ctor_get(v_____do__lift_737_, 0);
        lean_inc(v_val_741_);
        lean_dec_ref_known(v_____do__lift_737_, 1);
        v___x_742_ = lean_apply_2(v_h__2_739_, v_val_741_, lean_box(0));
        return v___x_742_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_743_: *mut LeanObject,
    mut v_00_u03b2_x27_744_: *mut LeanObject,
    mut v_n_745_: *mut LeanObject,
    mut v_f_746_: *mut LeanObject,
    mut v_inst_747_: *mut LeanObject,
    mut v_out_748_: *mut LeanObject,
    mut v_motive_749_: *mut LeanObject,
    mut v_____do__lift_750_: *mut LeanObject,
    mut v_h__1_751_: *mut LeanObject,
    mut v_h__2_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_753_: *mut LeanObject = core::ptr::null_mut();
    v_res_753_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_743_, v_00_u03b2_x27_744_, v_n_745_, v_f_746_, v_inst_747_, v_out_748_, v_motive_749_, v_____do__lift_750_, v_h__1_751_, v_h__2_752_);
    lean_dec(v_out_748_);
    lean_dec(v_inst_747_);
    lean_dec(v_f_746_);
    return v_res_753_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_754_: *mut LeanObject,
    mut v_h__1_755_: *mut LeanObject,
    mut v_h__2_756_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_754_) == 0 {
        let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_756_);
        v___x_757_ = lean_apply_1(v_h__1_755_, lean_box(0));
        return v___x_757_;
    } else {
        let mut v_val_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_755_);
        v_val_758_ = lean_ctor_get(v_____do__lift_754_, 0);
        lean_inc(v_val_758_);
        lean_dec_ref_known(v_____do__lift_754_, 1);
        v___x_759_ = lean_apply_2(v_h__2_756_, v_val_758_, lean_box(0));
        return v___x_759_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_760_: *mut LeanObject,
    mut v_n_761_: *mut LeanObject,
    mut v_00_u03b2_x27_762_: *mut LeanObject,
    mut v_f_763_: *mut LeanObject,
    mut v_inst_764_: *mut LeanObject,
    mut v_out_765_: *mut LeanObject,
    mut v_motive_766_: *mut LeanObject,
    mut v_____do__lift_767_: *mut LeanObject,
    mut v_h__1_768_: *mut LeanObject,
    mut v_h__2_769_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_767_) == 0 {
        let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_769_);
        v___x_770_ = lean_apply_1(v_h__1_768_, lean_box(0));
        return v___x_770_;
    } else {
        let mut v_val_771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_768_);
        v_val_771_ = lean_ctor_get(v_____do__lift_767_, 0);
        lean_inc(v_val_771_);
        lean_dec_ref_known(v_____do__lift_767_, 1);
        v___x_772_ = lean_apply_2(v_h__2_769_, v_val_771_, lean_box(0));
        return v___x_772_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_773_: *mut LeanObject,
    mut v_n_774_: *mut LeanObject,
    mut v_00_u03b2_x27_775_: *mut LeanObject,
    mut v_f_776_: *mut LeanObject,
    mut v_inst_777_: *mut LeanObject,
    mut v_out_778_: *mut LeanObject,
    mut v_motive_779_: *mut LeanObject,
    mut v_____do__lift_780_: *mut LeanObject,
    mut v_h__1_781_: *mut LeanObject,
    mut v_h__2_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(v_00_u03b2_773_, v_n_774_, v_00_u03b2_x27_775_, v_f_776_, v_inst_777_, v_out_778_, v_motive_779_, v_____do__lift_780_, v_h__1_781_, v_h__2_782_);
    lean_dec(v_out_778_);
    lean_dec(v_inst_777_);
    lean_dec(v_f_776_);
    return v_res_783_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_784_: u8,
    mut v_h__1_785_: *mut LeanObject,
    mut v_h__2_786_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_784_ == 0 {
        let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_786_);
        v___x_787_ = lean_apply_1(v_h__1_785_, lean_box(0));
        return v___x_787_;
    } else {
        let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_785_);
        v___x_788_ = lean_apply_1(v_h__2_786_, lean_box(0));
        return v___x_788_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_789_: *mut LeanObject,
    mut v_h__1_790_: *mut LeanObject,
    mut v_h__2_791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_74__boxed_792_: u8 = 0;
    let mut v_res_793_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_792_ = (lean_unbox(v_____do__lift_789_) as u8);
    v_res_793_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_792_, v_h__1_790_, v_h__2_791_);
    return v_res_793_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(
    mut v_00_u03b2_794_: *mut LeanObject,
    mut v_n_795_: *mut LeanObject,
    mut v_f_796_: *mut LeanObject,
    mut v_inst_797_: *mut LeanObject,
    mut v_out_798_: *mut LeanObject,
    mut v_motive_799_: *mut LeanObject,
    mut v_____do__lift_800_: u8,
    mut v_h__1_801_: *mut LeanObject,
    mut v_h__2_802_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_800_ == 0 {
        let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_802_);
        v___x_803_ = lean_apply_1(v_h__1_801_, lean_box(0));
        return v___x_803_;
    } else {
        let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_801_);
        v___x_804_ = lean_apply_1(v_h__2_802_, lean_box(0));
        return v___x_804_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_805_: *mut LeanObject,
    mut v_n_806_: *mut LeanObject,
    mut v_f_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_out_809_: *mut LeanObject,
    mut v_motive_810_: *mut LeanObject,
    mut v_____do__lift_811_: *mut LeanObject,
    mut v_h__1_812_: *mut LeanObject,
    mut v_h__2_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_82__boxed_814_: u8 = 0;
    let mut v_res_815_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_814_ = (lean_unbox(v_____do__lift_811_) as u8);
    v_res_815_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_805_, v_n_806_, v_f_807_, v_inst_808_, v_out_809_, v_motive_810_, v_____do__lift_82__boxed_814_, v_h__1_812_, v_h__2_813_);
    lean_dec(v_out_809_);
    lean_dec(v_inst_808_);
    lean_dec(v_f_807_);
    return v_res_815_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_816_: u8,
    mut v_h__1_817_: *mut LeanObject,
    mut v_h__2_818_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_816_ == 0 {
        let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_818_);
        v___x_819_ = lean_apply_1(v_h__1_817_, lean_box(0));
        return v___x_819_;
    } else {
        let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_817_);
        v___x_820_ = lean_apply_1(v_h__2_818_, lean_box(0));
        return v___x_820_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_821_: *mut LeanObject,
    mut v_h__1_822_: *mut LeanObject,
    mut v_h__2_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_74__boxed_824_: u8 = 0;
    let mut v_res_825_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_824_ = (lean_unbox(v_____do__lift_821_) as u8);
    v_res_825_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_824_, v_h__1_822_, v_h__2_823_);
    return v_res_825_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(
    mut v_00_u03b2_826_: *mut LeanObject,
    mut v_n_827_: *mut LeanObject,
    mut v_f_828_: *mut LeanObject,
    mut v_inst_829_: *mut LeanObject,
    mut v_out_830_: *mut LeanObject,
    mut v_motive_831_: *mut LeanObject,
    mut v_____do__lift_832_: u8,
    mut v_h__1_833_: *mut LeanObject,
    mut v_h__2_834_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_832_ == 0 {
        let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_834_);
        v___x_835_ = lean_apply_1(v_h__1_833_, lean_box(0));
        return v___x_835_;
    } else {
        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_833_);
        v___x_836_ = lean_apply_1(v_h__2_834_, lean_box(0));
        return v___x_836_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_837_: *mut LeanObject,
    mut v_n_838_: *mut LeanObject,
    mut v_f_839_: *mut LeanObject,
    mut v_inst_840_: *mut LeanObject,
    mut v_out_841_: *mut LeanObject,
    mut v_motive_842_: *mut LeanObject,
    mut v_____do__lift_843_: *mut LeanObject,
    mut v_h__1_844_: *mut LeanObject,
    mut v_h__2_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_82__boxed_846_: u8 = 0;
    let mut v_res_847_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_846_ = (lean_unbox(v_____do__lift_843_) as u8);
    v_res_847_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(v_00_u03b2_837_, v_n_838_, v_f_839_, v_inst_840_, v_out_841_, v_motive_842_, v_____do__lift_82__boxed_846_, v_h__1_844_, v_h__2_845_);
    lean_dec(v_out_841_);
    lean_dec(v_inst_840_);
    lean_dec(v_f_839_);
    return v_res_847_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(
    mut v_x_848_: *mut LeanObject,
    mut v_h__1_849_: *mut LeanObject,
    mut v_h__2_850_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_848_) == 0 {
        let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_850_);
        v___x_851_ = lean_apply_1(v_h__1_849_, lean_box(0));
        return v___x_851_;
    } else {
        let mut v_val_852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_849_);
        v_val_852_ = lean_ctor_get(v_x_848_, 0);
        lean_inc(v_val_852_);
        lean_dec_ref_known(v_x_848_, 1);
        v___x_853_ = lean_apply_2(v_h__2_850_, v_val_852_, lean_box(0));
        return v___x_853_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(
    mut v_00_u03b2_x27_854_: *mut LeanObject,
    mut v_motive_855_: *mut LeanObject,
    mut v_x_856_: *mut LeanObject,
    mut v_h__1_857_: *mut LeanObject,
    mut v_h__2_858_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_856_) == 0 {
        let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_858_);
        v___x_859_ = lean_apply_1(v_h__1_857_, lean_box(0));
        return v___x_859_;
    } else {
        let mut v_val_860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_857_);
        v_val_860_ = lean_ctor_get(v_x_856_, 0);
        lean_inc(v_val_860_);
        lean_dec_ref_known(v_x_856_, 1);
        v___x_861_ = lean_apply_2(v_h__2_858_, v_val_860_, lean_box(0));
        return v___x_861_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(
    mut v_x_862_: *mut LeanObject,
    mut v_h__1_863_: *mut LeanObject,
    mut v_h__2_864_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_862_) == 0 {
        let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_864_);
        v___x_865_ = lean_apply_1(v_h__1_863_, lean_box(0));
        return v___x_865_;
    } else {
        let mut v_val_866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_863_);
        v_val_866_ = lean_ctor_get(v_x_862_, 0);
        lean_inc(v_val_866_);
        lean_dec_ref_known(v_x_862_, 1);
        v___x_867_ = lean_apply_2(v_h__2_864_, v_val_866_, lean_box(0));
        return v___x_867_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(
    mut v_00_u03b3_868_: *mut LeanObject,
    mut v_motive_869_: *mut LeanObject,
    mut v_x_870_: *mut LeanObject,
    mut v_h__1_871_: *mut LeanObject,
    mut v_h__2_872_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_870_) == 0 {
        let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_872_);
        v___x_873_ = lean_apply_1(v_h__1_871_, lean_box(0));
        return v___x_873_;
    } else {
        let mut v_val_874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_871_);
        v_val_874_ = lean_ctor_get(v_x_870_, 0);
        lean_inc(v_val_874_);
        lean_dec_ref_known(v_x_870_, 1);
        v___x_875_ = lean_apply_2(v_h__2_872_, v_val_874_, lean_box(0));
        return v___x_875_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(
    mut v_x_876_: *mut LeanObject,
    mut v_h__1_877_: *mut LeanObject,
    mut v_h__2_878_: *mut LeanObject,
    mut v_h__3_879_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_876_) {
        0 => {
            let mut v_it_880_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_881_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_879_);
            lean_dec(v_h__2_878_);
            v_it_880_ = lean_ctor_get(v_x_876_, 0);
            lean_inc(v_it_880_);
            v_out_881_ = lean_ctor_get(v_x_876_, 1);
            lean_inc(v_out_881_);
            lean_dec_ref_known(v_x_876_, 2);
            v___x_882_ = lean_apply_2(v_h__1_877_, v_it_880_, v_out_881_);
            return v___x_882_;
        }
        1 => {
            let mut v_it_883_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_879_);
            lean_dec(v_h__1_877_);
            v_it_883_ = lean_ctor_get(v_x_876_, 0);
            lean_inc(v_it_883_);
            lean_dec_ref_known(v_x_876_, 1);
            v___x_884_ = lean_apply_1(v_h__2_878_, v_it_883_);
            return v___x_884_;
        }
        _ => {
            let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_878_);
            lean_dec(v_h__1_877_);
            v___x_885_ = lean_box(0);
            v___x_886_ = lean_apply_1(v_h__3_879_, v___x_885_);
            return v___x_886_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(
    mut v_00_u03b1_887_: *mut LeanObject,
    mut v_00_u03b2_888_: *mut LeanObject,
    mut v_motive_889_: *mut LeanObject,
    mut v_x_890_: *mut LeanObject,
    mut v_h__1_891_: *mut LeanObject,
    mut v_h__2_892_: *mut LeanObject,
    mut v_h__3_893_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_890_) {
        0 => {
            let mut v_it_894_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_895_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_893_);
            lean_dec(v_h__2_892_);
            v_it_894_ = lean_ctor_get(v_x_890_, 0);
            lean_inc(v_it_894_);
            v_out_895_ = lean_ctor_get(v_x_890_, 1);
            lean_inc(v_out_895_);
            lean_dec_ref_known(v_x_890_, 2);
            v___x_896_ = lean_apply_2(v_h__1_891_, v_it_894_, v_out_895_);
            return v___x_896_;
        }
        1 => {
            let mut v_it_897_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_893_);
            lean_dec(v_h__1_891_);
            v_it_897_ = lean_ctor_get(v_x_890_, 0);
            lean_inc(v_it_897_);
            lean_dec_ref_known(v_x_890_, 1);
            v___x_898_ = lean_apply_1(v_h__2_892_, v_it_897_);
            return v___x_898_;
        }
        _ => {
            let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_892_);
            lean_dec(v_h__1_891_);
            v___x_899_ = lean_box(0);
            v___x_900_ = lean_apply_1(v_h__3_893_, v___x_899_);
            return v___x_900_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(
    mut v_x_901_: *mut LeanObject,
    mut v_h__1_902_: *mut LeanObject,
    mut v_h__2_903_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_901_) == 0 {
        let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_903_);
        v___x_904_ = lean_box(0);
        v___x_905_ = lean_apply_1(v_h__1_902_, v___x_904_);
        return v___x_905_;
    } else {
        let mut v_val_906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_902_);
        v_val_906_ = lean_ctor_get(v_x_901_, 0);
        lean_inc(v_val_906_);
        lean_dec_ref_known(v_x_901_, 1);
        v___x_907_ = lean_apply_1(v_h__2_903_, v_val_906_);
        return v___x_907_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(
    mut v_00_u03b3_908_: *mut LeanObject,
    mut v_motive_909_: *mut LeanObject,
    mut v_x_910_: *mut LeanObject,
    mut v_h__1_911_: *mut LeanObject,
    mut v_h__2_912_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_910_) == 0 {
        let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_912_);
        v___x_913_ = lean_box(0);
        v___x_914_ = lean_apply_1(v_h__1_911_, v___x_913_);
        return v___x_914_;
    } else {
        let mut v_val_915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_911_);
        v_val_915_ = lean_ctor_get(v_x_910_, 0);
        lean_inc(v_val_915_);
        lean_dec_ref_known(v_x_910_, 1);
        v___x_916_ = lean_apply_1(v_h__2_912_, v_val_915_);
        return v___x_916_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_917_: *mut LeanObject,
    mut v_h__1_918_: *mut LeanObject,
    mut v_h__2_919_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_917_) == 0 {
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_918_);
        v___x_920_ = lean_box(0);
        v___x_921_ = lean_apply_1(v_h__2_919_, v___x_920_);
        return v___x_921_;
    } else {
        let mut v_val_922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_919_);
        v_val_922_ = lean_ctor_get(v_____do__lift_917_, 0);
        lean_inc(v_val_922_);
        lean_dec_ref_known(v_____do__lift_917_, 1);
        v___x_923_ = lean_apply_1(v_h__1_918_, v_val_922_);
        return v___x_923_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_924_: *mut LeanObject,
    mut v_motive_925_: *mut LeanObject,
    mut v_____do__lift_926_: *mut LeanObject,
    mut v_h__1_927_: *mut LeanObject,
    mut v_h__2_928_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_926_) == 0 {
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_927_);
        v___x_929_ = lean_box(0);
        v___x_930_ = lean_apply_1(v_h__2_928_, v___x_929_);
        return v___x_930_;
    } else {
        let mut v_val_931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_928_);
        v_val_931_ = lean_ctor_get(v_____do__lift_926_, 0);
        lean_inc(v_val_931_);
        lean_dec_ref_known(v_____do__lift_926_, 1);
        v___x_932_ = lean_apply_1(v_h__1_927_, v_val_931_);
        return v___x_932_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_933_: *mut LeanObject,
    mut v_h__1_934_: *mut LeanObject,
    mut v_h__2_935_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_933_) == 0 {
        let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_934_);
        v___x_936_ = lean_box(0);
        v___x_937_ = lean_apply_1(v_h__2_935_, v___x_936_);
        return v___x_937_;
    } else {
        let mut v_val_938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_935_);
        v_val_938_ = lean_ctor_get(v_____do__lift_933_, 0);
        lean_inc(v_val_938_);
        lean_dec_ref_known(v_____do__lift_933_, 1);
        v___x_939_ = lean_apply_1(v_h__1_934_, v_val_938_);
        return v___x_939_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_940_: *mut LeanObject,
    mut v_motive_941_: *mut LeanObject,
    mut v_____do__lift_942_: *mut LeanObject,
    mut v_h__1_943_: *mut LeanObject,
    mut v_h__2_944_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_942_) == 0 {
        let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_943_);
        v___x_945_ = lean_box(0);
        v___x_946_ = lean_apply_1(v_h__2_944_, v___x_945_);
        return v___x_946_;
    } else {
        let mut v_val_947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_944_);
        v_val_947_ = lean_ctor_get(v_____do__lift_942_, 0);
        lean_inc(v_val_947_);
        lean_dec_ref_known(v_____do__lift_942_, 1);
        v___x_948_ = lean_apply_1(v_h__1_943_, v_val_947_);
        return v___x_948_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_949_: *mut LeanObject,
    mut v_h__1_950_: *mut LeanObject,
    mut v_h__2_951_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_949_) == 1 {
        let mut v_val_952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_951_);
        v_val_952_ = lean_ctor_get(v_____x_949_, 0);
        lean_inc(v_val_952_);
        lean_dec_ref_known(v_____x_949_, 1);
        v___x_953_ = lean_apply_1(v_h__1_950_, v_val_952_);
        return v___x_953_;
    } else {
        let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_950_);
        v___x_954_ = lean_apply_2(v_h__2_951_, v_____x_949_, lean_box(0));
        return v___x_954_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_955_: *mut LeanObject,
    mut v_motive_956_: *mut LeanObject,
    mut v_____x_957_: *mut LeanObject,
    mut v_h__1_958_: *mut LeanObject,
    mut v_h__2_959_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_957_) == 1 {
        let mut v_val_960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_959_);
        v_val_960_ = lean_ctor_get(v_____x_957_, 0);
        lean_inc(v_val_960_);
        lean_dec_ref_known(v_____x_957_, 1);
        v___x_961_ = lean_apply_1(v_h__1_958_, v_val_960_);
        return v___x_961_;
    } else {
        let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_958_);
        v___x_962_ = lean_apply_2(v_h__2_959_, v_____x_957_, lean_box(0));
        return v___x_962_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_963_: *mut LeanObject,
    mut v_h__1_964_: *mut LeanObject,
    mut v_h__2_965_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_963_) == 1 {
        let mut v_val_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_965_);
        v_val_966_ = lean_ctor_get(v_____x_963_, 0);
        lean_inc(v_val_966_);
        lean_dec_ref_known(v_____x_963_, 1);
        v___x_967_ = lean_apply_1(v_h__1_964_, v_val_966_);
        return v___x_967_;
    } else {
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_964_);
        v___x_968_ = lean_apply_2(v_h__2_965_, v_____x_963_, lean_box(0));
        return v___x_968_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_969_: *mut LeanObject,
    mut v_motive_970_: *mut LeanObject,
    mut v_____x_971_: *mut LeanObject,
    mut v_h__1_972_: *mut LeanObject,
    mut v_h__2_973_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_971_) == 1 {
        let mut v_val_974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_973_);
        v_val_974_ = lean_ctor_get(v_____x_971_, 0);
        lean_inc(v_val_974_);
        lean_dec_ref_known(v_____x_971_, 1);
        v___x_975_ = lean_apply_1(v_h__1_972_, v_val_974_);
        return v___x_975_;
    } else {
        let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_972_);
        v___x_976_ = lean_apply_2(v_h__2_973_, v_____x_971_, lean_box(0));
        return v___x_976_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_977_: *mut LeanObject,
    mut v_h__1_978_: *mut LeanObject,
    mut v_h__2_979_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_977_) == 0 {
        let mut v_a_980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_978_);
        v_a_980_ = lean_ctor_get(v_____do__lift_977_, 0);
        lean_inc(v_a_980_);
        lean_dec_ref_known(v_____do__lift_977_, 1);
        v___x_981_ = lean_apply_1(v_h__2_979_, v_a_980_);
        return v___x_981_;
    } else {
        let mut v_a_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_979_);
        v_a_982_ = lean_ctor_get(v_____do__lift_977_, 0);
        lean_inc(v_a_982_);
        lean_dec_ref_known(v_____do__lift_977_, 1);
        v___x_983_ = lean_apply_1(v_h__1_978_, v_a_982_);
        return v___x_983_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_984_: *mut LeanObject,
    mut v_motive_985_: *mut LeanObject,
    mut v_____do__lift_986_: *mut LeanObject,
    mut v_h__1_987_: *mut LeanObject,
    mut v_h__2_988_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_986_) == 0 {
        let mut v_a_989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_987_);
        v_a_989_ = lean_ctor_get(v_____do__lift_986_, 0);
        lean_inc(v_a_989_);
        lean_dec_ref_known(v_____do__lift_986_, 1);
        v___x_990_ = lean_apply_1(v_h__2_988_, v_a_989_);
        return v___x_990_;
    } else {
        let mut v_a_991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_988_);
        v_a_991_ = lean_ctor_get(v_____do__lift_986_, 0);
        lean_inc(v_a_991_);
        lean_dec_ref_known(v_____do__lift_986_, 1);
        v___x_992_ = lean_apply_1(v_h__1_987_, v_a_991_);
        return v___x_992_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_993_: *mut LeanObject,
    mut v_h__1_994_: *mut LeanObject,
    mut v_h__2_995_: *mut LeanObject,
    mut v_h__3_996_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_993_) {
        0 => {
            let mut v_it_997_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_998_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_996_);
            lean_dec(v_h__2_995_);
            v_it_997_ = lean_ctor_get(v_x_993_, 0);
            lean_inc(v_it_997_);
            v_out_998_ = lean_ctor_get(v_x_993_, 1);
            lean_inc(v_out_998_);
            lean_dec_ref_known(v_x_993_, 2);
            v___x_999_ = lean_apply_3(v_h__1_994_, v_it_997_, v_out_998_, lean_box(0));
            return v___x_999_;
        }
        1 => {
            let mut v_it_1000_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_996_);
            lean_dec(v_h__1_994_);
            v_it_1000_ = lean_ctor_get(v_x_993_, 0);
            lean_inc(v_it_1000_);
            lean_dec_ref_known(v_x_993_, 1);
            v___x_1001_ = lean_apply_2(v_h__2_995_, v_it_1000_, lean_box(0));
            return v___x_1001_;
        }
        _ => {
            let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_995_);
            lean_dec(v_h__1_994_);
            v___x_1002_ = lean_apply_1(v_h__3_996_, lean_box(0));
            return v___x_1002_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_1003_: *mut LeanObject,
    mut v_00_u03b2_1004_: *mut LeanObject,
    mut v_m_1005_: *mut LeanObject,
    mut v_inst_1006_: *mut LeanObject,
    mut v_it_1007_: *mut LeanObject,
    mut v_motive_1008_: *mut LeanObject,
    mut v_x_1009_: *mut LeanObject,
    mut v_h__1_1010_: *mut LeanObject,
    mut v_h__2_1011_: *mut LeanObject,
    mut v_h__3_1012_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1009_) {
        0 => {
            let mut v_it_1013_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1014_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1012_);
            lean_dec(v_h__2_1011_);
            v_it_1013_ = lean_ctor_get(v_x_1009_, 0);
            lean_inc(v_it_1013_);
            v_out_1014_ = lean_ctor_get(v_x_1009_, 1);
            lean_inc(v_out_1014_);
            lean_dec_ref_known(v_x_1009_, 2);
            v___x_1015_ = lean_apply_3(v_h__1_1010_, v_it_1013_, v_out_1014_, lean_box(0));
            return v___x_1015_;
        }
        1 => {
            let mut v_it_1016_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1012_);
            lean_dec(v_h__1_1010_);
            v_it_1016_ = lean_ctor_get(v_x_1009_, 0);
            lean_inc(v_it_1016_);
            lean_dec_ref_known(v_x_1009_, 1);
            v___x_1017_ = lean_apply_2(v_h__2_1011_, v_it_1016_, lean_box(0));
            return v___x_1017_;
        }
        _ => {
            let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1011_);
            lean_dec(v_h__1_1010_);
            v___x_1018_ = lean_apply_1(v_h__3_1012_, lean_box(0));
            return v___x_1018_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_1019_: *mut LeanObject,
    mut v_00_u03b2_1020_: *mut LeanObject,
    mut v_m_1021_: *mut LeanObject,
    mut v_inst_1022_: *mut LeanObject,
    mut v_it_1023_: *mut LeanObject,
    mut v_motive_1024_: *mut LeanObject,
    mut v_x_1025_: *mut LeanObject,
    mut v_h__1_1026_: *mut LeanObject,
    mut v_h__2_1027_: *mut LeanObject,
    mut v_h__3_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_1019_, v_00_u03b2_1020_, v_m_1021_, v_inst_1022_, v_it_1023_, v_motive_1024_, v_x_1025_, v_h__1_1026_, v_h__2_1027_, v_h__3_1028_);
    lean_dec(v_it_1023_);
    lean_dec(v_inst_1022_);
    return v_res_1029_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_1030_: *mut LeanObject,
    mut v_h__1_1031_: *mut LeanObject,
    mut v_h__2_1032_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1030_) == 0 {
        let mut v_a_1033_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1031_);
        v_a_1033_ = lean_ctor_get(v_____do__lift_1030_, 0);
        lean_inc(v_a_1033_);
        lean_dec_ref_known(v_____do__lift_1030_, 1);
        v___x_1034_ = lean_apply_1(v_h__2_1032_, v_a_1033_);
        return v___x_1034_;
    } else {
        let mut v_a_1035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1032_);
        v_a_1035_ = lean_ctor_get(v_____do__lift_1030_, 0);
        lean_inc(v_a_1035_);
        lean_dec_ref_known(v_____do__lift_1030_, 1);
        v___x_1036_ = lean_apply_1(v_h__1_1031_, v_a_1035_);
        return v___x_1036_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_1037_: *mut LeanObject,
    mut v_motive_1038_: *mut LeanObject,
    mut v_____do__lift_1039_: *mut LeanObject,
    mut v_h__1_1040_: *mut LeanObject,
    mut v_h__2_1041_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1039_) == 0 {
        let mut v_a_1042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1040_);
        v_a_1042_ = lean_ctor_get(v_____do__lift_1039_, 0);
        lean_inc(v_a_1042_);
        lean_dec_ref_known(v_____do__lift_1039_, 1);
        v___x_1043_ = lean_apply_1(v_h__2_1041_, v_a_1042_);
        return v___x_1043_;
    } else {
        let mut v_a_1044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1041_);
        v_a_1044_ = lean_ctor_get(v_____do__lift_1039_, 0);
        lean_inc(v_a_1044_);
        lean_dec_ref_known(v_____do__lift_1039_, 1);
        v___x_1045_ = lean_apply_1(v_h__1_1040_, v_a_1044_);
        return v___x_1045_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_1046_: *mut LeanObject,
    mut v_h__1_1047_: *mut LeanObject,
    mut v_h__2_1048_: *mut LeanObject,
    mut v_h__3_1049_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1046_) {
        0 => {
            let mut v_it_1050_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1051_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1049_);
            lean_dec(v_h__2_1048_);
            v_it_1050_ = lean_ctor_get(v_x_1046_, 0);
            lean_inc(v_it_1050_);
            v_out_1051_ = lean_ctor_get(v_x_1046_, 1);
            lean_inc(v_out_1051_);
            lean_dec_ref_known(v_x_1046_, 2);
            v___x_1052_ = lean_apply_2(v_h__1_1047_, v_it_1050_, v_out_1051_);
            return v___x_1052_;
        }
        1 => {
            let mut v_it_1053_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1049_);
            lean_dec(v_h__1_1047_);
            v_it_1053_ = lean_ctor_get(v_x_1046_, 0);
            lean_inc(v_it_1053_);
            lean_dec_ref_known(v_x_1046_, 1);
            v___x_1054_ = lean_apply_1(v_h__2_1048_, v_it_1053_);
            return v___x_1054_;
        }
        _ => {
            let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1048_);
            lean_dec(v_h__1_1047_);
            v___x_1055_ = lean_box(0);
            v___x_1056_ = lean_apply_1(v_h__3_1049_, v___x_1055_);
            return v___x_1056_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_1057_: *mut LeanObject,
    mut v_00_u03b2_1058_: *mut LeanObject,
    mut v_motive_1059_: *mut LeanObject,
    mut v_x_1060_: *mut LeanObject,
    mut v_h__1_1061_: *mut LeanObject,
    mut v_h__2_1062_: *mut LeanObject,
    mut v_h__3_1063_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1060_) {
        0 => {
            let mut v_it_1064_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1065_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1063_);
            lean_dec(v_h__2_1062_);
            v_it_1064_ = lean_ctor_get(v_x_1060_, 0);
            lean_inc(v_it_1064_);
            v_out_1065_ = lean_ctor_get(v_x_1060_, 1);
            lean_inc(v_out_1065_);
            lean_dec_ref_known(v_x_1060_, 2);
            v___x_1066_ = lean_apply_2(v_h__1_1061_, v_it_1064_, v_out_1065_);
            return v___x_1066_;
        }
        1 => {
            let mut v_it_1067_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1063_);
            lean_dec(v_h__1_1061_);
            v_it_1067_ = lean_ctor_get(v_x_1060_, 0);
            lean_inc(v_it_1067_);
            lean_dec_ref_known(v_x_1060_, 1);
            v___x_1068_ = lean_apply_1(v_h__2_1062_, v_it_1067_);
            return v___x_1068_;
        }
        _ => {
            let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1062_);
            lean_dec(v_h__1_1061_);
            v___x_1069_ = lean_box(0);
            v___x_1070_ = lean_apply_1(v_h__3_1063_, v___x_1069_);
            return v___x_1070_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
}
