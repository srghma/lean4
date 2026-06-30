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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_536_: *mut leanh::LeanObject,
    mut v_h__1_537_: *mut leanh::LeanObject,
    mut v_h__2_538_: *mut leanh::LeanObject,
    mut v_h__3_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_536_) {
        0 => {
            let mut v_it_540_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_541_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_539_);
            leanh::lean_dec(v_h__2_538_);
            v_it_540_ = leanh::lean_ctor_get(v_x_536_, 0);
            leanh::lean_inc(v_it_540_);
            v_out_541_ = leanh::lean_ctor_get(v_x_536_, 1);
            leanh::lean_inc(v_out_541_);
            leanh::lean_dec_ref_known(v_x_536_, 2);
            v___x_542_ = leanh::lean_apply_3(
                v_h__1_537_,
                v_it_540_,
                v_out_541_,
                leanh::lean_box(0),
            );
            return v___x_542_;
        }
        1 => {
            let mut v_it_543_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_539_);
            leanh::lean_dec(v_h__1_537_);
            v_it_543_ = leanh::lean_ctor_get(v_x_536_, 0);
            leanh::lean_inc(v_it_543_);
            leanh::lean_dec_ref_known(v_x_536_, 1);
            v___x_544_ =
                leanh::lean_apply_2(v_h__2_538_, v_it_543_, leanh::lean_box(0));
            return v___x_544_;
        }
        _ => {
            let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_538_);
            leanh::lean_dec(v_h__1_537_);
            v___x_545_ = leanh::lean_apply_1(v_h__3_539_, leanh::lean_box(0));
            return v___x_545_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_546_: *mut leanh::LeanObject,
    mut v_00_u03b2_547_: *mut leanh::LeanObject,
    mut v_m_548_: *mut leanh::LeanObject,
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_it_550_: *mut leanh::LeanObject,
    mut v_motive_551_: *mut leanh::LeanObject,
    mut v_x_552_: *mut leanh::LeanObject,
    mut v_h__1_553_: *mut leanh::LeanObject,
    mut v_h__2_554_: *mut leanh::LeanObject,
    mut v_h__3_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_552_) {
        0 => {
            let mut v_it_556_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_555_);
            leanh::lean_dec(v_h__2_554_);
            v_it_556_ = leanh::lean_ctor_get(v_x_552_, 0);
            leanh::lean_inc(v_it_556_);
            v_out_557_ = leanh::lean_ctor_get(v_x_552_, 1);
            leanh::lean_inc(v_out_557_);
            leanh::lean_dec_ref_known(v_x_552_, 2);
            v___x_558_ = leanh::lean_apply_3(
                v_h__1_553_,
                v_it_556_,
                v_out_557_,
                leanh::lean_box(0),
            );
            return v___x_558_;
        }
        1 => {
            let mut v_it_559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_555_);
            leanh::lean_dec(v_h__1_553_);
            v_it_559_ = leanh::lean_ctor_get(v_x_552_, 0);
            leanh::lean_inc(v_it_559_);
            leanh::lean_dec_ref_known(v_x_552_, 1);
            v___x_560_ =
                leanh::lean_apply_2(v_h__2_554_, v_it_559_, leanh::lean_box(0));
            return v___x_560_;
        }
        _ => {
            let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_554_);
            leanh::lean_dec(v_h__1_553_);
            v___x_561_ = leanh::lean_apply_1(v_h__3_555_, leanh::lean_box(0));
            return v___x_561_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_562_: *mut leanh::LeanObject,
    mut v_00_u03b2_563_: *mut leanh::LeanObject,
    mut v_m_564_: *mut leanh::LeanObject,
    mut v_inst_565_: *mut leanh::LeanObject,
    mut v_it_566_: *mut leanh::LeanObject,
    mut v_motive_567_: *mut leanh::LeanObject,
    mut v_x_568_: *mut leanh::LeanObject,
    mut v_h__1_569_: *mut leanh::LeanObject,
    mut v_h__2_570_: *mut leanh::LeanObject,
    mut v_h__3_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_562_, v_00_u03b2_563_, v_m_564_, v_inst_565_, v_it_566_, v_motive_567_, v_x_568_, v_h__1_569_, v_h__2_570_, v_h__3_571_);
    leanh::lean_dec(v_it_566_);
    leanh::lean_dec(v_inst_565_);
    return v_res_572_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_573_: *mut leanh::LeanObject,
    mut v_h__1_574_: *mut leanh::LeanObject,
    mut v_h__2_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_573_) == 0 {
        let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_575_);
        v___x_576_ = leanh::lean_apply_1(v_h__1_574_, leanh::lean_box(0));
        return v___x_576_;
    } else {
        let mut v_val_577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_574_);
        v_val_577_ = leanh::lean_ctor_get(v_____do__lift_573_, 0);
        leanh::lean_inc(v_val_577_);
        leanh::lean_dec_ref_known(v_____do__lift_573_, 1);
        v___x_578_ = leanh::lean_apply_2(v_h__2_575_, v_val_577_, leanh::lean_box(0));
        return v___x_578_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_579_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_580_: *mut leanh::LeanObject,
    mut v_n_581_: *mut leanh::LeanObject,
    mut v_f_582_: *mut leanh::LeanObject,
    mut v_out_583_: *mut leanh::LeanObject,
    mut v_motive_584_: *mut leanh::LeanObject,
    mut v_____do__lift_585_: *mut leanh::LeanObject,
    mut v_h__1_586_: *mut leanh::LeanObject,
    mut v_h__2_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_585_) == 0 {
        let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_587_);
        v___x_588_ = leanh::lean_apply_1(v_h__1_586_, leanh::lean_box(0));
        return v___x_588_;
    } else {
        let mut v_val_589_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_586_);
        v_val_589_ = leanh::lean_ctor_get(v_____do__lift_585_, 0);
        leanh::lean_inc(v_val_589_);
        leanh::lean_dec_ref_known(v_____do__lift_585_, 1);
        v___x_590_ = leanh::lean_apply_2(v_h__2_587_, v_val_589_, leanh::lean_box(0));
        return v___x_590_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_591_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_592_: *mut leanh::LeanObject,
    mut v_n_593_: *mut leanh::LeanObject,
    mut v_f_594_: *mut leanh::LeanObject,
    mut v_out_595_: *mut leanh::LeanObject,
    mut v_motive_596_: *mut leanh::LeanObject,
    mut v_____do__lift_597_: *mut leanh::LeanObject,
    mut v_h__1_598_: *mut leanh::LeanObject,
    mut v_h__2_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_591_, v_00_u03b2_x27_592_, v_n_593_, v_f_594_, v_out_595_, v_motive_596_, v_____do__lift_597_, v_h__1_598_, v_h__2_599_);
    leanh::lean_dec(v_out_595_);
    leanh::lean_dec(v_f_594_);
    return v_res_600_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_601_: *mut leanh::LeanObject,
    mut v_h__1_602_: *mut leanh::LeanObject,
    mut v_h__2_603_: *mut leanh::LeanObject,
    mut v_h__3_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_601_) {
        0 => {
            let mut v_it_605_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_606_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_604_);
            leanh::lean_dec(v_h__2_603_);
            v_it_605_ = leanh::lean_ctor_get(v_x_601_, 0);
            leanh::lean_inc(v_it_605_);
            v_out_606_ = leanh::lean_ctor_get(v_x_601_, 1);
            leanh::lean_inc(v_out_606_);
            leanh::lean_dec_ref_known(v_x_601_, 2);
            v___x_607_ = leanh::lean_apply_3(
                v_h__1_602_,
                v_it_605_,
                v_out_606_,
                leanh::lean_box(0),
            );
            return v___x_607_;
        }
        1 => {
            let mut v_it_608_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_604_);
            leanh::lean_dec(v_h__1_602_);
            v_it_608_ = leanh::lean_ctor_get(v_x_601_, 0);
            leanh::lean_inc(v_it_608_);
            leanh::lean_dec_ref_known(v_x_601_, 1);
            v___x_609_ =
                leanh::lean_apply_2(v_h__2_603_, v_it_608_, leanh::lean_box(0));
            return v___x_609_;
        }
        _ => {
            let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_603_);
            leanh::lean_dec(v_h__1_602_);
            v___x_610_ = leanh::lean_apply_1(v_h__3_604_, leanh::lean_box(0));
            return v___x_610_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_611_: *mut leanh::LeanObject,
    mut v_00_u03b2_612_: *mut leanh::LeanObject,
    mut v_inst_613_: *mut leanh::LeanObject,
    mut v_it_614_: *mut leanh::LeanObject,
    mut v_motive_615_: *mut leanh::LeanObject,
    mut v_x_616_: *mut leanh::LeanObject,
    mut v_h__1_617_: *mut leanh::LeanObject,
    mut v_h__2_618_: *mut leanh::LeanObject,
    mut v_h__3_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_616_) {
        0 => {
            let mut v_it_620_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_621_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_619_);
            leanh::lean_dec(v_h__2_618_);
            v_it_620_ = leanh::lean_ctor_get(v_x_616_, 0);
            leanh::lean_inc(v_it_620_);
            v_out_621_ = leanh::lean_ctor_get(v_x_616_, 1);
            leanh::lean_inc(v_out_621_);
            leanh::lean_dec_ref_known(v_x_616_, 2);
            v___x_622_ = leanh::lean_apply_3(
                v_h__1_617_,
                v_it_620_,
                v_out_621_,
                leanh::lean_box(0),
            );
            return v___x_622_;
        }
        1 => {
            let mut v_it_623_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_619_);
            leanh::lean_dec(v_h__1_617_);
            v_it_623_ = leanh::lean_ctor_get(v_x_616_, 0);
            leanh::lean_inc(v_it_623_);
            leanh::lean_dec_ref_known(v_x_616_, 1);
            v___x_624_ =
                leanh::lean_apply_2(v_h__2_618_, v_it_623_, leanh::lean_box(0));
            return v___x_624_;
        }
        _ => {
            let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_618_);
            leanh::lean_dec(v_h__1_617_);
            v___x_625_ = leanh::lean_apply_1(v_h__3_619_, leanh::lean_box(0));
            return v___x_625_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_626_: *mut leanh::LeanObject,
    mut v_00_u03b2_627_: *mut leanh::LeanObject,
    mut v_inst_628_: *mut leanh::LeanObject,
    mut v_it_629_: *mut leanh::LeanObject,
    mut v_motive_630_: *mut leanh::LeanObject,
    mut v_x_631_: *mut leanh::LeanObject,
    mut v_h__1_632_: *mut leanh::LeanObject,
    mut v_h__2_633_: *mut leanh::LeanObject,
    mut v_h__3_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_635_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_626_, v_00_u03b2_627_, v_inst_628_, v_it_629_, v_motive_630_, v_x_631_, v_h__1_632_, v_h__2_633_, v_h__3_634_);
    leanh::lean_dec(v_it_629_);
    leanh::lean_dec(v_inst_628_);
    return v_res_635_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_636_: *mut leanh::LeanObject,
    mut v_h__1_637_: *mut leanh::LeanObject,
    mut v_h__2_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_636_) == 0 {
        let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_638_);
        v___x_639_ = leanh::lean_apply_1(v_h__1_637_, leanh::lean_box(0));
        return v___x_639_;
    } else {
        let mut v_val_640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_637_);
        v_val_640_ = leanh::lean_ctor_get(v_____do__lift_636_, 0);
        leanh::lean_inc(v_val_640_);
        leanh::lean_dec_ref_known(v_____do__lift_636_, 1);
        v___x_641_ = leanh::lean_apply_2(v_h__2_638_, v_val_640_, leanh::lean_box(0));
        return v___x_641_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_642_: *mut leanh::LeanObject,
    mut v_00_u03b3_643_: *mut leanh::LeanObject,
    mut v_n_644_: *mut leanh::LeanObject,
    mut v_f_645_: *mut leanh::LeanObject,
    mut v_out_646_: *mut leanh::LeanObject,
    mut v_motive_647_: *mut leanh::LeanObject,
    mut v_____do__lift_648_: *mut leanh::LeanObject,
    mut v_h__1_649_: *mut leanh::LeanObject,
    mut v_h__2_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_648_) == 0 {
        let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_650_);
        v___x_651_ = leanh::lean_apply_1(v_h__1_649_, leanh::lean_box(0));
        return v___x_651_;
    } else {
        let mut v_val_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_649_);
        v_val_652_ = leanh::lean_ctor_get(v_____do__lift_648_, 0);
        leanh::lean_inc(v_val_652_);
        leanh::lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_653_ = leanh::lean_apply_2(v_h__2_650_, v_val_652_, leanh::lean_box(0));
        return v___x_653_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_654_: *mut leanh::LeanObject,
    mut v_00_u03b3_655_: *mut leanh::LeanObject,
    mut v_n_656_: *mut leanh::LeanObject,
    mut v_f_657_: *mut leanh::LeanObject,
    mut v_out_658_: *mut leanh::LeanObject,
    mut v_motive_659_: *mut leanh::LeanObject,
    mut v_____do__lift_660_: *mut leanh::LeanObject,
    mut v_h__1_661_: *mut leanh::LeanObject,
    mut v_h__2_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_654_, v_00_u03b3_655_, v_n_656_, v_f_657_, v_out_658_, v_motive_659_, v_____do__lift_660_, v_h__1_661_, v_h__2_662_);
    leanh::lean_dec(v_out_658_);
    leanh::lean_dec(v_f_657_);
    return v_res_663_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_664_: u8,
    mut v_h__1_665_: *mut leanh::LeanObject,
    mut v_h__2_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_664_ == 0 {
        let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_666_);
        v___x_667_ = leanh::lean_apply_1(v_h__1_665_, leanh::lean_box(0));
        return v___x_667_;
    } else {
        let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_665_);
        v___x_668_ = leanh::lean_apply_1(v_h__2_666_, leanh::lean_box(0));
        return v___x_668_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_669_: *mut leanh::LeanObject,
    mut v_h__1_670_: *mut leanh::LeanObject,
    mut v_h__2_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_72__boxed_672_: u8 = 0;
    let mut v_res_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_672_ = (leanh::lean_unbox(v_____do__lift_669_) as u8);
    v_res_673_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_672_, v_h__1_670_, v_h__2_671_);
    return v_res_673_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_674_: *mut leanh::LeanObject,
    mut v_n_675_: *mut leanh::LeanObject,
    mut v_f_676_: *mut leanh::LeanObject,
    mut v_out_677_: *mut leanh::LeanObject,
    mut v_motive_678_: *mut leanh::LeanObject,
    mut v_____do__lift_679_: u8,
    mut v_h__1_680_: *mut leanh::LeanObject,
    mut v_h__2_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_679_ == 0 {
        let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_681_);
        v___x_682_ = leanh::lean_apply_1(v_h__1_680_, leanh::lean_box(0));
        return v___x_682_;
    } else {
        let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_680_);
        v___x_683_ = leanh::lean_apply_1(v_h__2_681_, leanh::lean_box(0));
        return v___x_683_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_684_: *mut leanh::LeanObject,
    mut v_n_685_: *mut leanh::LeanObject,
    mut v_f_686_: *mut leanh::LeanObject,
    mut v_out_687_: *mut leanh::LeanObject,
    mut v_motive_688_: *mut leanh::LeanObject,
    mut v_____do__lift_689_: *mut leanh::LeanObject,
    mut v_h__1_690_: *mut leanh::LeanObject,
    mut v_h__2_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_79__boxed_692_: u8 = 0;
    let mut v_res_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_692_ = (leanh::lean_unbox(v_____do__lift_689_) as u8);
    v_res_693_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_684_, v_n_685_, v_f_686_, v_out_687_, v_motive_688_, v_____do__lift_79__boxed_692_, v_h__1_690_, v_h__2_691_);
    leanh::lean_dec(v_out_687_);
    leanh::lean_dec(v_f_686_);
    return v_res_693_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_694_: u8,
    mut v_h__1_695_: *mut leanh::LeanObject,
    mut v_h__2_696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_694_ == 0 {
        let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_696_);
        v___x_697_ = leanh::lean_apply_1(v_h__1_695_, leanh::lean_box(0));
        return v___x_697_;
    } else {
        let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_695_);
        v___x_698_ = leanh::lean_apply_1(v_h__2_696_, leanh::lean_box(0));
        return v___x_698_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_699_: *mut leanh::LeanObject,
    mut v_h__1_700_: *mut leanh::LeanObject,
    mut v_h__2_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_72__boxed_702_: u8 = 0;
    let mut v_res_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_702_ = (leanh::lean_unbox(v_____do__lift_699_) as u8);
    v_res_703_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_702_, v_h__1_700_, v_h__2_701_);
    return v_res_703_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_704_: *mut leanh::LeanObject,
    mut v_n_705_: *mut leanh::LeanObject,
    mut v_f_706_: *mut leanh::LeanObject,
    mut v_out_707_: *mut leanh::LeanObject,
    mut v_motive_708_: *mut leanh::LeanObject,
    mut v_____do__lift_709_: u8,
    mut v_h__1_710_: *mut leanh::LeanObject,
    mut v_h__2_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_709_ == 0 {
        let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_711_);
        v___x_712_ = leanh::lean_apply_1(v_h__1_710_, leanh::lean_box(0));
        return v___x_712_;
    } else {
        let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_710_);
        v___x_713_ = leanh::lean_apply_1(v_h__2_711_, leanh::lean_box(0));
        return v___x_713_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_714_: *mut leanh::LeanObject,
    mut v_n_715_: *mut leanh::LeanObject,
    mut v_f_716_: *mut leanh::LeanObject,
    mut v_out_717_: *mut leanh::LeanObject,
    mut v_motive_718_: *mut leanh::LeanObject,
    mut v_____do__lift_719_: *mut leanh::LeanObject,
    mut v_h__1_720_: *mut leanh::LeanObject,
    mut v_h__2_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_79__boxed_722_: u8 = 0;
    let mut v_res_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_722_ = (leanh::lean_unbox(v_____do__lift_719_) as u8);
    v_res_723_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_714_, v_n_715_, v_f_716_, v_out_717_, v_motive_718_, v_____do__lift_79__boxed_722_, v_h__1_720_, v_h__2_721_);
    leanh::lean_dec(v_out_717_);
    leanh::lean_dec(v_f_716_);
    return v_res_723_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_724_: *mut leanh::LeanObject,
    mut v_h__1_725_: *mut leanh::LeanObject,
    mut v_h__2_726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_724_) == 0 {
        let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_726_);
        v___x_727_ = leanh::lean_apply_1(v_h__1_725_, leanh::lean_box(0));
        return v___x_727_;
    } else {
        let mut v_val_728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_725_);
        v_val_728_ = leanh::lean_ctor_get(v_____do__lift_724_, 0);
        leanh::lean_inc(v_val_728_);
        leanh::lean_dec_ref_known(v_____do__lift_724_, 1);
        v___x_729_ = leanh::lean_apply_2(v_h__2_726_, v_val_728_, leanh::lean_box(0));
        return v___x_729_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_730_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_731_: *mut leanh::LeanObject,
    mut v_n_732_: *mut leanh::LeanObject,
    mut v_f_733_: *mut leanh::LeanObject,
    mut v_inst_734_: *mut leanh::LeanObject,
    mut v_out_735_: *mut leanh::LeanObject,
    mut v_motive_736_: *mut leanh::LeanObject,
    mut v_____do__lift_737_: *mut leanh::LeanObject,
    mut v_h__1_738_: *mut leanh::LeanObject,
    mut v_h__2_739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_737_) == 0 {
        let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_739_);
        v___x_740_ = leanh::lean_apply_1(v_h__1_738_, leanh::lean_box(0));
        return v___x_740_;
    } else {
        let mut v_val_741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_738_);
        v_val_741_ = leanh::lean_ctor_get(v_____do__lift_737_, 0);
        leanh::lean_inc(v_val_741_);
        leanh::lean_dec_ref_known(v_____do__lift_737_, 1);
        v___x_742_ = leanh::lean_apply_2(v_h__2_739_, v_val_741_, leanh::lean_box(0));
        return v___x_742_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_743_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_744_: *mut leanh::LeanObject,
    mut v_n_745_: *mut leanh::LeanObject,
    mut v_f_746_: *mut leanh::LeanObject,
    mut v_inst_747_: *mut leanh::LeanObject,
    mut v_out_748_: *mut leanh::LeanObject,
    mut v_motive_749_: *mut leanh::LeanObject,
    mut v_____do__lift_750_: *mut leanh::LeanObject,
    mut v_h__1_751_: *mut leanh::LeanObject,
    mut v_h__2_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_743_, v_00_u03b2_x27_744_, v_n_745_, v_f_746_, v_inst_747_, v_out_748_, v_motive_749_, v_____do__lift_750_, v_h__1_751_, v_h__2_752_);
    leanh::lean_dec(v_out_748_);
    leanh::lean_dec(v_inst_747_);
    leanh::lean_dec(v_f_746_);
    return v_res_753_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_754_: *mut leanh::LeanObject,
    mut v_h__1_755_: *mut leanh::LeanObject,
    mut v_h__2_756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_754_) == 0 {
        let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_756_);
        v___x_757_ = leanh::lean_apply_1(v_h__1_755_, leanh::lean_box(0));
        return v___x_757_;
    } else {
        let mut v_val_758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_755_);
        v_val_758_ = leanh::lean_ctor_get(v_____do__lift_754_, 0);
        leanh::lean_inc(v_val_758_);
        leanh::lean_dec_ref_known(v_____do__lift_754_, 1);
        v___x_759_ = leanh::lean_apply_2(v_h__2_756_, v_val_758_, leanh::lean_box(0));
        return v___x_759_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_760_: *mut leanh::LeanObject,
    mut v_n_761_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_762_: *mut leanh::LeanObject,
    mut v_f_763_: *mut leanh::LeanObject,
    mut v_inst_764_: *mut leanh::LeanObject,
    mut v_out_765_: *mut leanh::LeanObject,
    mut v_motive_766_: *mut leanh::LeanObject,
    mut v_____do__lift_767_: *mut leanh::LeanObject,
    mut v_h__1_768_: *mut leanh::LeanObject,
    mut v_h__2_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_767_) == 0 {
        let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_769_);
        v___x_770_ = leanh::lean_apply_1(v_h__1_768_, leanh::lean_box(0));
        return v___x_770_;
    } else {
        let mut v_val_771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_768_);
        v_val_771_ = leanh::lean_ctor_get(v_____do__lift_767_, 0);
        leanh::lean_inc(v_val_771_);
        leanh::lean_dec_ref_known(v_____do__lift_767_, 1);
        v___x_772_ = leanh::lean_apply_2(v_h__2_769_, v_val_771_, leanh::lean_box(0));
        return v___x_772_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_773_: *mut leanh::LeanObject,
    mut v_n_774_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_775_: *mut leanh::LeanObject,
    mut v_f_776_: *mut leanh::LeanObject,
    mut v_inst_777_: *mut leanh::LeanObject,
    mut v_out_778_: *mut leanh::LeanObject,
    mut v_motive_779_: *mut leanh::LeanObject,
    mut v_____do__lift_780_: *mut leanh::LeanObject,
    mut v_h__1_781_: *mut leanh::LeanObject,
    mut v_h__2_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(v_00_u03b2_773_, v_n_774_, v_00_u03b2_x27_775_, v_f_776_, v_inst_777_, v_out_778_, v_motive_779_, v_____do__lift_780_, v_h__1_781_, v_h__2_782_);
    leanh::lean_dec(v_out_778_);
    leanh::lean_dec(v_inst_777_);
    leanh::lean_dec(v_f_776_);
    return v_res_783_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_784_: u8,
    mut v_h__1_785_: *mut leanh::LeanObject,
    mut v_h__2_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_784_ == 0 {
        let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_786_);
        v___x_787_ = leanh::lean_apply_1(v_h__1_785_, leanh::lean_box(0));
        return v___x_787_;
    } else {
        let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_785_);
        v___x_788_ = leanh::lean_apply_1(v_h__2_786_, leanh::lean_box(0));
        return v___x_788_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_789_: *mut leanh::LeanObject,
    mut v_h__1_790_: *mut leanh::LeanObject,
    mut v_h__2_791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_74__boxed_792_: u8 = 0;
    let mut v_res_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_792_ = (leanh::lean_unbox(v_____do__lift_789_) as u8);
    v_res_793_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_792_, v_h__1_790_, v_h__2_791_);
    return v_res_793_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(
    mut v_00_u03b2_794_: *mut leanh::LeanObject,
    mut v_n_795_: *mut leanh::LeanObject,
    mut v_f_796_: *mut leanh::LeanObject,
    mut v_inst_797_: *mut leanh::LeanObject,
    mut v_out_798_: *mut leanh::LeanObject,
    mut v_motive_799_: *mut leanh::LeanObject,
    mut v_____do__lift_800_: u8,
    mut v_h__1_801_: *mut leanh::LeanObject,
    mut v_h__2_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_800_ == 0 {
        let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_802_);
        v___x_803_ = leanh::lean_apply_1(v_h__1_801_, leanh::lean_box(0));
        return v___x_803_;
    } else {
        let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_801_);
        v___x_804_ = leanh::lean_apply_1(v_h__2_802_, leanh::lean_box(0));
        return v___x_804_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_805_: *mut leanh::LeanObject,
    mut v_n_806_: *mut leanh::LeanObject,
    mut v_f_807_: *mut leanh::LeanObject,
    mut v_inst_808_: *mut leanh::LeanObject,
    mut v_out_809_: *mut leanh::LeanObject,
    mut v_motive_810_: *mut leanh::LeanObject,
    mut v_____do__lift_811_: *mut leanh::LeanObject,
    mut v_h__1_812_: *mut leanh::LeanObject,
    mut v_h__2_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_82__boxed_814_: u8 = 0;
    let mut v_res_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_814_ = (leanh::lean_unbox(v_____do__lift_811_) as u8);
    v_res_815_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_805_, v_n_806_, v_f_807_, v_inst_808_, v_out_809_, v_motive_810_, v_____do__lift_82__boxed_814_, v_h__1_812_, v_h__2_813_);
    leanh::lean_dec(v_out_809_);
    leanh::lean_dec(v_inst_808_);
    leanh::lean_dec(v_f_807_);
    return v_res_815_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_816_: u8,
    mut v_h__1_817_: *mut leanh::LeanObject,
    mut v_h__2_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_816_ == 0 {
        let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_818_);
        v___x_819_ = leanh::lean_apply_1(v_h__1_817_, leanh::lean_box(0));
        return v___x_819_;
    } else {
        let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_817_);
        v___x_820_ = leanh::lean_apply_1(v_h__2_818_, leanh::lean_box(0));
        return v___x_820_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_821_: *mut leanh::LeanObject,
    mut v_h__1_822_: *mut leanh::LeanObject,
    mut v_h__2_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_74__boxed_824_: u8 = 0;
    let mut v_res_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_824_ = (leanh::lean_unbox(v_____do__lift_821_) as u8);
    v_res_825_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_824_, v_h__1_822_, v_h__2_823_);
    return v_res_825_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(
    mut v_00_u03b2_826_: *mut leanh::LeanObject,
    mut v_n_827_: *mut leanh::LeanObject,
    mut v_f_828_: *mut leanh::LeanObject,
    mut v_inst_829_: *mut leanh::LeanObject,
    mut v_out_830_: *mut leanh::LeanObject,
    mut v_motive_831_: *mut leanh::LeanObject,
    mut v_____do__lift_832_: u8,
    mut v_h__1_833_: *mut leanh::LeanObject,
    mut v_h__2_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_832_ == 0 {
        let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_834_);
        v___x_835_ = leanh::lean_apply_1(v_h__1_833_, leanh::lean_box(0));
        return v___x_835_;
    } else {
        let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_833_);
        v___x_836_ = leanh::lean_apply_1(v_h__2_834_, leanh::lean_box(0));
        return v___x_836_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_837_: *mut leanh::LeanObject,
    mut v_n_838_: *mut leanh::LeanObject,
    mut v_f_839_: *mut leanh::LeanObject,
    mut v_inst_840_: *mut leanh::LeanObject,
    mut v_out_841_: *mut leanh::LeanObject,
    mut v_motive_842_: *mut leanh::LeanObject,
    mut v_____do__lift_843_: *mut leanh::LeanObject,
    mut v_h__1_844_: *mut leanh::LeanObject,
    mut v_h__2_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_82__boxed_846_: u8 = 0;
    let mut v_res_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_846_ = (leanh::lean_unbox(v_____do__lift_843_) as u8);
    v_res_847_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(v_00_u03b2_837_, v_n_838_, v_f_839_, v_inst_840_, v_out_841_, v_motive_842_, v_____do__lift_82__boxed_846_, v_h__1_844_, v_h__2_845_);
    leanh::lean_dec(v_out_841_);
    leanh::lean_dec(v_inst_840_);
    leanh::lean_dec(v_f_839_);
    return v_res_847_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(
    mut v_x_848_: *mut leanh::LeanObject,
    mut v_h__1_849_: *mut leanh::LeanObject,
    mut v_h__2_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_848_) == 0 {
        let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_850_);
        v___x_851_ = leanh::lean_apply_1(v_h__1_849_, leanh::lean_box(0));
        return v___x_851_;
    } else {
        let mut v_val_852_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_849_);
        v_val_852_ = leanh::lean_ctor_get(v_x_848_, 0);
        leanh::lean_inc(v_val_852_);
        leanh::lean_dec_ref_known(v_x_848_, 1);
        v___x_853_ = leanh::lean_apply_2(v_h__2_850_, v_val_852_, leanh::lean_box(0));
        return v___x_853_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(
    mut v_00_u03b2_x27_854_: *mut leanh::LeanObject,
    mut v_motive_855_: *mut leanh::LeanObject,
    mut v_x_856_: *mut leanh::LeanObject,
    mut v_h__1_857_: *mut leanh::LeanObject,
    mut v_h__2_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_856_) == 0 {
        let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_858_);
        v___x_859_ = leanh::lean_apply_1(v_h__1_857_, leanh::lean_box(0));
        return v___x_859_;
    } else {
        let mut v_val_860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_857_);
        v_val_860_ = leanh::lean_ctor_get(v_x_856_, 0);
        leanh::lean_inc(v_val_860_);
        leanh::lean_dec_ref_known(v_x_856_, 1);
        v___x_861_ = leanh::lean_apply_2(v_h__2_858_, v_val_860_, leanh::lean_box(0));
        return v___x_861_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(
    mut v_x_862_: *mut leanh::LeanObject,
    mut v_h__1_863_: *mut leanh::LeanObject,
    mut v_h__2_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_862_) == 0 {
        let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_864_);
        v___x_865_ = leanh::lean_apply_1(v_h__1_863_, leanh::lean_box(0));
        return v___x_865_;
    } else {
        let mut v_val_866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_863_);
        v_val_866_ = leanh::lean_ctor_get(v_x_862_, 0);
        leanh::lean_inc(v_val_866_);
        leanh::lean_dec_ref_known(v_x_862_, 1);
        v___x_867_ = leanh::lean_apply_2(v_h__2_864_, v_val_866_, leanh::lean_box(0));
        return v___x_867_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(
    mut v_00_u03b3_868_: *mut leanh::LeanObject,
    mut v_motive_869_: *mut leanh::LeanObject,
    mut v_x_870_: *mut leanh::LeanObject,
    mut v_h__1_871_: *mut leanh::LeanObject,
    mut v_h__2_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_870_) == 0 {
        let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_872_);
        v___x_873_ = leanh::lean_apply_1(v_h__1_871_, leanh::lean_box(0));
        return v___x_873_;
    } else {
        let mut v_val_874_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_871_);
        v_val_874_ = leanh::lean_ctor_get(v_x_870_, 0);
        leanh::lean_inc(v_val_874_);
        leanh::lean_dec_ref_known(v_x_870_, 1);
        v___x_875_ = leanh::lean_apply_2(v_h__2_872_, v_val_874_, leanh::lean_box(0));
        return v___x_875_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(
    mut v_x_876_: *mut leanh::LeanObject,
    mut v_h__1_877_: *mut leanh::LeanObject,
    mut v_h__2_878_: *mut leanh::LeanObject,
    mut v_h__3_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_876_) {
        0 => {
            let mut v_it_880_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_881_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_879_);
            leanh::lean_dec(v_h__2_878_);
            v_it_880_ = leanh::lean_ctor_get(v_x_876_, 0);
            leanh::lean_inc(v_it_880_);
            v_out_881_ = leanh::lean_ctor_get(v_x_876_, 1);
            leanh::lean_inc(v_out_881_);
            leanh::lean_dec_ref_known(v_x_876_, 2);
            v___x_882_ = leanh::lean_apply_2(v_h__1_877_, v_it_880_, v_out_881_);
            return v___x_882_;
        }
        1 => {
            let mut v_it_883_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_879_);
            leanh::lean_dec(v_h__1_877_);
            v_it_883_ = leanh::lean_ctor_get(v_x_876_, 0);
            leanh::lean_inc(v_it_883_);
            leanh::lean_dec_ref_known(v_x_876_, 1);
            v___x_884_ = leanh::lean_apply_1(v_h__2_878_, v_it_883_);
            return v___x_884_;
        }
        _ => {
            let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_878_);
            leanh::lean_dec(v_h__1_877_);
            v___x_885_ = leanh::lean_box(0);
            v___x_886_ = leanh::lean_apply_1(v_h__3_879_, v___x_885_);
            return v___x_886_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(
    mut v_00_u03b1_887_: *mut leanh::LeanObject,
    mut v_00_u03b2_888_: *mut leanh::LeanObject,
    mut v_motive_889_: *mut leanh::LeanObject,
    mut v_x_890_: *mut leanh::LeanObject,
    mut v_h__1_891_: *mut leanh::LeanObject,
    mut v_h__2_892_: *mut leanh::LeanObject,
    mut v_h__3_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_890_) {
        0 => {
            let mut v_it_894_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_895_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_893_);
            leanh::lean_dec(v_h__2_892_);
            v_it_894_ = leanh::lean_ctor_get(v_x_890_, 0);
            leanh::lean_inc(v_it_894_);
            v_out_895_ = leanh::lean_ctor_get(v_x_890_, 1);
            leanh::lean_inc(v_out_895_);
            leanh::lean_dec_ref_known(v_x_890_, 2);
            v___x_896_ = leanh::lean_apply_2(v_h__1_891_, v_it_894_, v_out_895_);
            return v___x_896_;
        }
        1 => {
            let mut v_it_897_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_893_);
            leanh::lean_dec(v_h__1_891_);
            v_it_897_ = leanh::lean_ctor_get(v_x_890_, 0);
            leanh::lean_inc(v_it_897_);
            leanh::lean_dec_ref_known(v_x_890_, 1);
            v___x_898_ = leanh::lean_apply_1(v_h__2_892_, v_it_897_);
            return v___x_898_;
        }
        _ => {
            let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_892_);
            leanh::lean_dec(v_h__1_891_);
            v___x_899_ = leanh::lean_box(0);
            v___x_900_ = leanh::lean_apply_1(v_h__3_893_, v___x_899_);
            return v___x_900_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(
    mut v_x_901_: *mut leanh::LeanObject,
    mut v_h__1_902_: *mut leanh::LeanObject,
    mut v_h__2_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_901_) == 0 {
        let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_903_);
        v___x_904_ = leanh::lean_box(0);
        v___x_905_ = leanh::lean_apply_1(v_h__1_902_, v___x_904_);
        return v___x_905_;
    } else {
        let mut v_val_906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_902_);
        v_val_906_ = leanh::lean_ctor_get(v_x_901_, 0);
        leanh::lean_inc(v_val_906_);
        leanh::lean_dec_ref_known(v_x_901_, 1);
        v___x_907_ = leanh::lean_apply_1(v_h__2_903_, v_val_906_);
        return v___x_907_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(
    mut v_00_u03b3_908_: *mut leanh::LeanObject,
    mut v_motive_909_: *mut leanh::LeanObject,
    mut v_x_910_: *mut leanh::LeanObject,
    mut v_h__1_911_: *mut leanh::LeanObject,
    mut v_h__2_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_910_) == 0 {
        let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_912_);
        v___x_913_ = leanh::lean_box(0);
        v___x_914_ = leanh::lean_apply_1(v_h__1_911_, v___x_913_);
        return v___x_914_;
    } else {
        let mut v_val_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_911_);
        v_val_915_ = leanh::lean_ctor_get(v_x_910_, 0);
        leanh::lean_inc(v_val_915_);
        leanh::lean_dec_ref_known(v_x_910_, 1);
        v___x_916_ = leanh::lean_apply_1(v_h__2_912_, v_val_915_);
        return v___x_916_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_917_: *mut leanh::LeanObject,
    mut v_h__1_918_: *mut leanh::LeanObject,
    mut v_h__2_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_917_) == 0 {
        let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_918_);
        v___x_920_ = leanh::lean_box(0);
        v___x_921_ = leanh::lean_apply_1(v_h__2_919_, v___x_920_);
        return v___x_921_;
    } else {
        let mut v_val_922_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_919_);
        v_val_922_ = leanh::lean_ctor_get(v_____do__lift_917_, 0);
        leanh::lean_inc(v_val_922_);
        leanh::lean_dec_ref_known(v_____do__lift_917_, 1);
        v___x_923_ = leanh::lean_apply_1(v_h__1_918_, v_val_922_);
        return v___x_923_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_924_: *mut leanh::LeanObject,
    mut v_motive_925_: *mut leanh::LeanObject,
    mut v_____do__lift_926_: *mut leanh::LeanObject,
    mut v_h__1_927_: *mut leanh::LeanObject,
    mut v_h__2_928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_926_) == 0 {
        let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_927_);
        v___x_929_ = leanh::lean_box(0);
        v___x_930_ = leanh::lean_apply_1(v_h__2_928_, v___x_929_);
        return v___x_930_;
    } else {
        let mut v_val_931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_928_);
        v_val_931_ = leanh::lean_ctor_get(v_____do__lift_926_, 0);
        leanh::lean_inc(v_val_931_);
        leanh::lean_dec_ref_known(v_____do__lift_926_, 1);
        v___x_932_ = leanh::lean_apply_1(v_h__1_927_, v_val_931_);
        return v___x_932_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_933_: *mut leanh::LeanObject,
    mut v_h__1_934_: *mut leanh::LeanObject,
    mut v_h__2_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_933_) == 0 {
        let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_934_);
        v___x_936_ = leanh::lean_box(0);
        v___x_937_ = leanh::lean_apply_1(v_h__2_935_, v___x_936_);
        return v___x_937_;
    } else {
        let mut v_val_938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_935_);
        v_val_938_ = leanh::lean_ctor_get(v_____do__lift_933_, 0);
        leanh::lean_inc(v_val_938_);
        leanh::lean_dec_ref_known(v_____do__lift_933_, 1);
        v___x_939_ = leanh::lean_apply_1(v_h__1_934_, v_val_938_);
        return v___x_939_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_940_: *mut leanh::LeanObject,
    mut v_motive_941_: *mut leanh::LeanObject,
    mut v_____do__lift_942_: *mut leanh::LeanObject,
    mut v_h__1_943_: *mut leanh::LeanObject,
    mut v_h__2_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_942_) == 0 {
        let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_943_);
        v___x_945_ = leanh::lean_box(0);
        v___x_946_ = leanh::lean_apply_1(v_h__2_944_, v___x_945_);
        return v___x_946_;
    } else {
        let mut v_val_947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_944_);
        v_val_947_ = leanh::lean_ctor_get(v_____do__lift_942_, 0);
        leanh::lean_inc(v_val_947_);
        leanh::lean_dec_ref_known(v_____do__lift_942_, 1);
        v___x_948_ = leanh::lean_apply_1(v_h__1_943_, v_val_947_);
        return v___x_948_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_949_: *mut leanh::LeanObject,
    mut v_h__1_950_: *mut leanh::LeanObject,
    mut v_h__2_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_949_) == 1 {
        let mut v_val_952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_951_);
        v_val_952_ = leanh::lean_ctor_get(v_____x_949_, 0);
        leanh::lean_inc(v_val_952_);
        leanh::lean_dec_ref_known(v_____x_949_, 1);
        v___x_953_ = leanh::lean_apply_1(v_h__1_950_, v_val_952_);
        return v___x_953_;
    } else {
        let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_950_);
        v___x_954_ =
            leanh::lean_apply_2(v_h__2_951_, v_____x_949_, leanh::lean_box(0));
        return v___x_954_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_955_: *mut leanh::LeanObject,
    mut v_motive_956_: *mut leanh::LeanObject,
    mut v_____x_957_: *mut leanh::LeanObject,
    mut v_h__1_958_: *mut leanh::LeanObject,
    mut v_h__2_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_957_) == 1 {
        let mut v_val_960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_959_);
        v_val_960_ = leanh::lean_ctor_get(v_____x_957_, 0);
        leanh::lean_inc(v_val_960_);
        leanh::lean_dec_ref_known(v_____x_957_, 1);
        v___x_961_ = leanh::lean_apply_1(v_h__1_958_, v_val_960_);
        return v___x_961_;
    } else {
        let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_958_);
        v___x_962_ =
            leanh::lean_apply_2(v_h__2_959_, v_____x_957_, leanh::lean_box(0));
        return v___x_962_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_963_: *mut leanh::LeanObject,
    mut v_h__1_964_: *mut leanh::LeanObject,
    mut v_h__2_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_963_) == 1 {
        let mut v_val_966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_965_);
        v_val_966_ = leanh::lean_ctor_get(v_____x_963_, 0);
        leanh::lean_inc(v_val_966_);
        leanh::lean_dec_ref_known(v_____x_963_, 1);
        v___x_967_ = leanh::lean_apply_1(v_h__1_964_, v_val_966_);
        return v___x_967_;
    } else {
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_964_);
        v___x_968_ =
            leanh::lean_apply_2(v_h__2_965_, v_____x_963_, leanh::lean_box(0));
        return v___x_968_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_969_: *mut leanh::LeanObject,
    mut v_motive_970_: *mut leanh::LeanObject,
    mut v_____x_971_: *mut leanh::LeanObject,
    mut v_h__1_972_: *mut leanh::LeanObject,
    mut v_h__2_973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_971_) == 1 {
        let mut v_val_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_973_);
        v_val_974_ = leanh::lean_ctor_get(v_____x_971_, 0);
        leanh::lean_inc(v_val_974_);
        leanh::lean_dec_ref_known(v_____x_971_, 1);
        v___x_975_ = leanh::lean_apply_1(v_h__1_972_, v_val_974_);
        return v___x_975_;
    } else {
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_972_);
        v___x_976_ =
            leanh::lean_apply_2(v_h__2_973_, v_____x_971_, leanh::lean_box(0));
        return v___x_976_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_977_: *mut leanh::LeanObject,
    mut v_h__1_978_: *mut leanh::LeanObject,
    mut v_h__2_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_977_) == 0 {
        let mut v_a_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_978_);
        v_a_980_ = leanh::lean_ctor_get(v_____do__lift_977_, 0);
        leanh::lean_inc(v_a_980_);
        leanh::lean_dec_ref_known(v_____do__lift_977_, 1);
        v___x_981_ = leanh::lean_apply_1(v_h__2_979_, v_a_980_);
        return v___x_981_;
    } else {
        let mut v_a_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_979_);
        v_a_982_ = leanh::lean_ctor_get(v_____do__lift_977_, 0);
        leanh::lean_inc(v_a_982_);
        leanh::lean_dec_ref_known(v_____do__lift_977_, 1);
        v___x_983_ = leanh::lean_apply_1(v_h__1_978_, v_a_982_);
        return v___x_983_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_984_: *mut leanh::LeanObject,
    mut v_motive_985_: *mut leanh::LeanObject,
    mut v_____do__lift_986_: *mut leanh::LeanObject,
    mut v_h__1_987_: *mut leanh::LeanObject,
    mut v_h__2_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_986_) == 0 {
        let mut v_a_989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_987_);
        v_a_989_ = leanh::lean_ctor_get(v_____do__lift_986_, 0);
        leanh::lean_inc(v_a_989_);
        leanh::lean_dec_ref_known(v_____do__lift_986_, 1);
        v___x_990_ = leanh::lean_apply_1(v_h__2_988_, v_a_989_);
        return v___x_990_;
    } else {
        let mut v_a_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_988_);
        v_a_991_ = leanh::lean_ctor_get(v_____do__lift_986_, 0);
        leanh::lean_inc(v_a_991_);
        leanh::lean_dec_ref_known(v_____do__lift_986_, 1);
        v___x_992_ = leanh::lean_apply_1(v_h__1_987_, v_a_991_);
        return v___x_992_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_993_: *mut leanh::LeanObject,
    mut v_h__1_994_: *mut leanh::LeanObject,
    mut v_h__2_995_: *mut leanh::LeanObject,
    mut v_h__3_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_993_) {
        0 => {
            let mut v_it_997_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_998_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_996_);
            leanh::lean_dec(v_h__2_995_);
            v_it_997_ = leanh::lean_ctor_get(v_x_993_, 0);
            leanh::lean_inc(v_it_997_);
            v_out_998_ = leanh::lean_ctor_get(v_x_993_, 1);
            leanh::lean_inc(v_out_998_);
            leanh::lean_dec_ref_known(v_x_993_, 2);
            v___x_999_ = leanh::lean_apply_3(
                v_h__1_994_,
                v_it_997_,
                v_out_998_,
                leanh::lean_box(0),
            );
            return v___x_999_;
        }
        1 => {
            let mut v_it_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_996_);
            leanh::lean_dec(v_h__1_994_);
            v_it_1000_ = leanh::lean_ctor_get(v_x_993_, 0);
            leanh::lean_inc(v_it_1000_);
            leanh::lean_dec_ref_known(v_x_993_, 1);
            v___x_1001_ =
                leanh::lean_apply_2(v_h__2_995_, v_it_1000_, leanh::lean_box(0));
            return v___x_1001_;
        }
        _ => {
            let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_995_);
            leanh::lean_dec(v_h__1_994_);
            v___x_1002_ = leanh::lean_apply_1(v_h__3_996_, leanh::lean_box(0));
            return v___x_1002_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_1003_: *mut leanh::LeanObject,
    mut v_00_u03b2_1004_: *mut leanh::LeanObject,
    mut v_m_1005_: *mut leanh::LeanObject,
    mut v_inst_1006_: *mut leanh::LeanObject,
    mut v_it_1007_: *mut leanh::LeanObject,
    mut v_motive_1008_: *mut leanh::LeanObject,
    mut v_x_1009_: *mut leanh::LeanObject,
    mut v_h__1_1010_: *mut leanh::LeanObject,
    mut v_h__2_1011_: *mut leanh::LeanObject,
    mut v_h__3_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1009_) {
        0 => {
            let mut v_it_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1012_);
            leanh::lean_dec(v_h__2_1011_);
            v_it_1013_ = leanh::lean_ctor_get(v_x_1009_, 0);
            leanh::lean_inc(v_it_1013_);
            v_out_1014_ = leanh::lean_ctor_get(v_x_1009_, 1);
            leanh::lean_inc(v_out_1014_);
            leanh::lean_dec_ref_known(v_x_1009_, 2);
            v___x_1015_ = leanh::lean_apply_3(
                v_h__1_1010_,
                v_it_1013_,
                v_out_1014_,
                leanh::lean_box(0),
            );
            return v___x_1015_;
        }
        1 => {
            let mut v_it_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1012_);
            leanh::lean_dec(v_h__1_1010_);
            v_it_1016_ = leanh::lean_ctor_get(v_x_1009_, 0);
            leanh::lean_inc(v_it_1016_);
            leanh::lean_dec_ref_known(v_x_1009_, 1);
            v___x_1017_ =
                leanh::lean_apply_2(v_h__2_1011_, v_it_1016_, leanh::lean_box(0));
            return v___x_1017_;
        }
        _ => {
            let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1011_);
            leanh::lean_dec(v_h__1_1010_);
            v___x_1018_ = leanh::lean_apply_1(v_h__3_1012_, leanh::lean_box(0));
            return v___x_1018_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_1019_: *mut leanh::LeanObject,
    mut v_00_u03b2_1020_: *mut leanh::LeanObject,
    mut v_m_1021_: *mut leanh::LeanObject,
    mut v_inst_1022_: *mut leanh::LeanObject,
    mut v_it_1023_: *mut leanh::LeanObject,
    mut v_motive_1024_: *mut leanh::LeanObject,
    mut v_x_1025_: *mut leanh::LeanObject,
    mut v_h__1_1026_: *mut leanh::LeanObject,
    mut v_h__2_1027_: *mut leanh::LeanObject,
    mut v_h__3_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_1019_, v_00_u03b2_1020_, v_m_1021_, v_inst_1022_, v_it_1023_, v_motive_1024_, v_x_1025_, v_h__1_1026_, v_h__2_1027_, v_h__3_1028_);
    leanh::lean_dec(v_it_1023_);
    leanh::lean_dec(v_inst_1022_);
    return v_res_1029_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_1030_: *mut leanh::LeanObject,
    mut v_h__1_1031_: *mut leanh::LeanObject,
    mut v_h__2_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1030_) == 0 {
        let mut v_a_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1031_);
        v_a_1033_ = leanh::lean_ctor_get(v_____do__lift_1030_, 0);
        leanh::lean_inc(v_a_1033_);
        leanh::lean_dec_ref_known(v_____do__lift_1030_, 1);
        v___x_1034_ = leanh::lean_apply_1(v_h__2_1032_, v_a_1033_);
        return v___x_1034_;
    } else {
        let mut v_a_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1032_);
        v_a_1035_ = leanh::lean_ctor_get(v_____do__lift_1030_, 0);
        leanh::lean_inc(v_a_1035_);
        leanh::lean_dec_ref_known(v_____do__lift_1030_, 1);
        v___x_1036_ = leanh::lean_apply_1(v_h__1_1031_, v_a_1035_);
        return v___x_1036_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_1037_: *mut leanh::LeanObject,
    mut v_motive_1038_: *mut leanh::LeanObject,
    mut v_____do__lift_1039_: *mut leanh::LeanObject,
    mut v_h__1_1040_: *mut leanh::LeanObject,
    mut v_h__2_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1039_) == 0 {
        let mut v_a_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1040_);
        v_a_1042_ = leanh::lean_ctor_get(v_____do__lift_1039_, 0);
        leanh::lean_inc(v_a_1042_);
        leanh::lean_dec_ref_known(v_____do__lift_1039_, 1);
        v___x_1043_ = leanh::lean_apply_1(v_h__2_1041_, v_a_1042_);
        return v___x_1043_;
    } else {
        let mut v_a_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1041_);
        v_a_1044_ = leanh::lean_ctor_get(v_____do__lift_1039_, 0);
        leanh::lean_inc(v_a_1044_);
        leanh::lean_dec_ref_known(v_____do__lift_1039_, 1);
        v___x_1045_ = leanh::lean_apply_1(v_h__1_1040_, v_a_1044_);
        return v___x_1045_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_1046_: *mut leanh::LeanObject,
    mut v_h__1_1047_: *mut leanh::LeanObject,
    mut v_h__2_1048_: *mut leanh::LeanObject,
    mut v_h__3_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1046_) {
        0 => {
            let mut v_it_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1049_);
            leanh::lean_dec(v_h__2_1048_);
            v_it_1050_ = leanh::lean_ctor_get(v_x_1046_, 0);
            leanh::lean_inc(v_it_1050_);
            v_out_1051_ = leanh::lean_ctor_get(v_x_1046_, 1);
            leanh::lean_inc(v_out_1051_);
            leanh::lean_dec_ref_known(v_x_1046_, 2);
            v___x_1052_ = leanh::lean_apply_2(v_h__1_1047_, v_it_1050_, v_out_1051_);
            return v___x_1052_;
        }
        1 => {
            let mut v_it_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1049_);
            leanh::lean_dec(v_h__1_1047_);
            v_it_1053_ = leanh::lean_ctor_get(v_x_1046_, 0);
            leanh::lean_inc(v_it_1053_);
            leanh::lean_dec_ref_known(v_x_1046_, 1);
            v___x_1054_ = leanh::lean_apply_1(v_h__2_1048_, v_it_1053_);
            return v___x_1054_;
        }
        _ => {
            let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1048_);
            leanh::lean_dec(v_h__1_1047_);
            v___x_1055_ = leanh::lean_box(0);
            v___x_1056_ = leanh::lean_apply_1(v_h__3_1049_, v___x_1055_);
            return v___x_1056_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_1057_: *mut leanh::LeanObject,
    mut v_00_u03b2_1058_: *mut leanh::LeanObject,
    mut v_motive_1059_: *mut leanh::LeanObject,
    mut v_x_1060_: *mut leanh::LeanObject,
    mut v_h__1_1061_: *mut leanh::LeanObject,
    mut v_h__2_1062_: *mut leanh::LeanObject,
    mut v_h__3_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1060_) {
        0 => {
            let mut v_it_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1063_);
            leanh::lean_dec(v_h__2_1062_);
            v_it_1064_ = leanh::lean_ctor_get(v_x_1060_, 0);
            leanh::lean_inc(v_it_1064_);
            v_out_1065_ = leanh::lean_ctor_get(v_x_1060_, 1);
            leanh::lean_inc(v_out_1065_);
            leanh::lean_dec_ref_known(v_x_1060_, 2);
            v___x_1066_ = leanh::lean_apply_2(v_h__1_1061_, v_it_1064_, v_out_1065_);
            return v___x_1066_;
        }
        1 => {
            let mut v_it_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1063_);
            leanh::lean_dec(v_h__1_1061_);
            v_it_1067_ = leanh::lean_ctor_get(v_x_1060_, 0);
            leanh::lean_inc(v_it_1067_);
            leanh::lean_dec_ref_known(v_x_1060_, 1);
            v___x_1068_ = leanh::lean_apply_1(v_h__2_1062_, v_it_1067_);
            return v___x_1068_;
        }
        _ => {
            let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1062_);
            leanh::lean_dec(v_h__1_1061_);
            v___x_1069_ = leanh::lean_box(0);
            v___x_1070_ = leanh::lean_apply_1(v_h__3_1063_, v___x_1069_);
            return v___x_1070_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
}