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
    mut v_x_536_: *mut crate::leanh::LeanObject,
    mut v_h__1_537_: *mut crate::leanh::LeanObject,
    mut v_h__2_538_: *mut crate::leanh::LeanObject,
    mut v_h__3_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_536_) {
        0 => {
            let mut v_it_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_539_);
            crate::leanh::lean_dec(v_h__2_538_);
            v_it_540_ = crate::leanh::lean_ctor_get(v_x_536_, 0);
            crate::leanh::lean_inc(v_it_540_);
            v_out_541_ = crate::leanh::lean_ctor_get(v_x_536_, 1);
            crate::leanh::lean_inc(v_out_541_);
            crate::leanh::lean_dec_ref_known(v_x_536_, 2);
            v___x_542_ = crate::leanh::lean_apply_3(
                v_h__1_537_,
                v_it_540_,
                v_out_541_,
                crate::leanh::lean_box(0),
            );
            return v___x_542_;
        }
        1 => {
            let mut v_it_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_539_);
            crate::leanh::lean_dec(v_h__1_537_);
            v_it_543_ = crate::leanh::lean_ctor_get(v_x_536_, 0);
            crate::leanh::lean_inc(v_it_543_);
            crate::leanh::lean_dec_ref_known(v_x_536_, 1);
            v___x_544_ =
                crate::leanh::lean_apply_2(v_h__2_538_, v_it_543_, crate::leanh::lean_box(0));
            return v___x_544_;
        }
        _ => {
            let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_538_);
            crate::leanh::lean_dec(v_h__1_537_);
            v___x_545_ = crate::leanh::lean_apply_1(v_h__3_539_, crate::leanh::lean_box(0));
            return v___x_545_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_546_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_547_: *mut crate::leanh::LeanObject,
    mut v_m_548_: *mut crate::leanh::LeanObject,
    mut v_inst_549_: *mut crate::leanh::LeanObject,
    mut v_it_550_: *mut crate::leanh::LeanObject,
    mut v_motive_551_: *mut crate::leanh::LeanObject,
    mut v_x_552_: *mut crate::leanh::LeanObject,
    mut v_h__1_553_: *mut crate::leanh::LeanObject,
    mut v_h__2_554_: *mut crate::leanh::LeanObject,
    mut v_h__3_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_552_) {
        0 => {
            let mut v_it_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_555_);
            crate::leanh::lean_dec(v_h__2_554_);
            v_it_556_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
            crate::leanh::lean_inc(v_it_556_);
            v_out_557_ = crate::leanh::lean_ctor_get(v_x_552_, 1);
            crate::leanh::lean_inc(v_out_557_);
            crate::leanh::lean_dec_ref_known(v_x_552_, 2);
            v___x_558_ = crate::leanh::lean_apply_3(
                v_h__1_553_,
                v_it_556_,
                v_out_557_,
                crate::leanh::lean_box(0),
            );
            return v___x_558_;
        }
        1 => {
            let mut v_it_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_555_);
            crate::leanh::lean_dec(v_h__1_553_);
            v_it_559_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
            crate::leanh::lean_inc(v_it_559_);
            crate::leanh::lean_dec_ref_known(v_x_552_, 1);
            v___x_560_ =
                crate::leanh::lean_apply_2(v_h__2_554_, v_it_559_, crate::leanh::lean_box(0));
            return v___x_560_;
        }
        _ => {
            let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_554_);
            crate::leanh::lean_dec(v_h__1_553_);
            v___x_561_ = crate::leanh::lean_apply_1(v_h__3_555_, crate::leanh::lean_box(0));
            return v___x_561_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_562_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_563_: *mut crate::leanh::LeanObject,
    mut v_m_564_: *mut crate::leanh::LeanObject,
    mut v_inst_565_: *mut crate::leanh::LeanObject,
    mut v_it_566_: *mut crate::leanh::LeanObject,
    mut v_motive_567_: *mut crate::leanh::LeanObject,
    mut v_x_568_: *mut crate::leanh::LeanObject,
    mut v_h__1_569_: *mut crate::leanh::LeanObject,
    mut v_h__2_570_: *mut crate::leanh::LeanObject,
    mut v_h__3_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_562_, v_00_u03b2_563_, v_m_564_, v_inst_565_, v_it_566_, v_motive_567_, v_x_568_, v_h__1_569_, v_h__2_570_, v_h__3_571_);
    crate::leanh::lean_dec(v_it_566_);
    crate::leanh::lean_dec(v_inst_565_);
    return v_res_572_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_573_: *mut crate::leanh::LeanObject,
    mut v_h__1_574_: *mut crate::leanh::LeanObject,
    mut v_h__2_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_573_) == 0 {
        let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_575_);
        v___x_576_ = crate::leanh::lean_apply_1(v_h__1_574_, crate::leanh::lean_box(0));
        return v___x_576_;
    } else {
        let mut v_val_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_574_);
        v_val_577_ = crate::leanh::lean_ctor_get(v_____do__lift_573_, 0);
        crate::leanh::lean_inc(v_val_577_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_573_, 1);
        v___x_578_ = crate::leanh::lean_apply_2(v_h__2_575_, v_val_577_, crate::leanh::lean_box(0));
        return v___x_578_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_580_: *mut crate::leanh::LeanObject,
    mut v_n_581_: *mut crate::leanh::LeanObject,
    mut v_f_582_: *mut crate::leanh::LeanObject,
    mut v_out_583_: *mut crate::leanh::LeanObject,
    mut v_motive_584_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_585_: *mut crate::leanh::LeanObject,
    mut v_h__1_586_: *mut crate::leanh::LeanObject,
    mut v_h__2_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_585_) == 0 {
        let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_587_);
        v___x_588_ = crate::leanh::lean_apply_1(v_h__1_586_, crate::leanh::lean_box(0));
        return v___x_588_;
    } else {
        let mut v_val_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_586_);
        v_val_589_ = crate::leanh::lean_ctor_get(v_____do__lift_585_, 0);
        crate::leanh::lean_inc(v_val_589_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_585_, 1);
        v___x_590_ = crate::leanh::lean_apply_2(v_h__2_587_, v_val_589_, crate::leanh::lean_box(0));
        return v___x_590_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_591_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_592_: *mut crate::leanh::LeanObject,
    mut v_n_593_: *mut crate::leanh::LeanObject,
    mut v_f_594_: *mut crate::leanh::LeanObject,
    mut v_out_595_: *mut crate::leanh::LeanObject,
    mut v_motive_596_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_597_: *mut crate::leanh::LeanObject,
    mut v_h__1_598_: *mut crate::leanh::LeanObject,
    mut v_h__2_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_591_, v_00_u03b2_x27_592_, v_n_593_, v_f_594_, v_out_595_, v_motive_596_, v_____do__lift_597_, v_h__1_598_, v_h__2_599_);
    crate::leanh::lean_dec(v_out_595_);
    crate::leanh::lean_dec(v_f_594_);
    return v_res_600_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_601_: *mut crate::leanh::LeanObject,
    mut v_h__1_602_: *mut crate::leanh::LeanObject,
    mut v_h__2_603_: *mut crate::leanh::LeanObject,
    mut v_h__3_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_601_) {
        0 => {
            let mut v_it_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_604_);
            crate::leanh::lean_dec(v_h__2_603_);
            v_it_605_ = crate::leanh::lean_ctor_get(v_x_601_, 0);
            crate::leanh::lean_inc(v_it_605_);
            v_out_606_ = crate::leanh::lean_ctor_get(v_x_601_, 1);
            crate::leanh::lean_inc(v_out_606_);
            crate::leanh::lean_dec_ref_known(v_x_601_, 2);
            v___x_607_ = crate::leanh::lean_apply_3(
                v_h__1_602_,
                v_it_605_,
                v_out_606_,
                crate::leanh::lean_box(0),
            );
            return v___x_607_;
        }
        1 => {
            let mut v_it_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_604_);
            crate::leanh::lean_dec(v_h__1_602_);
            v_it_608_ = crate::leanh::lean_ctor_get(v_x_601_, 0);
            crate::leanh::lean_inc(v_it_608_);
            crate::leanh::lean_dec_ref_known(v_x_601_, 1);
            v___x_609_ =
                crate::leanh::lean_apply_2(v_h__2_603_, v_it_608_, crate::leanh::lean_box(0));
            return v___x_609_;
        }
        _ => {
            let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_603_);
            crate::leanh::lean_dec(v_h__1_602_);
            v___x_610_ = crate::leanh::lean_apply_1(v_h__3_604_, crate::leanh::lean_box(0));
            return v___x_610_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_611_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_612_: *mut crate::leanh::LeanObject,
    mut v_inst_613_: *mut crate::leanh::LeanObject,
    mut v_it_614_: *mut crate::leanh::LeanObject,
    mut v_motive_615_: *mut crate::leanh::LeanObject,
    mut v_x_616_: *mut crate::leanh::LeanObject,
    mut v_h__1_617_: *mut crate::leanh::LeanObject,
    mut v_h__2_618_: *mut crate::leanh::LeanObject,
    mut v_h__3_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_616_) {
        0 => {
            let mut v_it_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_619_);
            crate::leanh::lean_dec(v_h__2_618_);
            v_it_620_ = crate::leanh::lean_ctor_get(v_x_616_, 0);
            crate::leanh::lean_inc(v_it_620_);
            v_out_621_ = crate::leanh::lean_ctor_get(v_x_616_, 1);
            crate::leanh::lean_inc(v_out_621_);
            crate::leanh::lean_dec_ref_known(v_x_616_, 2);
            v___x_622_ = crate::leanh::lean_apply_3(
                v_h__1_617_,
                v_it_620_,
                v_out_621_,
                crate::leanh::lean_box(0),
            );
            return v___x_622_;
        }
        1 => {
            let mut v_it_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_619_);
            crate::leanh::lean_dec(v_h__1_617_);
            v_it_623_ = crate::leanh::lean_ctor_get(v_x_616_, 0);
            crate::leanh::lean_inc(v_it_623_);
            crate::leanh::lean_dec_ref_known(v_x_616_, 1);
            v___x_624_ =
                crate::leanh::lean_apply_2(v_h__2_618_, v_it_623_, crate::leanh::lean_box(0));
            return v___x_624_;
        }
        _ => {
            let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_618_);
            crate::leanh::lean_dec(v_h__1_617_);
            v___x_625_ = crate::leanh::lean_apply_1(v_h__3_619_, crate::leanh::lean_box(0));
            return v___x_625_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_626_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_627_: *mut crate::leanh::LeanObject,
    mut v_inst_628_: *mut crate::leanh::LeanObject,
    mut v_it_629_: *mut crate::leanh::LeanObject,
    mut v_motive_630_: *mut crate::leanh::LeanObject,
    mut v_x_631_: *mut crate::leanh::LeanObject,
    mut v_h__1_632_: *mut crate::leanh::LeanObject,
    mut v_h__2_633_: *mut crate::leanh::LeanObject,
    mut v_h__3_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_635_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_626_, v_00_u03b2_627_, v_inst_628_, v_it_629_, v_motive_630_, v_x_631_, v_h__1_632_, v_h__2_633_, v_h__3_634_);
    crate::leanh::lean_dec(v_it_629_);
    crate::leanh::lean_dec(v_inst_628_);
    return v_res_635_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_636_: *mut crate::leanh::LeanObject,
    mut v_h__1_637_: *mut crate::leanh::LeanObject,
    mut v_h__2_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_636_) == 0 {
        let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_638_);
        v___x_639_ = crate::leanh::lean_apply_1(v_h__1_637_, crate::leanh::lean_box(0));
        return v___x_639_;
    } else {
        let mut v_val_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_637_);
        v_val_640_ = crate::leanh::lean_ctor_get(v_____do__lift_636_, 0);
        crate::leanh::lean_inc(v_val_640_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_636_, 1);
        v___x_641_ = crate::leanh::lean_apply_2(v_h__2_638_, v_val_640_, crate::leanh::lean_box(0));
        return v___x_641_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_642_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_643_: *mut crate::leanh::LeanObject,
    mut v_n_644_: *mut crate::leanh::LeanObject,
    mut v_f_645_: *mut crate::leanh::LeanObject,
    mut v_out_646_: *mut crate::leanh::LeanObject,
    mut v_motive_647_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_648_: *mut crate::leanh::LeanObject,
    mut v_h__1_649_: *mut crate::leanh::LeanObject,
    mut v_h__2_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_648_) == 0 {
        let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_650_);
        v___x_651_ = crate::leanh::lean_apply_1(v_h__1_649_, crate::leanh::lean_box(0));
        return v___x_651_;
    } else {
        let mut v_val_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_649_);
        v_val_652_ = crate::leanh::lean_ctor_get(v_____do__lift_648_, 0);
        crate::leanh::lean_inc(v_val_652_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_648_, 1);
        v___x_653_ = crate::leanh::lean_apply_2(v_h__2_650_, v_val_652_, crate::leanh::lean_box(0));
        return v___x_653_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_654_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_655_: *mut crate::leanh::LeanObject,
    mut v_n_656_: *mut crate::leanh::LeanObject,
    mut v_f_657_: *mut crate::leanh::LeanObject,
    mut v_out_658_: *mut crate::leanh::LeanObject,
    mut v_motive_659_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_660_: *mut crate::leanh::LeanObject,
    mut v_h__1_661_: *mut crate::leanh::LeanObject,
    mut v_h__2_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_654_, v_00_u03b3_655_, v_n_656_, v_f_657_, v_out_658_, v_motive_659_, v_____do__lift_660_, v_h__1_661_, v_h__2_662_);
    crate::leanh::lean_dec(v_out_658_);
    crate::leanh::lean_dec(v_f_657_);
    return v_res_663_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_664_: u8,
    mut v_h__1_665_: *mut crate::leanh::LeanObject,
    mut v_h__2_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_664_ == 0 {
        let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_666_);
        v___x_667_ = crate::leanh::lean_apply_1(v_h__1_665_, crate::leanh::lean_box(0));
        return v___x_667_;
    } else {
        let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_665_);
        v___x_668_ = crate::leanh::lean_apply_1(v_h__2_666_, crate::leanh::lean_box(0));
        return v___x_668_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_669_: *mut crate::leanh::LeanObject,
    mut v_h__1_670_: *mut crate::leanh::LeanObject,
    mut v_h__2_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_72__boxed_672_: u8 = 0;
    let mut v_res_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_672_ = (crate::leanh::lean_unbox(v_____do__lift_669_) as u8);
    v_res_673_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_672_, v_h__1_670_, v_h__2_671_);
    return v_res_673_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_674_: *mut crate::leanh::LeanObject,
    mut v_n_675_: *mut crate::leanh::LeanObject,
    mut v_f_676_: *mut crate::leanh::LeanObject,
    mut v_out_677_: *mut crate::leanh::LeanObject,
    mut v_motive_678_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_679_: u8,
    mut v_h__1_680_: *mut crate::leanh::LeanObject,
    mut v_h__2_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_679_ == 0 {
        let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_681_);
        v___x_682_ = crate::leanh::lean_apply_1(v_h__1_680_, crate::leanh::lean_box(0));
        return v___x_682_;
    } else {
        let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_680_);
        v___x_683_ = crate::leanh::lean_apply_1(v_h__2_681_, crate::leanh::lean_box(0));
        return v___x_683_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_684_: *mut crate::leanh::LeanObject,
    mut v_n_685_: *mut crate::leanh::LeanObject,
    mut v_f_686_: *mut crate::leanh::LeanObject,
    mut v_out_687_: *mut crate::leanh::LeanObject,
    mut v_motive_688_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_689_: *mut crate::leanh::LeanObject,
    mut v_h__1_690_: *mut crate::leanh::LeanObject,
    mut v_h__2_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_79__boxed_692_: u8 = 0;
    let mut v_res_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_692_ = (crate::leanh::lean_unbox(v_____do__lift_689_) as u8);
    v_res_693_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_684_, v_n_685_, v_f_686_, v_out_687_, v_motive_688_, v_____do__lift_79__boxed_692_, v_h__1_690_, v_h__2_691_);
    crate::leanh::lean_dec(v_out_687_);
    crate::leanh::lean_dec(v_f_686_);
    return v_res_693_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_694_: u8,
    mut v_h__1_695_: *mut crate::leanh::LeanObject,
    mut v_h__2_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_694_ == 0 {
        let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_696_);
        v___x_697_ = crate::leanh::lean_apply_1(v_h__1_695_, crate::leanh::lean_box(0));
        return v___x_697_;
    } else {
        let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_695_);
        v___x_698_ = crate::leanh::lean_apply_1(v_h__2_696_, crate::leanh::lean_box(0));
        return v___x_698_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_699_: *mut crate::leanh::LeanObject,
    mut v_h__1_700_: *mut crate::leanh::LeanObject,
    mut v_h__2_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_72__boxed_702_: u8 = 0;
    let mut v_res_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_702_ = (crate::leanh::lean_unbox(v_____do__lift_699_) as u8);
    v_res_703_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_702_, v_h__1_700_, v_h__2_701_);
    return v_res_703_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(
    mut v_00_u03b2_704_: *mut crate::leanh::LeanObject,
    mut v_n_705_: *mut crate::leanh::LeanObject,
    mut v_f_706_: *mut crate::leanh::LeanObject,
    mut v_out_707_: *mut crate::leanh::LeanObject,
    mut v_motive_708_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_709_: u8,
    mut v_h__1_710_: *mut crate::leanh::LeanObject,
    mut v_h__2_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_709_ == 0 {
        let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_711_);
        v___x_712_ = crate::leanh::lean_apply_1(v_h__1_710_, crate::leanh::lean_box(0));
        return v___x_712_;
    } else {
        let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_710_);
        v___x_713_ = crate::leanh::lean_apply_1(v_h__2_711_, crate::leanh::lean_box(0));
        return v___x_713_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_714_: *mut crate::leanh::LeanObject,
    mut v_n_715_: *mut crate::leanh::LeanObject,
    mut v_f_716_: *mut crate::leanh::LeanObject,
    mut v_out_717_: *mut crate::leanh::LeanObject,
    mut v_motive_718_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_719_: *mut crate::leanh::LeanObject,
    mut v_h__1_720_: *mut crate::leanh::LeanObject,
    mut v_h__2_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_79__boxed_722_: u8 = 0;
    let mut v_res_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_722_ = (crate::leanh::lean_unbox(v_____do__lift_719_) as u8);
    v_res_723_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_714_, v_n_715_, v_f_716_, v_out_717_, v_motive_718_, v_____do__lift_79__boxed_722_, v_h__1_720_, v_h__2_721_);
    crate::leanh::lean_dec(v_out_717_);
    crate::leanh::lean_dec(v_f_716_);
    return v_res_723_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_724_: *mut crate::leanh::LeanObject,
    mut v_h__1_725_: *mut crate::leanh::LeanObject,
    mut v_h__2_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_724_) == 0 {
        let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_726_);
        v___x_727_ = crate::leanh::lean_apply_1(v_h__1_725_, crate::leanh::lean_box(0));
        return v___x_727_;
    } else {
        let mut v_val_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_725_);
        v_val_728_ = crate::leanh::lean_ctor_get(v_____do__lift_724_, 0);
        crate::leanh::lean_inc(v_val_728_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_724_, 1);
        v___x_729_ = crate::leanh::lean_apply_2(v_h__2_726_, v_val_728_, crate::leanh::lean_box(0));
        return v___x_729_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_730_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_731_: *mut crate::leanh::LeanObject,
    mut v_n_732_: *mut crate::leanh::LeanObject,
    mut v_f_733_: *mut crate::leanh::LeanObject,
    mut v_inst_734_: *mut crate::leanh::LeanObject,
    mut v_out_735_: *mut crate::leanh::LeanObject,
    mut v_motive_736_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_737_: *mut crate::leanh::LeanObject,
    mut v_h__1_738_: *mut crate::leanh::LeanObject,
    mut v_h__2_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_737_) == 0 {
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_739_);
        v___x_740_ = crate::leanh::lean_apply_1(v_h__1_738_, crate::leanh::lean_box(0));
        return v___x_740_;
    } else {
        let mut v_val_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_738_);
        v_val_741_ = crate::leanh::lean_ctor_get(v_____do__lift_737_, 0);
        crate::leanh::lean_inc(v_val_741_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_737_, 1);
        v___x_742_ = crate::leanh::lean_apply_2(v_h__2_739_, v_val_741_, crate::leanh::lean_box(0));
        return v___x_742_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_743_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_744_: *mut crate::leanh::LeanObject,
    mut v_n_745_: *mut crate::leanh::LeanObject,
    mut v_f_746_: *mut crate::leanh::LeanObject,
    mut v_inst_747_: *mut crate::leanh::LeanObject,
    mut v_out_748_: *mut crate::leanh::LeanObject,
    mut v_motive_749_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_750_: *mut crate::leanh::LeanObject,
    mut v_h__1_751_: *mut crate::leanh::LeanObject,
    mut v_h__2_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_743_, v_00_u03b2_x27_744_, v_n_745_, v_f_746_, v_inst_747_, v_out_748_, v_motive_749_, v_____do__lift_750_, v_h__1_751_, v_h__2_752_);
    crate::leanh::lean_dec(v_out_748_);
    crate::leanh::lean_dec(v_inst_747_);
    crate::leanh::lean_dec(v_f_746_);
    return v_res_753_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_754_: *mut crate::leanh::LeanObject,
    mut v_h__1_755_: *mut crate::leanh::LeanObject,
    mut v_h__2_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_754_) == 0 {
        let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_756_);
        v___x_757_ = crate::leanh::lean_apply_1(v_h__1_755_, crate::leanh::lean_box(0));
        return v___x_757_;
    } else {
        let mut v_val_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_755_);
        v_val_758_ = crate::leanh::lean_ctor_get(v_____do__lift_754_, 0);
        crate::leanh::lean_inc(v_val_758_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_754_, 1);
        v___x_759_ = crate::leanh::lean_apply_2(v_h__2_756_, v_val_758_, crate::leanh::lean_box(0));
        return v___x_759_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(
    mut v_00_u03b2_760_: *mut crate::leanh::LeanObject,
    mut v_n_761_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_762_: *mut crate::leanh::LeanObject,
    mut v_f_763_: *mut crate::leanh::LeanObject,
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_out_765_: *mut crate::leanh::LeanObject,
    mut v_motive_766_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_767_: *mut crate::leanh::LeanObject,
    mut v_h__1_768_: *mut crate::leanh::LeanObject,
    mut v_h__2_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_767_) == 0 {
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_769_);
        v___x_770_ = crate::leanh::lean_apply_1(v_h__1_768_, crate::leanh::lean_box(0));
        return v___x_770_;
    } else {
        let mut v_val_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_768_);
        v_val_771_ = crate::leanh::lean_ctor_get(v_____do__lift_767_, 0);
        crate::leanh::lean_inc(v_val_771_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_767_, 1);
        v___x_772_ = crate::leanh::lean_apply_2(v_h__2_769_, v_val_771_, crate::leanh::lean_box(0));
        return v___x_772_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(
    mut v_00_u03b2_773_: *mut crate::leanh::LeanObject,
    mut v_n_774_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_775_: *mut crate::leanh::LeanObject,
    mut v_f_776_: *mut crate::leanh::LeanObject,
    mut v_inst_777_: *mut crate::leanh::LeanObject,
    mut v_out_778_: *mut crate::leanh::LeanObject,
    mut v_motive_779_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_780_: *mut crate::leanh::LeanObject,
    mut v_h__1_781_: *mut crate::leanh::LeanObject,
    mut v_h__2_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(v_00_u03b2_773_, v_n_774_, v_00_u03b2_x27_775_, v_f_776_, v_inst_777_, v_out_778_, v_motive_779_, v_____do__lift_780_, v_h__1_781_, v_h__2_782_);
    crate::leanh::lean_dec(v_out_778_);
    crate::leanh::lean_dec(v_inst_777_);
    crate::leanh::lean_dec(v_f_776_);
    return v_res_783_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_784_: u8,
    mut v_h__1_785_: *mut crate::leanh::LeanObject,
    mut v_h__2_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_784_ == 0 {
        let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_786_);
        v___x_787_ = crate::leanh::lean_apply_1(v_h__1_785_, crate::leanh::lean_box(0));
        return v___x_787_;
    } else {
        let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_785_);
        v___x_788_ = crate::leanh::lean_apply_1(v_h__2_786_, crate::leanh::lean_box(0));
        return v___x_788_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_789_: *mut crate::leanh::LeanObject,
    mut v_h__1_790_: *mut crate::leanh::LeanObject,
    mut v_h__2_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_74__boxed_792_: u8 = 0;
    let mut v_res_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_792_ = (crate::leanh::lean_unbox(v_____do__lift_789_) as u8);
    v_res_793_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_792_, v_h__1_790_, v_h__2_791_);
    return v_res_793_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(
    mut v_00_u03b2_794_: *mut crate::leanh::LeanObject,
    mut v_n_795_: *mut crate::leanh::LeanObject,
    mut v_f_796_: *mut crate::leanh::LeanObject,
    mut v_inst_797_: *mut crate::leanh::LeanObject,
    mut v_out_798_: *mut crate::leanh::LeanObject,
    mut v_motive_799_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_800_: u8,
    mut v_h__1_801_: *mut crate::leanh::LeanObject,
    mut v_h__2_802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_800_ == 0 {
        let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_802_);
        v___x_803_ = crate::leanh::lean_apply_1(v_h__1_801_, crate::leanh::lean_box(0));
        return v___x_803_;
    } else {
        let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_801_);
        v___x_804_ = crate::leanh::lean_apply_1(v_h__2_802_, crate::leanh::lean_box(0));
        return v___x_804_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_805_: *mut crate::leanh::LeanObject,
    mut v_n_806_: *mut crate::leanh::LeanObject,
    mut v_f_807_: *mut crate::leanh::LeanObject,
    mut v_inst_808_: *mut crate::leanh::LeanObject,
    mut v_out_809_: *mut crate::leanh::LeanObject,
    mut v_motive_810_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_811_: *mut crate::leanh::LeanObject,
    mut v_h__1_812_: *mut crate::leanh::LeanObject,
    mut v_h__2_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_82__boxed_814_: u8 = 0;
    let mut v_res_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_814_ = (crate::leanh::lean_unbox(v_____do__lift_811_) as u8);
    v_res_815_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_805_, v_n_806_, v_f_807_, v_inst_808_, v_out_809_, v_motive_810_, v_____do__lift_82__boxed_814_, v_h__1_812_, v_h__2_813_);
    crate::leanh::lean_dec(v_out_809_);
    crate::leanh::lean_dec(v_inst_808_);
    crate::leanh::lean_dec(v_f_807_);
    return v_res_815_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(
    mut v_____do__lift_816_: u8,
    mut v_h__1_817_: *mut crate::leanh::LeanObject,
    mut v_h__2_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_816_ == 0 {
        let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_818_);
        v___x_819_ = crate::leanh::lean_apply_1(v_h__1_817_, crate::leanh::lean_box(0));
        return v___x_819_;
    } else {
        let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_817_);
        v___x_820_ = crate::leanh::lean_apply_1(v_h__2_818_, crate::leanh::lean_box(0));
        return v___x_820_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_821_: *mut crate::leanh::LeanObject,
    mut v_h__1_822_: *mut crate::leanh::LeanObject,
    mut v_h__2_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_74__boxed_824_: u8 = 0;
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_824_ = (crate::leanh::lean_unbox(v_____do__lift_821_) as u8);
    v_res_825_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_824_, v_h__1_822_, v_h__2_823_);
    return v_res_825_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(
    mut v_00_u03b2_826_: *mut crate::leanh::LeanObject,
    mut v_n_827_: *mut crate::leanh::LeanObject,
    mut v_f_828_: *mut crate::leanh::LeanObject,
    mut v_inst_829_: *mut crate::leanh::LeanObject,
    mut v_out_830_: *mut crate::leanh::LeanObject,
    mut v_motive_831_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_832_: u8,
    mut v_h__1_833_: *mut crate::leanh::LeanObject,
    mut v_h__2_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_832_ == 0 {
        let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_834_);
        v___x_835_ = crate::leanh::lean_apply_1(v_h__1_833_, crate::leanh::lean_box(0));
        return v___x_835_;
    } else {
        let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_833_);
        v___x_836_ = crate::leanh::lean_apply_1(v_h__2_834_, crate::leanh::lean_box(0));
        return v___x_836_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(
    mut v_00_u03b2_837_: *mut crate::leanh::LeanObject,
    mut v_n_838_: *mut crate::leanh::LeanObject,
    mut v_f_839_: *mut crate::leanh::LeanObject,
    mut v_inst_840_: *mut crate::leanh::LeanObject,
    mut v_out_841_: *mut crate::leanh::LeanObject,
    mut v_motive_842_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_843_: *mut crate::leanh::LeanObject,
    mut v_h__1_844_: *mut crate::leanh::LeanObject,
    mut v_h__2_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_82__boxed_846_: u8 = 0;
    let mut v_res_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_846_ = (crate::leanh::lean_unbox(v_____do__lift_843_) as u8);
    v_res_847_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(v_00_u03b2_837_, v_n_838_, v_f_839_, v_inst_840_, v_out_841_, v_motive_842_, v_____do__lift_82__boxed_846_, v_h__1_844_, v_h__2_845_);
    crate::leanh::lean_dec(v_out_841_);
    crate::leanh::lean_dec(v_inst_840_);
    crate::leanh::lean_dec(v_f_839_);
    return v_res_847_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(
    mut v_x_848_: *mut crate::leanh::LeanObject,
    mut v_h__1_849_: *mut crate::leanh::LeanObject,
    mut v_h__2_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_848_) == 0 {
        let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_850_);
        v___x_851_ = crate::leanh::lean_apply_1(v_h__1_849_, crate::leanh::lean_box(0));
        return v___x_851_;
    } else {
        let mut v_val_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_849_);
        v_val_852_ = crate::leanh::lean_ctor_get(v_x_848_, 0);
        crate::leanh::lean_inc(v_val_852_);
        crate::leanh::lean_dec_ref_known(v_x_848_, 1);
        v___x_853_ = crate::leanh::lean_apply_2(v_h__2_850_, v_val_852_, crate::leanh::lean_box(0));
        return v___x_853_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(
    mut v_00_u03b2_x27_854_: *mut crate::leanh::LeanObject,
    mut v_motive_855_: *mut crate::leanh::LeanObject,
    mut v_x_856_: *mut crate::leanh::LeanObject,
    mut v_h__1_857_: *mut crate::leanh::LeanObject,
    mut v_h__2_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_856_) == 0 {
        let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_858_);
        v___x_859_ = crate::leanh::lean_apply_1(v_h__1_857_, crate::leanh::lean_box(0));
        return v___x_859_;
    } else {
        let mut v_val_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_857_);
        v_val_860_ = crate::leanh::lean_ctor_get(v_x_856_, 0);
        crate::leanh::lean_inc(v_val_860_);
        crate::leanh::lean_dec_ref_known(v_x_856_, 1);
        v___x_861_ = crate::leanh::lean_apply_2(v_h__2_858_, v_val_860_, crate::leanh::lean_box(0));
        return v___x_861_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(
    mut v_x_862_: *mut crate::leanh::LeanObject,
    mut v_h__1_863_: *mut crate::leanh::LeanObject,
    mut v_h__2_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_862_) == 0 {
        let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_864_);
        v___x_865_ = crate::leanh::lean_apply_1(v_h__1_863_, crate::leanh::lean_box(0));
        return v___x_865_;
    } else {
        let mut v_val_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_863_);
        v_val_866_ = crate::leanh::lean_ctor_get(v_x_862_, 0);
        crate::leanh::lean_inc(v_val_866_);
        crate::leanh::lean_dec_ref_known(v_x_862_, 1);
        v___x_867_ = crate::leanh::lean_apply_2(v_h__2_864_, v_val_866_, crate::leanh::lean_box(0));
        return v___x_867_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(
    mut v_00_u03b3_868_: *mut crate::leanh::LeanObject,
    mut v_motive_869_: *mut crate::leanh::LeanObject,
    mut v_x_870_: *mut crate::leanh::LeanObject,
    mut v_h__1_871_: *mut crate::leanh::LeanObject,
    mut v_h__2_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_870_) == 0 {
        let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_872_);
        v___x_873_ = crate::leanh::lean_apply_1(v_h__1_871_, crate::leanh::lean_box(0));
        return v___x_873_;
    } else {
        let mut v_val_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_871_);
        v_val_874_ = crate::leanh::lean_ctor_get(v_x_870_, 0);
        crate::leanh::lean_inc(v_val_874_);
        crate::leanh::lean_dec_ref_known(v_x_870_, 1);
        v___x_875_ = crate::leanh::lean_apply_2(v_h__2_872_, v_val_874_, crate::leanh::lean_box(0));
        return v___x_875_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(
    mut v_x_876_: *mut crate::leanh::LeanObject,
    mut v_h__1_877_: *mut crate::leanh::LeanObject,
    mut v_h__2_878_: *mut crate::leanh::LeanObject,
    mut v_h__3_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_876_) {
        0 => {
            let mut v_it_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_879_);
            crate::leanh::lean_dec(v_h__2_878_);
            v_it_880_ = crate::leanh::lean_ctor_get(v_x_876_, 0);
            crate::leanh::lean_inc(v_it_880_);
            v_out_881_ = crate::leanh::lean_ctor_get(v_x_876_, 1);
            crate::leanh::lean_inc(v_out_881_);
            crate::leanh::lean_dec_ref_known(v_x_876_, 2);
            v___x_882_ = crate::leanh::lean_apply_2(v_h__1_877_, v_it_880_, v_out_881_);
            return v___x_882_;
        }
        1 => {
            let mut v_it_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_879_);
            crate::leanh::lean_dec(v_h__1_877_);
            v_it_883_ = crate::leanh::lean_ctor_get(v_x_876_, 0);
            crate::leanh::lean_inc(v_it_883_);
            crate::leanh::lean_dec_ref_known(v_x_876_, 1);
            v___x_884_ = crate::leanh::lean_apply_1(v_h__2_878_, v_it_883_);
            return v___x_884_;
        }
        _ => {
            let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_878_);
            crate::leanh::lean_dec(v_h__1_877_);
            v___x_885_ = crate::leanh::lean_box(0);
            v___x_886_ = crate::leanh::lean_apply_1(v_h__3_879_, v___x_885_);
            return v___x_886_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(
    mut v_00_u03b1_887_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_888_: *mut crate::leanh::LeanObject,
    mut v_motive_889_: *mut crate::leanh::LeanObject,
    mut v_x_890_: *mut crate::leanh::LeanObject,
    mut v_h__1_891_: *mut crate::leanh::LeanObject,
    mut v_h__2_892_: *mut crate::leanh::LeanObject,
    mut v_h__3_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_890_) {
        0 => {
            let mut v_it_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_893_);
            crate::leanh::lean_dec(v_h__2_892_);
            v_it_894_ = crate::leanh::lean_ctor_get(v_x_890_, 0);
            crate::leanh::lean_inc(v_it_894_);
            v_out_895_ = crate::leanh::lean_ctor_get(v_x_890_, 1);
            crate::leanh::lean_inc(v_out_895_);
            crate::leanh::lean_dec_ref_known(v_x_890_, 2);
            v___x_896_ = crate::leanh::lean_apply_2(v_h__1_891_, v_it_894_, v_out_895_);
            return v___x_896_;
        }
        1 => {
            let mut v_it_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_893_);
            crate::leanh::lean_dec(v_h__1_891_);
            v_it_897_ = crate::leanh::lean_ctor_get(v_x_890_, 0);
            crate::leanh::lean_inc(v_it_897_);
            crate::leanh::lean_dec_ref_known(v_x_890_, 1);
            v___x_898_ = crate::leanh::lean_apply_1(v_h__2_892_, v_it_897_);
            return v___x_898_;
        }
        _ => {
            let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_892_);
            crate::leanh::lean_dec(v_h__1_891_);
            v___x_899_ = crate::leanh::lean_box(0);
            v___x_900_ = crate::leanh::lean_apply_1(v_h__3_893_, v___x_899_);
            return v___x_900_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(
    mut v_x_901_: *mut crate::leanh::LeanObject,
    mut v_h__1_902_: *mut crate::leanh::LeanObject,
    mut v_h__2_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_901_) == 0 {
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_903_);
        v___x_904_ = crate::leanh::lean_box(0);
        v___x_905_ = crate::leanh::lean_apply_1(v_h__1_902_, v___x_904_);
        return v___x_905_;
    } else {
        let mut v_val_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_902_);
        v_val_906_ = crate::leanh::lean_ctor_get(v_x_901_, 0);
        crate::leanh::lean_inc(v_val_906_);
        crate::leanh::lean_dec_ref_known(v_x_901_, 1);
        v___x_907_ = crate::leanh::lean_apply_1(v_h__2_903_, v_val_906_);
        return v___x_907_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(
    mut v_00_u03b3_908_: *mut crate::leanh::LeanObject,
    mut v_motive_909_: *mut crate::leanh::LeanObject,
    mut v_x_910_: *mut crate::leanh::LeanObject,
    mut v_h__1_911_: *mut crate::leanh::LeanObject,
    mut v_h__2_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_910_) == 0 {
        let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_912_);
        v___x_913_ = crate::leanh::lean_box(0);
        v___x_914_ = crate::leanh::lean_apply_1(v_h__1_911_, v___x_913_);
        return v___x_914_;
    } else {
        let mut v_val_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_911_);
        v_val_915_ = crate::leanh::lean_ctor_get(v_x_910_, 0);
        crate::leanh::lean_inc(v_val_915_);
        crate::leanh::lean_dec_ref_known(v_x_910_, 1);
        v___x_916_ = crate::leanh::lean_apply_1(v_h__2_912_, v_val_915_);
        return v___x_916_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_917_: *mut crate::leanh::LeanObject,
    mut v_h__1_918_: *mut crate::leanh::LeanObject,
    mut v_h__2_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_917_) == 0 {
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_918_);
        v___x_920_ = crate::leanh::lean_box(0);
        v___x_921_ = crate::leanh::lean_apply_1(v_h__2_919_, v___x_920_);
        return v___x_921_;
    } else {
        let mut v_val_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_919_);
        v_val_922_ = crate::leanh::lean_ctor_get(v_____do__lift_917_, 0);
        crate::leanh::lean_inc(v_val_922_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_917_, 1);
        v___x_923_ = crate::leanh::lean_apply_1(v_h__1_918_, v_val_922_);
        return v___x_923_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_924_: *mut crate::leanh::LeanObject,
    mut v_motive_925_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_926_: *mut crate::leanh::LeanObject,
    mut v_h__1_927_: *mut crate::leanh::LeanObject,
    mut v_h__2_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_926_) == 0 {
        let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_927_);
        v___x_929_ = crate::leanh::lean_box(0);
        v___x_930_ = crate::leanh::lean_apply_1(v_h__2_928_, v___x_929_);
        return v___x_930_;
    } else {
        let mut v_val_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_928_);
        v_val_931_ = crate::leanh::lean_ctor_get(v_____do__lift_926_, 0);
        crate::leanh::lean_inc(v_val_931_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_926_, 1);
        v___x_932_ = crate::leanh::lean_apply_1(v_h__1_927_, v_val_931_);
        return v___x_932_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_933_: *mut crate::leanh::LeanObject,
    mut v_h__1_934_: *mut crate::leanh::LeanObject,
    mut v_h__2_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_933_) == 0 {
        let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_934_);
        v___x_936_ = crate::leanh::lean_box(0);
        v___x_937_ = crate::leanh::lean_apply_1(v_h__2_935_, v___x_936_);
        return v___x_937_;
    } else {
        let mut v_val_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_935_);
        v_val_938_ = crate::leanh::lean_ctor_get(v_____do__lift_933_, 0);
        crate::leanh::lean_inc(v_val_938_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_933_, 1);
        v___x_939_ = crate::leanh::lean_apply_1(v_h__1_934_, v_val_938_);
        return v___x_939_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_u2082_940_: *mut crate::leanh::LeanObject,
    mut v_motive_941_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_942_: *mut crate::leanh::LeanObject,
    mut v_h__1_943_: *mut crate::leanh::LeanObject,
    mut v_h__2_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_942_) == 0 {
        let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_943_);
        v___x_945_ = crate::leanh::lean_box(0);
        v___x_946_ = crate::leanh::lean_apply_1(v_h__2_944_, v___x_945_);
        return v___x_946_;
    } else {
        let mut v_val_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_944_);
        v_val_947_ = crate::leanh::lean_ctor_get(v_____do__lift_942_, 0);
        crate::leanh::lean_inc(v_val_947_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_942_, 1);
        v___x_948_ = crate::leanh::lean_apply_1(v_h__1_943_, v_val_947_);
        return v___x_948_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_949_: *mut crate::leanh::LeanObject,
    mut v_h__1_950_: *mut crate::leanh::LeanObject,
    mut v_h__2_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_949_) == 1 {
        let mut v_val_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_951_);
        v_val_952_ = crate::leanh::lean_ctor_get(v_____x_949_, 0);
        crate::leanh::lean_inc(v_val_952_);
        crate::leanh::lean_dec_ref_known(v_____x_949_, 1);
        v___x_953_ = crate::leanh::lean_apply_1(v_h__1_950_, v_val_952_);
        return v___x_953_;
    } else {
        let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_950_);
        v___x_954_ =
            crate::leanh::lean_apply_2(v_h__2_951_, v_____x_949_, crate::leanh::lean_box(0));
        return v___x_954_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_955_: *mut crate::leanh::LeanObject,
    mut v_motive_956_: *mut crate::leanh::LeanObject,
    mut v_____x_957_: *mut crate::leanh::LeanObject,
    mut v_h__1_958_: *mut crate::leanh::LeanObject,
    mut v_h__2_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_957_) == 1 {
        let mut v_val_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_959_);
        v_val_960_ = crate::leanh::lean_ctor_get(v_____x_957_, 0);
        crate::leanh::lean_inc(v_val_960_);
        crate::leanh::lean_dec_ref_known(v_____x_957_, 1);
        v___x_961_ = crate::leanh::lean_apply_1(v_h__1_958_, v_val_960_);
        return v___x_961_;
    } else {
        let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_958_);
        v___x_962_ =
            crate::leanh::lean_apply_2(v_h__2_959_, v_____x_957_, crate::leanh::lean_box(0));
        return v___x_962_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____x_963_: *mut crate::leanh::LeanObject,
    mut v_h__1_964_: *mut crate::leanh::LeanObject,
    mut v_h__2_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_963_) == 1 {
        let mut v_val_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_965_);
        v_val_966_ = crate::leanh::lean_ctor_get(v_____x_963_, 0);
        crate::leanh::lean_inc(v_val_966_);
        crate::leanh::lean_dec_ref_known(v_____x_963_, 1);
        v___x_967_ = crate::leanh::lean_apply_1(v_h__1_964_, v_val_966_);
        return v___x_967_;
    } else {
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_964_);
        v___x_968_ =
            crate::leanh::lean_apply_2(v_h__2_965_, v_____x_963_, crate::leanh::lean_box(0));
        return v___x_968_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_969_: *mut crate::leanh::LeanObject,
    mut v_motive_970_: *mut crate::leanh::LeanObject,
    mut v_____x_971_: *mut crate::leanh::LeanObject,
    mut v_h__1_972_: *mut crate::leanh::LeanObject,
    mut v_h__2_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_971_) == 1 {
        let mut v_val_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_973_);
        v_val_974_ = crate::leanh::lean_ctor_get(v_____x_971_, 0);
        crate::leanh::lean_inc(v_val_974_);
        crate::leanh::lean_dec_ref_known(v_____x_971_, 1);
        v___x_975_ = crate::leanh::lean_apply_1(v_h__1_972_, v_val_974_);
        return v___x_975_;
    } else {
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_972_);
        v___x_976_ =
            crate::leanh::lean_apply_2(v_h__2_973_, v_____x_971_, crate::leanh::lean_box(0));
        return v___x_976_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_977_: *mut crate::leanh::LeanObject,
    mut v_h__1_978_: *mut crate::leanh::LeanObject,
    mut v_h__2_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_977_) == 0 {
        let mut v_a_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_978_);
        v_a_980_ = crate::leanh::lean_ctor_get(v_____do__lift_977_, 0);
        crate::leanh::lean_inc(v_a_980_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_977_, 1);
        v___x_981_ = crate::leanh::lean_apply_1(v_h__2_979_, v_a_980_);
        return v___x_981_;
    } else {
        let mut v_a_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_979_);
        v_a_982_ = crate::leanh::lean_ctor_get(v_____do__lift_977_, 0);
        crate::leanh::lean_inc(v_a_982_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_977_, 1);
        v___x_983_ = crate::leanh::lean_apply_1(v_h__1_978_, v_a_982_);
        return v___x_983_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_984_: *mut crate::leanh::LeanObject,
    mut v_motive_985_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_986_: *mut crate::leanh::LeanObject,
    mut v_h__1_987_: *mut crate::leanh::LeanObject,
    mut v_h__2_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_986_) == 0 {
        let mut v_a_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_987_);
        v_a_989_ = crate::leanh::lean_ctor_get(v_____do__lift_986_, 0);
        crate::leanh::lean_inc(v_a_989_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_986_, 1);
        v___x_990_ = crate::leanh::lean_apply_1(v_h__2_988_, v_a_989_);
        return v___x_990_;
    } else {
        let mut v_a_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_988_);
        v_a_991_ = crate::leanh::lean_ctor_get(v_____do__lift_986_, 0);
        crate::leanh::lean_inc(v_a_991_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_986_, 1);
        v___x_992_ = crate::leanh::lean_apply_1(v_h__1_987_, v_a_991_);
        return v___x_992_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_993_: *mut crate::leanh::LeanObject,
    mut v_h__1_994_: *mut crate::leanh::LeanObject,
    mut v_h__2_995_: *mut crate::leanh::LeanObject,
    mut v_h__3_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_993_) {
        0 => {
            let mut v_it_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_996_);
            crate::leanh::lean_dec(v_h__2_995_);
            v_it_997_ = crate::leanh::lean_ctor_get(v_x_993_, 0);
            crate::leanh::lean_inc(v_it_997_);
            v_out_998_ = crate::leanh::lean_ctor_get(v_x_993_, 1);
            crate::leanh::lean_inc(v_out_998_);
            crate::leanh::lean_dec_ref_known(v_x_993_, 2);
            v___x_999_ = crate::leanh::lean_apply_3(
                v_h__1_994_,
                v_it_997_,
                v_out_998_,
                crate::leanh::lean_box(0),
            );
            return v___x_999_;
        }
        1 => {
            let mut v_it_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_996_);
            crate::leanh::lean_dec(v_h__1_994_);
            v_it_1000_ = crate::leanh::lean_ctor_get(v_x_993_, 0);
            crate::leanh::lean_inc(v_it_1000_);
            crate::leanh::lean_dec_ref_known(v_x_993_, 1);
            v___x_1001_ =
                crate::leanh::lean_apply_2(v_h__2_995_, v_it_1000_, crate::leanh::lean_box(0));
            return v___x_1001_;
        }
        _ => {
            let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_995_);
            crate::leanh::lean_dec(v_h__1_994_);
            v___x_1002_ = crate::leanh::lean_apply_1(v_h__3_996_, crate::leanh::lean_box(0));
            return v___x_1002_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_1003_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1004_: *mut crate::leanh::LeanObject,
    mut v_m_1005_: *mut crate::leanh::LeanObject,
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_it_1007_: *mut crate::leanh::LeanObject,
    mut v_motive_1008_: *mut crate::leanh::LeanObject,
    mut v_x_1009_: *mut crate::leanh::LeanObject,
    mut v_h__1_1010_: *mut crate::leanh::LeanObject,
    mut v_h__2_1011_: *mut crate::leanh::LeanObject,
    mut v_h__3_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1009_) {
        0 => {
            let mut v_it_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1012_);
            crate::leanh::lean_dec(v_h__2_1011_);
            v_it_1013_ = crate::leanh::lean_ctor_get(v_x_1009_, 0);
            crate::leanh::lean_inc(v_it_1013_);
            v_out_1014_ = crate::leanh::lean_ctor_get(v_x_1009_, 1);
            crate::leanh::lean_inc(v_out_1014_);
            crate::leanh::lean_dec_ref_known(v_x_1009_, 2);
            v___x_1015_ = crate::leanh::lean_apply_3(
                v_h__1_1010_,
                v_it_1013_,
                v_out_1014_,
                crate::leanh::lean_box(0),
            );
            return v___x_1015_;
        }
        1 => {
            let mut v_it_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1012_);
            crate::leanh::lean_dec(v_h__1_1010_);
            v_it_1016_ = crate::leanh::lean_ctor_get(v_x_1009_, 0);
            crate::leanh::lean_inc(v_it_1016_);
            crate::leanh::lean_dec_ref_known(v_x_1009_, 1);
            v___x_1017_ =
                crate::leanh::lean_apply_2(v_h__2_1011_, v_it_1016_, crate::leanh::lean_box(0));
            return v___x_1017_;
        }
        _ => {
            let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1011_);
            crate::leanh::lean_dec(v_h__1_1010_);
            v___x_1018_ = crate::leanh::lean_apply_1(v_h__3_1012_, crate::leanh::lean_box(0));
            return v___x_1018_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_1019_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1020_: *mut crate::leanh::LeanObject,
    mut v_m_1021_: *mut crate::leanh::LeanObject,
    mut v_inst_1022_: *mut crate::leanh::LeanObject,
    mut v_it_1023_: *mut crate::leanh::LeanObject,
    mut v_motive_1024_: *mut crate::leanh::LeanObject,
    mut v_x_1025_: *mut crate::leanh::LeanObject,
    mut v_h__1_1026_: *mut crate::leanh::LeanObject,
    mut v_h__2_1027_: *mut crate::leanh::LeanObject,
    mut v_h__3_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_1019_, v_00_u03b2_1020_, v_m_1021_, v_inst_1022_, v_it_1023_, v_motive_1024_, v_x_1025_, v_h__1_1026_, v_h__2_1027_, v_h__3_1028_);
    crate::leanh::lean_dec(v_it_1023_);
    crate::leanh::lean_dec(v_inst_1022_);
    return v_res_1029_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_1030_: *mut crate::leanh::LeanObject,
    mut v_h__1_1031_: *mut crate::leanh::LeanObject,
    mut v_h__2_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1030_) == 0 {
        let mut v_a_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1031_);
        v_a_1033_ = crate::leanh::lean_ctor_get(v_____do__lift_1030_, 0);
        crate::leanh::lean_inc(v_a_1033_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1030_, 1);
        v___x_1034_ = crate::leanh::lean_apply_1(v_h__2_1032_, v_a_1033_);
        return v___x_1034_;
    } else {
        let mut v_a_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1032_);
        v_a_1035_ = crate::leanh::lean_ctor_get(v_____do__lift_1030_, 0);
        crate::leanh::lean_inc(v_a_1035_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1030_, 1);
        v___x_1036_ = crate::leanh::lean_apply_1(v_h__1_1031_, v_a_1035_);
        return v___x_1036_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_1037_: *mut crate::leanh::LeanObject,
    mut v_motive_1038_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1039_: *mut crate::leanh::LeanObject,
    mut v_h__1_1040_: *mut crate::leanh::LeanObject,
    mut v_h__2_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1039_) == 0 {
        let mut v_a_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1040_);
        v_a_1042_ = crate::leanh::lean_ctor_get(v_____do__lift_1039_, 0);
        crate::leanh::lean_inc(v_a_1042_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1039_, 1);
        v___x_1043_ = crate::leanh::lean_apply_1(v_h__2_1041_, v_a_1042_);
        return v___x_1043_;
    } else {
        let mut v_a_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1041_);
        v_a_1044_ = crate::leanh::lean_ctor_get(v_____do__lift_1039_, 0);
        crate::leanh::lean_inc(v_a_1044_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1039_, 1);
        v___x_1045_ = crate::leanh::lean_apply_1(v_h__1_1040_, v_a_1044_);
        return v___x_1045_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_1046_: *mut crate::leanh::LeanObject,
    mut v_h__1_1047_: *mut crate::leanh::LeanObject,
    mut v_h__2_1048_: *mut crate::leanh::LeanObject,
    mut v_h__3_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1046_) {
        0 => {
            let mut v_it_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1049_);
            crate::leanh::lean_dec(v_h__2_1048_);
            v_it_1050_ = crate::leanh::lean_ctor_get(v_x_1046_, 0);
            crate::leanh::lean_inc(v_it_1050_);
            v_out_1051_ = crate::leanh::lean_ctor_get(v_x_1046_, 1);
            crate::leanh::lean_inc(v_out_1051_);
            crate::leanh::lean_dec_ref_known(v_x_1046_, 2);
            v___x_1052_ = crate::leanh::lean_apply_2(v_h__1_1047_, v_it_1050_, v_out_1051_);
            return v___x_1052_;
        }
        1 => {
            let mut v_it_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1049_);
            crate::leanh::lean_dec(v_h__1_1047_);
            v_it_1053_ = crate::leanh::lean_ctor_get(v_x_1046_, 0);
            crate::leanh::lean_inc(v_it_1053_);
            crate::leanh::lean_dec_ref_known(v_x_1046_, 1);
            v___x_1054_ = crate::leanh::lean_apply_1(v_h__2_1048_, v_it_1053_);
            return v___x_1054_;
        }
        _ => {
            let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1048_);
            crate::leanh::lean_dec(v_h__1_1047_);
            v___x_1055_ = crate::leanh::lean_box(0);
            v___x_1056_ = crate::leanh::lean_apply_1(v_h__3_1049_, v___x_1055_);
            return v___x_1056_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_1057_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1058_: *mut crate::leanh::LeanObject,
    mut v_motive_1059_: *mut crate::leanh::LeanObject,
    mut v_x_1060_: *mut crate::leanh::LeanObject,
    mut v_h__1_1061_: *mut crate::leanh::LeanObject,
    mut v_h__2_1062_: *mut crate::leanh::LeanObject,
    mut v_h__3_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1060_) {
        0 => {
            let mut v_it_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1063_);
            crate::leanh::lean_dec(v_h__2_1062_);
            v_it_1064_ = crate::leanh::lean_ctor_get(v_x_1060_, 0);
            crate::leanh::lean_inc(v_it_1064_);
            v_out_1065_ = crate::leanh::lean_ctor_get(v_x_1060_, 1);
            crate::leanh::lean_inc(v_out_1065_);
            crate::leanh::lean_dec_ref_known(v_x_1060_, 2);
            v___x_1066_ = crate::leanh::lean_apply_2(v_h__1_1061_, v_it_1064_, v_out_1065_);
            return v___x_1066_;
        }
        1 => {
            let mut v_it_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1063_);
            crate::leanh::lean_dec(v_h__1_1061_);
            v_it_1067_ = crate::leanh::lean_ctor_get(v_x_1060_, 0);
            crate::leanh::lean_inc(v_it_1067_);
            crate::leanh::lean_dec_ref_known(v_x_1060_, 1);
            v___x_1068_ = crate::leanh::lean_apply_1(v_h__2_1062_, v_it_1067_);
            return v___x_1068_;
        }
        _ => {
            let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1062_);
            crate::leanh::lean_dec(v_h__1_1061_);
            v___x_1069_ = crate::leanh::lean_box(0);
            v___x_1070_ = crate::leanh::lean_apply_1(v_h__3_1063_, v___x_1069_);
            return v___x_1070_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
}
