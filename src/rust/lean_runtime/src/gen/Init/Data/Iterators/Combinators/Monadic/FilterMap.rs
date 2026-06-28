// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.FilterMap
// Imports: Init.Data.Iterators.PostconditionMonad Init.Data.Iterators.Consumers.Monadic.Loop Init.PropLemmas
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::PostconditionMonad::{
    initialize_Init_Data_Iterators_PostconditionMonad,
    runtime_initialize_Init_Data_Iterators_PostconditionMonad,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap___redArg(
    mut v_it_563_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_563_);
    return v_it_563_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap___redArg___boxed(
    mut v_it_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_565_: *mut LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Std_IterM_InternalCombinators_filterMap___redArg(v_it_564_);
    lean_dec(v_it_564_);
    return v_res_565_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap(
    mut v_00_u03b1_566_: *mut LeanObject,
    mut v_00_u03b2_567_: *mut LeanObject,
    mut v_00_u03b3_568_: *mut LeanObject,
    mut v_m_569_: *mut LeanObject,
    mut v_n_570_: *mut LeanObject,
    mut v_lift_571_: *mut LeanObject,
    mut v_inst_572_: *mut LeanObject,
    mut v_f_573_: *mut LeanObject,
    mut v_it_574_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_574_);
    return v_it_574_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap___boxed(
    mut v_00_u03b1_575_: *mut LeanObject,
    mut v_00_u03b2_576_: *mut LeanObject,
    mut v_00_u03b3_577_: *mut LeanObject,
    mut v_m_578_: *mut LeanObject,
    mut v_n_579_: *mut LeanObject,
    mut v_lift_580_: *mut LeanObject,
    mut v_inst_581_: *mut LeanObject,
    mut v_f_582_: *mut LeanObject,
    mut v_it_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Std_IterM_InternalCombinators_filterMap(
        v_00_u03b1_575_,
        v_00_u03b2_576_,
        v_00_u03b3_577_,
        v_m_578_,
        v_n_579_,
        v_lift_580_,
        v_inst_581_,
        v_f_582_,
        v_it_583_,
    );
    lean_dec(v_it_583_);
    lean_dec(v_f_582_);
    lean_dec(v_inst_581_);
    lean_dec(v_lift_580_);
    return v_res_584_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map___redArg(
    mut v_it_585_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_585_);
    return v_it_585_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map___redArg___boxed(
    mut v_it_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_587_: *mut LeanObject = core::ptr::null_mut();
    v_res_587_ = l_Std_IterM_InternalCombinators_map___redArg(v_it_586_);
    lean_dec(v_it_586_);
    return v_res_587_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map(
    mut v_00_u03b1_588_: *mut LeanObject,
    mut v_00_u03b2_589_: *mut LeanObject,
    mut v_00_u03b3_590_: *mut LeanObject,
    mut v_m_591_: *mut LeanObject,
    mut v_n_592_: *mut LeanObject,
    mut v_inst_593_: *mut LeanObject,
    mut v_lift_594_: *mut LeanObject,
    mut v_inst_595_: *mut LeanObject,
    mut v_f_596_: *mut LeanObject,
    mut v_it_597_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_597_);
    return v_it_597_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map___boxed(
    mut v_00_u03b1_598_: *mut LeanObject,
    mut v_00_u03b2_599_: *mut LeanObject,
    mut v_00_u03b3_600_: *mut LeanObject,
    mut v_m_601_: *mut LeanObject,
    mut v_n_602_: *mut LeanObject,
    mut v_inst_603_: *mut LeanObject,
    mut v_lift_604_: *mut LeanObject,
    mut v_inst_605_: *mut LeanObject,
    mut v_f_606_: *mut LeanObject,
    mut v_it_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_608_: *mut LeanObject = core::ptr::null_mut();
    v_res_608_ = l_Std_IterM_InternalCombinators_map(
        v_00_u03b1_598_,
        v_00_u03b2_599_,
        v_00_u03b3_600_,
        v_m_601_,
        v_n_602_,
        v_inst_603_,
        v_lift_604_,
        v_inst_605_,
        v_f_606_,
        v_it_607_,
    );
    lean_dec(v_it_607_);
    lean_dec(v_f_606_);
    lean_dec(v_inst_605_);
    lean_dec(v_lift_604_);
    lean_dec_ref(v_inst_603_);
    return v_res_608_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition___redArg(
    mut v_it_609_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_609_);
    return v_it_609_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition___redArg___boxed(
    mut v_it_610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_611_: *mut LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Std_IterM_filterMapWithPostcondition___redArg(v_it_610_);
    lean_dec(v_it_610_);
    return v_res_611_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition(
    mut v_00_u03b1_612_: *mut LeanObject,
    mut v_00_u03b2_613_: *mut LeanObject,
    mut v_00_u03b3_614_: *mut LeanObject,
    mut v_m_615_: *mut LeanObject,
    mut v_n_616_: *mut LeanObject,
    mut v_inst_617_: *mut LeanObject,
    mut v_inst_618_: *mut LeanObject,
    mut v_f_619_: *mut LeanObject,
    mut v_it_620_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_620_);
    return v_it_620_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition___boxed(
    mut v_00_u03b1_621_: *mut LeanObject,
    mut v_00_u03b2_622_: *mut LeanObject,
    mut v_00_u03b3_623_: *mut LeanObject,
    mut v_m_624_: *mut LeanObject,
    mut v_n_625_: *mut LeanObject,
    mut v_inst_626_: *mut LeanObject,
    mut v_inst_627_: *mut LeanObject,
    mut v_f_628_: *mut LeanObject,
    mut v_it_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_630_: *mut LeanObject = core::ptr::null_mut();
    v_res_630_ = l_Std_IterM_filterMapWithPostcondition(
        v_00_u03b1_621_,
        v_00_u03b2_622_,
        v_00_u03b3_623_,
        v_m_624_,
        v_n_625_,
        v_inst_626_,
        v_inst_627_,
        v_f_628_,
        v_it_629_,
    );
    lean_dec(v_it_629_);
    lean_dec(v_f_628_);
    lean_dec(v_inst_627_);
    lean_dec(v_inst_626_);
    return v_res_630_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(
    mut v_it_631_: *mut LeanObject,
    mut v_toPure_632_: *mut LeanObject,
    mut v_____do__lift_633_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_633_) == 0 {
        let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
        v___x_634_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_634_, 0, v_it_631_);
        v___x_635_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_634_);
        return v___x_635_;
    } else {
        let mut v_val_636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
        v_val_636_ = lean_ctor_get(v_____do__lift_633_, 0);
        lean_inc(v_val_636_);
        v___x_637_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_637_, 0, v_it_631_);
        lean_ctor_set(v___x_637_, 1, v_val_636_);
        v___x_638_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_637_);
        return v___x_638_;
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed(
    mut v_it_639_: *mut LeanObject,
    mut v_toPure_640_: *mut LeanObject,
    mut v_____do__lift_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_642_: *mut LeanObject = core::ptr::null_mut();
    v_res_642_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(
        v_it_639_,
        v_toPure_640_,
        v_____do__lift_641_,
    );
    lean_dec(v_____do__lift_641_);
    return v_res_642_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1(
    mut v_toPure_643_: *mut LeanObject,
    mut v_f_644_: *mut LeanObject,
    mut v_toBind_645_: *mut LeanObject,
    mut v_____do__lift_646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_646_) {
                0 => {
                    v_it_647_ = lean_ctor_get(v_____do__lift_646_, 0);
                    lean_inc(v_it_647_);
                    v_out_648_ = lean_ctor_get(v_____do__lift_646_, 1);
                    lean_inc(v_out_648_);
                    lean_dec_ref_known(v_____do__lift_646_, 2);
                    v___f_649_ = lean_alloc_closure(
                        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_649_, 0, v_it_647_);
                    lean_closure_set(v___f_649_, 1, v_toPure_643_);
                    v___x_650_ = lean_apply_1(v_f_644_, v_out_648_);
                    v___x_651_ = lean_apply_4(
                        v_toBind_645_,
                        lean_box(0),
                        lean_box(0),
                        v___x_650_,
                        v___f_649_,
                    );
                    return v___x_651_;
                }
                1 => {
                    lean_dec(v_toBind_645_);
                    lean_dec(v_f_644_);
                    v_it_652_ = lean_ctor_get(v_____do__lift_646_, 0);
                    v_isSharedCheck_660_ = (!lean_is_exclusive(v_____do__lift_646_)) as u8;
                    if v_isSharedCheck_660_ == 0 {
                        v___x_654_ = v_____do__lift_646_;
                        v_isShared_655_ = v_isSharedCheck_660_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_it_652_);
                        lean_dec(v_____do__lift_646_);
                        v___x_654_ = lean_box(0);
                        v_isShared_655_ = v_isSharedCheck_660_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_toBind_645_);
                    lean_dec(v_f_644_);
                    v___x_661_ = lean_box(2);
                    v___x_662_ = lean_apply_2(v_toPure_643_, lean_box(0), v___x_661_);
                    return v___x_662_;
                }
            },
            1 => {
                if v_isShared_655_ == 0 {
                    v___x_657_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_659_, 0, v_it_652_);
                    v___x_657_ = v_reuseFailAlloc_659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_658_ = lean_apply_2(v_toPure_643_, lean_box(0), v___x_657_);
                return v___x_658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2(
    mut v_inst_663_: *mut LeanObject,
    mut v_lift_664_: *mut LeanObject,
    mut v_toBind_665_: *mut LeanObject,
    mut v___f_666_: *mut LeanObject,
    mut v_it_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_668_ = lean_apply_1(v_inst_663_, v_it_667_);
    v___x_669_ = lean_apply_2(v_lift_664_, lean_box(0), v___x_668_);
    v___x_670_ = lean_apply_4(
        v_toBind_665_,
        lean_box(0),
        lean_box(0),
        v___x_669_,
        v___f_666_,
    );
    return v___x_670_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg(
    mut v_lift_671_: *mut LeanObject,
    mut v_f_672_: *mut LeanObject,
    mut v_inst_673_: *mut LeanObject,
    mut v_inst_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_679_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_675_ = lean_ctor_get(v_inst_674_, 0);
    lean_inc_ref(v_toApplicative_675_);
    v_toBind_676_ = lean_ctor_get(v_inst_674_, 1);
    lean_inc_n(v_toBind_676_, 2);
    lean_dec_ref(v_inst_674_);
    v_toPure_677_ = lean_ctor_get(v_toApplicative_675_, 1);
    lean_inc(v_toPure_677_);
    lean_dec_ref(v_toApplicative_675_);
    v___f_678_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_678_, 0, v_toPure_677_);
    lean_closure_set(v___f_678_, 1, v_f_672_);
    lean_closure_set(v___f_678_, 2, v_toBind_676_);
    v___f_679_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_679_, 0, v_inst_673_);
    lean_closure_set(v___f_679_, 1, v_lift_671_);
    lean_closure_set(v___f_679_, 2, v_toBind_676_);
    lean_closure_set(v___f_679_, 3, v___f_678_);
    return v___f_679_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator(
    mut v_00_u03b1_680_: *mut LeanObject,
    mut v_00_u03b2_681_: *mut LeanObject,
    mut v_00_u03b3_682_: *mut LeanObject,
    mut v_m_683_: *mut LeanObject,
    mut v_n_684_: *mut LeanObject,
    mut v_lift_685_: *mut LeanObject,
    mut v_f_686_: *mut LeanObject,
    mut v_inst_687_: *mut LeanObject,
    mut v_inst_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg(
        v_lift_685_,
        v_f_686_,
        v_inst_687_,
        v_inst_688_,
    );
    return v___x_689_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0(
    mut v_a_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v___x_691_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_691_, 0, v_a_690_);
    return v___x_691_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2(
    mut v_toFunctor_692_: *mut LeanObject,
    mut v_toPure_693_: *mut LeanObject,
    mut v_f_694_: *mut LeanObject,
    mut v___f_695_: *mut LeanObject,
    mut v_toBind_696_: *mut LeanObject,
    mut v_____do__lift_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_708_: u8 = 0;
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_697_) {
                0 => {
                    v_it_698_ = lean_ctor_get(v_____do__lift_697_, 0);
                    lean_inc(v_it_698_);
                    v_out_699_ = lean_ctor_get(v_____do__lift_697_, 1);
                    lean_inc(v_out_699_);
                    lean_dec_ref_known(v_____do__lift_697_, 2);
                    v_map_700_ = lean_ctor_get(v_toFunctor_692_, 0);
                    lean_inc(v_map_700_);
                    lean_dec_ref(v_toFunctor_692_);
                    v___f_701_ = lean_alloc_closure(
                        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_701_, 0, v_it_698_);
                    lean_closure_set(v___f_701_, 1, v_toPure_693_);
                    v___x_702_ = lean_apply_1(v_f_694_, v_out_699_);
                    v___x_703_ =
                        lean_apply_4(v_map_700_, lean_box(0), lean_box(0), v___f_695_, v___x_702_);
                    v___x_704_ = lean_apply_4(
                        v_toBind_696_,
                        lean_box(0),
                        lean_box(0),
                        v___x_703_,
                        v___f_701_,
                    );
                    return v___x_704_;
                }
                1 => {
                    lean_dec(v_toBind_696_);
                    lean_dec_ref(v___f_695_);
                    lean_dec(v_f_694_);
                    lean_dec_ref(v_toFunctor_692_);
                    v_it_705_ = lean_ctor_get(v_____do__lift_697_, 0);
                    v_isSharedCheck_713_ = (!lean_is_exclusive(v_____do__lift_697_)) as u8;
                    if v_isSharedCheck_713_ == 0 {
                        v___x_707_ = v_____do__lift_697_;
                        v_isShared_708_ = v_isSharedCheck_713_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_it_705_);
                        lean_dec(v_____do__lift_697_);
                        v___x_707_ = lean_box(0);
                        v_isShared_708_ = v_isSharedCheck_713_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_toBind_696_);
                    lean_dec_ref(v___f_695_);
                    lean_dec(v_f_694_);
                    lean_dec_ref(v_toFunctor_692_);
                    v___x_714_ = lean_box(2);
                    v___x_715_ = lean_apply_2(v_toPure_693_, lean_box(0), v___x_714_);
                    return v___x_715_;
                }
            },
            1 => {
                if v_isShared_708_ == 0 {
                    v___x_710_ = v___x_707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_712_, 0, v_it_705_);
                    v___x_710_ = v_reuseFailAlloc_712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_711_ = lean_apply_2(v_toPure_693_, lean_box(0), v___x_710_);
                return v___x_711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3___redArg(
    mut v_inst_717_: *mut LeanObject,
    mut v_inst_718_: *mut LeanObject,
    mut v_lift_719_: *mut LeanObject,
    mut v_f_720_: *mut LeanObject,
    mut v_it_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_722_ = lean_ctor_get(v_inst_717_, 0);
    lean_inc_ref(v_toApplicative_722_);
    v_toBind_723_ = lean_ctor_get(v_inst_717_, 1);
    lean_inc_n(v_toBind_723_, 2);
    lean_dec_ref(v_inst_717_);
    v_toFunctor_724_ = lean_ctor_get(v_toApplicative_722_, 0);
    lean_inc_ref(v_toFunctor_724_);
    v_toPure_725_ = lean_ctor_get(v_toApplicative_722_, 1);
    lean_inc(v_toPure_725_);
    lean_dec_ref(v_toApplicative_722_);
    v___f_726_ = l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0;
    v___x_727_ = lean_apply_1(v_inst_718_, v_it_721_);
    v___x_728_ = lean_apply_2(v_lift_719_, lean_box(0), v___x_727_);
    v___f_729_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_729_, 0, v_toFunctor_724_);
    lean_closure_set(v___f_729_, 1, v_toPure_725_);
    lean_closure_set(v___f_729_, 2, v_f_720_);
    lean_closure_set(v___f_729_, 3, v___f_726_);
    lean_closure_set(v___f_729_, 4, v_toBind_723_);
    v___x_730_ = lean_apply_4(
        v_toBind_723_,
        lean_box(0),
        lean_box(0),
        v___x_728_,
        v___f_729_,
    );
    return v___x_730_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3(
    mut v_00_u03b1_731_: *mut LeanObject,
    mut v_00_u03b2_732_: *mut LeanObject,
    mut v_00_u03b3_733_: *mut LeanObject,
    mut v_m_734_: *mut LeanObject,
    mut v_n_735_: *mut LeanObject,
    mut v_inst_736_: *mut LeanObject,
    mut v_inst_737_: *mut LeanObject,
    mut v_lift_738_: *mut LeanObject,
    mut v_f_739_: *mut LeanObject,
    mut v_it_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_741_ = lean_ctor_get(v_inst_736_, 0);
    lean_inc_ref(v_toApplicative_741_);
    v_toBind_742_ = lean_ctor_get(v_inst_736_, 1);
    lean_inc_n(v_toBind_742_, 2);
    lean_dec_ref(v_inst_736_);
    v_toFunctor_743_ = lean_ctor_get(v_toApplicative_741_, 0);
    lean_inc_ref(v_toFunctor_743_);
    v_toPure_744_ = lean_ctor_get(v_toApplicative_741_, 1);
    lean_inc(v_toPure_744_);
    lean_dec_ref(v_toApplicative_741_);
    v___f_745_ = l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0;
    v___x_746_ = lean_apply_1(v_inst_737_, v_it_740_);
    v___x_747_ = lean_apply_2(v_lift_738_, lean_box(0), v___x_746_);
    v___f_748_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_748_, 0, v_toFunctor_743_);
    lean_closure_set(v___f_748_, 1, v_toPure_744_);
    lean_closure_set(v___f_748_, 2, v_f_739_);
    lean_closure_set(v___f_748_, 3, v___f_745_);
    lean_closure_set(v___f_748_, 4, v_toBind_742_);
    v___x_749_ = lean_apply_4(
        v_toBind_742_,
        lean_box(0),
        lean_box(0),
        v___x_747_,
        v___f_748_,
    );
    return v___x_749_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___redArg(
    mut v_inst_750_: *mut LeanObject,
    mut v_inst_751_: *mut LeanObject,
    mut v_lift_752_: *mut LeanObject,
    mut v_f_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___x_754_, 0, lean_box(0));
    lean_closure_set(v___x_754_, 1, lean_box(0));
    lean_closure_set(v___x_754_, 2, lean_box(0));
    lean_closure_set(v___x_754_, 3, lean_box(0));
    lean_closure_set(v___x_754_, 4, lean_box(0));
    lean_closure_set(v___x_754_, 5, v_inst_750_);
    lean_closure_set(v___x_754_, 6, v_inst_751_);
    lean_closure_set(v___x_754_, 7, v_lift_752_);
    lean_closure_set(v___x_754_, 8, v_f_753_);
    return v___x_754_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator(
    mut v_00_u03b1_755_: *mut LeanObject,
    mut v_00_u03b2_756_: *mut LeanObject,
    mut v_00_u03b3_757_: *mut LeanObject,
    mut v_m_758_: *mut LeanObject,
    mut v_n_759_: *mut LeanObject,
    mut v_inst_760_: *mut LeanObject,
    mut v_inst_761_: *mut LeanObject,
    mut v_lift_762_: *mut LeanObject,
    mut v_f_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___x_764_, 0, lean_box(0));
    lean_closure_set(v___x_764_, 1, lean_box(0));
    lean_closure_set(v___x_764_, 2, lean_box(0));
    lean_closure_set(v___x_764_, 3, lean_box(0));
    lean_closure_set(v___x_764_, 4, lean_box(0));
    lean_closure_set(v___x_764_, 5, v_inst_760_);
    lean_closure_set(v___x_764_, 6, v_inst_761_);
    lean_closure_set(v___x_764_, 7, v_lift_762_);
    lean_closure_set(v___x_764_, 8, v_f_763_);
    return v___x_764_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(
    mut v_00_u03b1_765_: *mut LeanObject,
    mut v_00_u03b2_766_: *mut LeanObject,
    mut v_00_u03b3_767_: *mut LeanObject,
    mut v_m_768_: *mut LeanObject,
    mut v_n_769_: *mut LeanObject,
    mut v_inst_770_: *mut LeanObject,
    mut v_inst_771_: *mut LeanObject,
    mut v_lift_772_: *mut LeanObject,
    mut v_f_773_: *mut LeanObject,
    mut v_inst_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_775_ = lean_box(0);
    return v___x_775_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(
    mut v_00_u03b1_776_: *mut LeanObject,
    mut v_00_u03b2_777_: *mut LeanObject,
    mut v_00_u03b3_778_: *mut LeanObject,
    mut v_m_779_: *mut LeanObject,
    mut v_n_780_: *mut LeanObject,
    mut v_inst_781_: *mut LeanObject,
    mut v_inst_782_: *mut LeanObject,
    mut v_lift_783_: *mut LeanObject,
    mut v_f_784_: *mut LeanObject,
    mut v_inst_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_786_: *mut LeanObject = core::ptr::null_mut();
    v_res_786_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(v_00_u03b1_776_, v_00_u03b2_777_, v_00_u03b3_778_, v_m_779_, v_n_780_, v_inst_781_, v_inst_782_, v_lift_783_, v_f_784_, v_inst_785_);
    lean_dec(v_f_784_);
    lean_dec(v_lift_783_);
    lean_dec(v_inst_782_);
    lean_dec_ref(v_inst_781_);
    return v_res_786_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(
    mut v_00_u03b1_787_: *mut LeanObject,
    mut v_00_u03b2_788_: *mut LeanObject,
    mut v_00_u03b3_789_: *mut LeanObject,
    mut v_m_790_: *mut LeanObject,
    mut v_n_791_: *mut LeanObject,
    mut v_inst_792_: *mut LeanObject,
    mut v_inst_793_: *mut LeanObject,
    mut v_lift_794_: *mut LeanObject,
    mut v_f_795_: *mut LeanObject,
    mut v_inst_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___x_797_ = lean_box(0);
    return v___x_797_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(
    mut v_00_u03b1_798_: *mut LeanObject,
    mut v_00_u03b2_799_: *mut LeanObject,
    mut v_00_u03b3_800_: *mut LeanObject,
    mut v_m_801_: *mut LeanObject,
    mut v_n_802_: *mut LeanObject,
    mut v_inst_803_: *mut LeanObject,
    mut v_inst_804_: *mut LeanObject,
    mut v_lift_805_: *mut LeanObject,
    mut v_f_806_: *mut LeanObject,
    mut v_inst_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(v_00_u03b1_798_, v_00_u03b2_799_, v_00_u03b3_800_, v_m_801_, v_n_802_, v_inst_803_, v_inst_804_, v_lift_805_, v_f_806_, v_inst_807_);
    lean_dec(v_f_806_);
    lean_dec(v_lift_805_);
    lean_dec(v_inst_804_);
    lean_dec_ref(v_inst_803_);
    return v_res_808_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(
    mut v_toPure_809_: *mut LeanObject,
    mut v_recur_810_: *mut LeanObject,
    mut v_it_811_: *mut LeanObject,
    mut v_____do__lift_812_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_812_) == 0 {
        let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_811_);
        lean_dec(v_recur_810_);
        v_a_813_ = lean_ctor_get(v_____do__lift_812_, 0);
        lean_inc(v_a_813_);
        lean_dec_ref_known(v_____do__lift_812_, 1);
        v___x_814_ = lean_apply_2(v_toPure_809_, lean_box(0), v_a_813_);
        return v___x_814_;
    } else {
        let mut v_a_815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_809_);
        v_a_815_ = lean_ctor_get(v_____do__lift_812_, 0);
        lean_inc(v_a_815_);
        lean_dec_ref_known(v_____do__lift_812_, 1);
        v___x_816_ = lean_apply_4(v_recur_810_, v_it_811_, v_a_815_, lean_box(0), lean_box(0));
        return v___x_816_;
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(
    mut v_toPure_817_: *mut LeanObject,
    mut v_recur_818_: *mut LeanObject,
    mut v___y_819_: *mut LeanObject,
    mut v_acc_820_: *mut LeanObject,
    mut v_toBind_821_: *mut LeanObject,
    mut v_s_822_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_822_) {
        0 => {
            let mut v_it_823_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
            v_it_823_ = lean_ctor_get(v_s_822_, 0);
            lean_inc(v_it_823_);
            v_out_824_ = lean_ctor_get(v_s_822_, 1);
            lean_inc(v_out_824_);
            lean_dec_ref_known(v_s_822_, 2);
            v___f_825_ = lean_alloc_closure(
                l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_825_, 0, v_toPure_817_);
            lean_closure_set(v___f_825_, 1, v_recur_818_);
            lean_closure_set(v___f_825_, 2, v_it_823_);
            v___x_826_ = lean_apply_3(v___y_819_, v_out_824_, lean_box(0), v_acc_820_);
            v___x_827_ = lean_apply_4(
                v_toBind_821_,
                lean_box(0),
                lean_box(0),
                v___x_826_,
                v___f_825_,
            );
            return v___x_827_;
        }
        1 => {
            let mut v_it_828_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_821_);
            lean_dec(v___y_819_);
            lean_dec(v_toPure_817_);
            v_it_828_ = lean_ctor_get(v_s_822_, 0);
            lean_inc(v_it_828_);
            lean_dec_ref_known(v_s_822_, 1);
            v___x_829_ = lean_apply_4(
                v_recur_818_,
                v_it_828_,
                v_acc_820_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_829_;
        }
        _ => {
            let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_821_);
            lean_dec(v___y_819_);
            lean_dec(v_recur_818_);
            v___x_830_ = lean_apply_2(v_toPure_817_, lean_box(0), v_acc_820_);
            return v___x_830_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(
    mut v_inst_831_: *mut LeanObject,
    mut v_toPure_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v_toBind_834_: *mut LeanObject,
    mut v_f_835_: *mut LeanObject,
    mut v_inst_836_: *mut LeanObject,
    mut v_lift_837_: *mut LeanObject,
    mut v_lift_838_: *mut LeanObject,
    mut v_it_839_: *mut LeanObject,
    mut v_acc_840_: *mut LeanObject,
    mut v_hP_841_: *mut LeanObject,
    mut v_recur_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_843_ = lean_ctor_get(v_inst_831_, 0);
    lean_inc_ref(v_toApplicative_843_);
    v_toBind_844_ = lean_ctor_get(v_inst_831_, 1);
    lean_inc_n(v_toBind_844_, 2);
    lean_dec_ref(v_inst_831_);
    v_toPure_845_ = lean_ctor_get(v_toApplicative_843_, 1);
    lean_inc(v_toPure_845_);
    lean_dec_ref(v_toApplicative_843_);
    v___f_846_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_846_, 0, v_toPure_832_);
    lean_closure_set(v___f_846_, 1, v_recur_842_);
    lean_closure_set(v___f_846_, 2, v___y_833_);
    lean_closure_set(v___f_846_, 3, v_acc_840_);
    lean_closure_set(v___f_846_, 4, v_toBind_834_);
    v___f_847_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_847_, 0, v_toPure_845_);
    lean_closure_set(v___f_847_, 1, v_f_835_);
    lean_closure_set(v___f_847_, 2, v_toBind_844_);
    v___x_848_ = lean_apply_1(v_inst_836_, v_it_839_);
    v___x_849_ = lean_apply_2(v_lift_837_, lean_box(0), v___x_848_);
    v___x_850_ = lean_apply_4(
        v_toBind_844_,
        lean_box(0),
        lean_box(0),
        v___x_849_,
        v___f_847_,
    );
    v___x_851_ = lean_apply_4(
        v_lift_838_,
        lean_box(0),
        lean_box(0),
        v___f_846_,
        v___x_850_,
    );
    return v___x_851_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(
    mut v_inst_852_: *mut LeanObject,
    mut v_inst_853_: *mut LeanObject,
    mut v_f_854_: *mut LeanObject,
    mut v_inst_855_: *mut LeanObject,
    mut v_lift_856_: *mut LeanObject,
    mut v_lift_857_: *mut LeanObject,
    mut v_00_u03b3_858_: *mut LeanObject,
    mut v_Pl_859_: *mut LeanObject,
    mut v_it_860_: *mut LeanObject,
    mut v_init_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_863_ = lean_ctor_get(v_inst_852_, 0);
    lean_inc_ref(v_toApplicative_863_);
    v_toBind_864_ = lean_ctor_get(v_inst_852_, 1);
    lean_inc(v_toBind_864_);
    lean_dec_ref(v_inst_852_);
    v_toPure_865_ = lean_ctor_get(v_toApplicative_863_, 1);
    lean_inc(v_toPure_865_);
    lean_dec_ref(v_toApplicative_863_);
    v___f_866_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4
            as *mut core::ffi::c_void,
        12,
        8,
    );
    lean_closure_set(v___f_866_, 0, v_inst_853_);
    lean_closure_set(v___f_866_, 1, v_toPure_865_);
    lean_closure_set(v___f_866_, 2, v___y_862_);
    lean_closure_set(v___f_866_, 3, v_toBind_864_);
    lean_closure_set(v___f_866_, 4, v_f_854_);
    lean_closure_set(v___f_866_, 5, v_inst_855_);
    lean_closure_set(v___f_866_, 6, v_lift_856_);
    lean_closure_set(v___f_866_, 7, v_lift_857_);
    v___x_867_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_866_, v_it_860_, v_init_861_, lean_box(0));
    return v___x_867_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(
    mut v_inst_868_: *mut LeanObject,
    mut v_inst_869_: *mut LeanObject,
    mut v_inst_870_: *mut LeanObject,
    mut v_lift_871_: *mut LeanObject,
    mut v_f_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_873_: *mut LeanObject = core::ptr::null_mut();
    v___f_873_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        11,
        5,
    );
    lean_closure_set(v___f_873_, 0, v_inst_869_);
    lean_closure_set(v___f_873_, 1, v_inst_868_);
    lean_closure_set(v___f_873_, 2, v_f_872_);
    lean_closure_set(v___f_873_, 3, v_inst_870_);
    lean_closure_set(v___f_873_, 4, v_lift_871_);
    return v___f_873_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop(
    mut v_00_u03b1_874_: *mut LeanObject,
    mut v_00_u03b2_875_: *mut LeanObject,
    mut v_00_u03b3_876_: *mut LeanObject,
    mut v_m_877_: *mut LeanObject,
    mut v_n_878_: *mut LeanObject,
    mut v_o_879_: *mut LeanObject,
    mut v_inst_880_: *mut LeanObject,
    mut v_inst_881_: *mut LeanObject,
    mut v_inst_882_: *mut LeanObject,
    mut v_lift_883_: *mut LeanObject,
    mut v_f_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_885_: *mut LeanObject = core::ptr::null_mut();
    v___f_885_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        11,
        5,
    );
    lean_closure_set(v___f_885_, 0, v_inst_881_);
    lean_closure_set(v___f_885_, 1, v_inst_880_);
    lean_closure_set(v___f_885_, 2, v_f_884_);
    lean_closure_set(v___f_885_, 3, v_inst_882_);
    lean_closure_set(v___f_885_, 4, v_lift_883_);
    return v___f_885_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5(
    mut v_inst_886_: *mut LeanObject,
    mut v_toPure_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
    mut v_toBind_889_: *mut LeanObject,
    mut v_inst_890_: *mut LeanObject,
    mut v_lift_891_: *mut LeanObject,
    mut v_f_892_: *mut LeanObject,
    mut v___f_893_: *mut LeanObject,
    mut v_lift_894_: *mut LeanObject,
    mut v_it_895_: *mut LeanObject,
    mut v_acc_896_: *mut LeanObject,
    mut v_hP_897_: *mut LeanObject,
    mut v_recur_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_899_ = lean_ctor_get(v_inst_886_, 0);
    lean_inc_ref(v_toApplicative_899_);
    v_toBind_900_ = lean_ctor_get(v_inst_886_, 1);
    lean_inc_n(v_toBind_900_, 2);
    lean_dec_ref(v_inst_886_);
    v_toFunctor_901_ = lean_ctor_get(v_toApplicative_899_, 0);
    lean_inc_ref(v_toFunctor_901_);
    v_toPure_902_ = lean_ctor_get(v_toApplicative_899_, 1);
    lean_inc(v_toPure_902_);
    lean_dec_ref(v_toApplicative_899_);
    v___f_903_ = lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_903_, 0, v_toPure_887_);
    lean_closure_set(v___f_903_, 1, v_recur_898_);
    lean_closure_set(v___f_903_, 2, v___y_888_);
    lean_closure_set(v___f_903_, 3, v_acc_896_);
    lean_closure_set(v___f_903_, 4, v_toBind_889_);
    v___x_904_ = lean_apply_1(v_inst_890_, v_it_895_);
    v___x_905_ = lean_apply_2(v_lift_891_, lean_box(0), v___x_904_);
    v___f_906_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_906_, 0, v_toFunctor_901_);
    lean_closure_set(v___f_906_, 1, v_toPure_902_);
    lean_closure_set(v___f_906_, 2, v_f_892_);
    lean_closure_set(v___f_906_, 3, v___f_893_);
    lean_closure_set(v___f_906_, 4, v_toBind_900_);
    v___x_907_ = lean_apply_4(
        v_toBind_900_,
        lean_box(0),
        lean_box(0),
        v___x_905_,
        v___f_906_,
    );
    v___x_908_ = lean_apply_4(
        v_lift_894_,
        lean_box(0),
        lean_box(0),
        v___f_903_,
        v___x_907_,
    );
    return v___x_908_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(
    mut v_inst_909_: *mut LeanObject,
    mut v_inst_910_: *mut LeanObject,
    mut v_inst_911_: *mut LeanObject,
    mut v_lift_912_: *mut LeanObject,
    mut v_f_913_: *mut LeanObject,
    mut v___f_914_: *mut LeanObject,
    mut v_lift_915_: *mut LeanObject,
    mut v_00_u03b3_916_: *mut LeanObject,
    mut v_Pl_917_: *mut LeanObject,
    mut v_it_918_: *mut LeanObject,
    mut v_init_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_921_ = lean_ctor_get(v_inst_909_, 0);
    lean_inc_ref(v_toApplicative_921_);
    v_toBind_922_ = lean_ctor_get(v_inst_909_, 1);
    lean_inc(v_toBind_922_);
    lean_dec_ref(v_inst_909_);
    v_toPure_923_ = lean_ctor_get(v_toApplicative_921_, 1);
    lean_inc(v_toPure_923_);
    lean_dec_ref(v_toApplicative_921_);
    v___f_924_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5 as *mut core::ffi::c_void,
        13,
        9,
    );
    lean_closure_set(v___f_924_, 0, v_inst_910_);
    lean_closure_set(v___f_924_, 1, v_toPure_923_);
    lean_closure_set(v___f_924_, 2, v___y_920_);
    lean_closure_set(v___f_924_, 3, v_toBind_922_);
    lean_closure_set(v___f_924_, 4, v_inst_911_);
    lean_closure_set(v___f_924_, 5, v_lift_912_);
    lean_closure_set(v___f_924_, 6, v_f_913_);
    lean_closure_set(v___f_924_, 7, v___f_914_);
    lean_closure_set(v___f_924_, 8, v_lift_915_);
    v___x_925_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_924_, v_it_918_, v_init_919_, lean_box(0));
    return v___x_925_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop___redArg(
    mut v_inst_926_: *mut LeanObject,
    mut v_inst_927_: *mut LeanObject,
    mut v_inst_928_: *mut LeanObject,
    mut v_lift_929_: *mut LeanObject,
    mut v_f_930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_932_: *mut LeanObject = core::ptr::null_mut();
    v___f_931_ = l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0;
    v___f_932_ = lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        12,
        6,
    );
    lean_closure_set(v___f_932_, 0, v_inst_927_);
    lean_closure_set(v___f_932_, 1, v_inst_926_);
    lean_closure_set(v___f_932_, 2, v_inst_928_);
    lean_closure_set(v___f_932_, 3, v_lift_929_);
    lean_closure_set(v___f_932_, 4, v_f_930_);
    lean_closure_set(v___f_932_, 5, v___f_931_);
    return v___f_932_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop(
    mut v_00_u03b1_933_: *mut LeanObject,
    mut v_00_u03b2_934_: *mut LeanObject,
    mut v_00_u03b3_935_: *mut LeanObject,
    mut v_m_936_: *mut LeanObject,
    mut v_n_937_: *mut LeanObject,
    mut v_o_938_: *mut LeanObject,
    mut v_inst_939_: *mut LeanObject,
    mut v_inst_940_: *mut LeanObject,
    mut v_inst_941_: *mut LeanObject,
    mut v_lift_942_: *mut LeanObject,
    mut v_f_943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___x_944_ = l_Std_Iterators_Types_Map_instIteratorLoop___redArg(
        v_inst_939_,
        v_inst_940_,
        v_inst_941_,
        v_lift_942_,
        v_f_943_,
    );
    return v___x_944_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition___redArg(
    mut v_it_945_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_945_);
    return v_it_945_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition___redArg___boxed(
    mut v_it_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_947_: *mut LeanObject = core::ptr::null_mut();
    v_res_947_ = l_Std_IterM_mapWithPostcondition___redArg(v_it_946_);
    lean_dec(v_it_946_);
    return v_res_947_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition(
    mut v_00_u03b1_948_: *mut LeanObject,
    mut v_00_u03b2_949_: *mut LeanObject,
    mut v_00_u03b3_950_: *mut LeanObject,
    mut v_m_951_: *mut LeanObject,
    mut v_n_952_: *mut LeanObject,
    mut v_inst_953_: *mut LeanObject,
    mut v_inst_954_: *mut LeanObject,
    mut v_inst_955_: *mut LeanObject,
    mut v_f_956_: *mut LeanObject,
    mut v_it_957_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_957_);
    return v_it_957_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition___boxed(
    mut v_00_u03b1_958_: *mut LeanObject,
    mut v_00_u03b2_959_: *mut LeanObject,
    mut v_00_u03b3_960_: *mut LeanObject,
    mut v_m_961_: *mut LeanObject,
    mut v_n_962_: *mut LeanObject,
    mut v_inst_963_: *mut LeanObject,
    mut v_inst_964_: *mut LeanObject,
    mut v_inst_965_: *mut LeanObject,
    mut v_f_966_: *mut LeanObject,
    mut v_it_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Std_IterM_mapWithPostcondition(
        v_00_u03b1_958_,
        v_00_u03b2_959_,
        v_00_u03b3_960_,
        v_m_961_,
        v_n_962_,
        v_inst_963_,
        v_inst_964_,
        v_inst_965_,
        v_f_966_,
        v_it_967_,
    );
    lean_dec(v_it_967_);
    lean_dec(v_f_966_);
    lean_dec(v_inst_965_);
    lean_dec(v_inst_964_);
    lean_dec_ref(v_inst_963_);
    return v_res_968_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition___redArg(
    mut v_it_969_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_969_);
    return v_it_969_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition___redArg___boxed(
    mut v_it_970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_971_: *mut LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Std_IterM_filterWithPostcondition___redArg(v_it_970_);
    lean_dec(v_it_970_);
    return v_res_971_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition(
    mut v_00_u03b1_972_: *mut LeanObject,
    mut v_00_u03b2_973_: *mut LeanObject,
    mut v_m_974_: *mut LeanObject,
    mut v_n_975_: *mut LeanObject,
    mut v_inst_976_: *mut LeanObject,
    mut v_inst_977_: *mut LeanObject,
    mut v_inst_978_: *mut LeanObject,
    mut v_f_979_: *mut LeanObject,
    mut v_it_980_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_980_);
    return v_it_980_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition___boxed(
    mut v_00_u03b1_981_: *mut LeanObject,
    mut v_00_u03b2_982_: *mut LeanObject,
    mut v_m_983_: *mut LeanObject,
    mut v_n_984_: *mut LeanObject,
    mut v_inst_985_: *mut LeanObject,
    mut v_inst_986_: *mut LeanObject,
    mut v_inst_987_: *mut LeanObject,
    mut v_f_988_: *mut LeanObject,
    mut v_it_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Std_IterM_filterWithPostcondition(
        v_00_u03b1_981_,
        v_00_u03b2_982_,
        v_m_983_,
        v_n_984_,
        v_inst_985_,
        v_inst_986_,
        v_inst_987_,
        v_f_988_,
        v_it_989_,
    );
    lean_dec(v_it_989_);
    lean_dec(v_f_988_);
    lean_dec(v_inst_987_);
    lean_dec(v_inst_986_);
    lean_dec_ref(v_inst_985_);
    return v_res_990_;
}
pub unsafe fn l_Std_IterM_filterMapM___redArg(mut v_it_991_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_991_);
    return v_it_991_;
}
pub unsafe fn l_Std_IterM_filterMapM___redArg___boxed(
    mut v_it_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_993_: *mut LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Std_IterM_filterMapM___redArg(v_it_992_);
    lean_dec(v_it_992_);
    return v_res_993_;
}
pub unsafe fn l_Std_IterM_filterMapM(
    mut v_00_u03b1_994_: *mut LeanObject,
    mut v_00_u03b2_995_: *mut LeanObject,
    mut v_00_u03b3_996_: *mut LeanObject,
    mut v_m_997_: *mut LeanObject,
    mut v_n_998_: *mut LeanObject,
    mut v_inst_999_: *mut LeanObject,
    mut v_inst_1000_: *mut LeanObject,
    mut v_inst_1001_: *mut LeanObject,
    mut v_inst_1002_: *mut LeanObject,
    mut v_f_1003_: *mut LeanObject,
    mut v_it_1004_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_1004_);
    return v_it_1004_;
}
pub unsafe fn l_Std_IterM_filterMapM___boxed(
    mut v_00_u03b1_1005_: *mut LeanObject,
    mut v_00_u03b2_1006_: *mut LeanObject,
    mut v_00_u03b3_1007_: *mut LeanObject,
    mut v_m_1008_: *mut LeanObject,
    mut v_n_1009_: *mut LeanObject,
    mut v_inst_1010_: *mut LeanObject,
    mut v_inst_1011_: *mut LeanObject,
    mut v_inst_1012_: *mut LeanObject,
    mut v_inst_1013_: *mut LeanObject,
    mut v_f_1014_: *mut LeanObject,
    mut v_it_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1016_: *mut LeanObject = core::ptr::null_mut();
    v_res_1016_ = l_Std_IterM_filterMapM(
        v_00_u03b1_1005_,
        v_00_u03b2_1006_,
        v_00_u03b3_1007_,
        v_m_1008_,
        v_n_1009_,
        v_inst_1010_,
        v_inst_1011_,
        v_inst_1012_,
        v_inst_1013_,
        v_f_1014_,
        v_it_1015_,
    );
    lean_dec(v_it_1015_);
    lean_dec(v_f_1014_);
    lean_dec(v_inst_1013_);
    lean_dec(v_inst_1012_);
    lean_dec_ref(v_inst_1011_);
    lean_dec(v_inst_1010_);
    return v_res_1016_;
}
pub unsafe fn l_Std_IterM_mapM___redArg(mut v_it_1017_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_1017_);
    return v_it_1017_;
}
pub unsafe fn l_Std_IterM_mapM___redArg___boxed(
    mut v_it_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Std_IterM_mapM___redArg(v_it_1018_);
    lean_dec(v_it_1018_);
    return v_res_1019_;
}
pub unsafe fn l_Std_IterM_mapM(
    mut v_00_u03b1_1020_: *mut LeanObject,
    mut v_00_u03b2_1021_: *mut LeanObject,
    mut v_00_u03b3_1022_: *mut LeanObject,
    mut v_m_1023_: *mut LeanObject,
    mut v_n_1024_: *mut LeanObject,
    mut v_inst_1025_: *mut LeanObject,
    mut v_inst_1026_: *mut LeanObject,
    mut v_inst_1027_: *mut LeanObject,
    mut v_inst_1028_: *mut LeanObject,
    mut v_f_1029_: *mut LeanObject,
    mut v_it_1030_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_1030_);
    return v_it_1030_;
}
pub unsafe fn l_Std_IterM_mapM___boxed(
    mut v_00_u03b1_1031_: *mut LeanObject,
    mut v_00_u03b2_1032_: *mut LeanObject,
    mut v_00_u03b3_1033_: *mut LeanObject,
    mut v_m_1034_: *mut LeanObject,
    mut v_n_1035_: *mut LeanObject,
    mut v_inst_1036_: *mut LeanObject,
    mut v_inst_1037_: *mut LeanObject,
    mut v_inst_1038_: *mut LeanObject,
    mut v_inst_1039_: *mut LeanObject,
    mut v_f_1040_: *mut LeanObject,
    mut v_it_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1042_: *mut LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Std_IterM_mapM(
        v_00_u03b1_1031_,
        v_00_u03b2_1032_,
        v_00_u03b3_1033_,
        v_m_1034_,
        v_n_1035_,
        v_inst_1036_,
        v_inst_1037_,
        v_inst_1038_,
        v_inst_1039_,
        v_f_1040_,
        v_it_1041_,
    );
    lean_dec(v_it_1041_);
    lean_dec(v_f_1040_);
    lean_dec(v_inst_1039_);
    lean_dec(v_inst_1038_);
    lean_dec_ref(v_inst_1037_);
    lean_dec(v_inst_1036_);
    return v_res_1042_;
}
pub unsafe fn l_Std_IterM_filterM___redArg(mut v_it_1043_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_1043_);
    return v_it_1043_;
}
pub unsafe fn l_Std_IterM_filterM___redArg___boxed(
    mut v_it_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1045_: *mut LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Std_IterM_filterM___redArg(v_it_1044_);
    lean_dec(v_it_1044_);
    return v_res_1045_;
}
pub unsafe fn l_Std_IterM_filterM(
    mut v_00_u03b1_1046_: *mut LeanObject,
    mut v_00_u03b2_1047_: *mut LeanObject,
    mut v_m_1048_: *mut LeanObject,
    mut v_n_1049_: *mut LeanObject,
    mut v_inst_1050_: *mut LeanObject,
    mut v_inst_1051_: *mut LeanObject,
    mut v_inst_1052_: *mut LeanObject,
    mut v_inst_1053_: *mut LeanObject,
    mut v_f_1054_: *mut LeanObject,
    mut v_it_1055_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_1055_);
    return v_it_1055_;
}
pub unsafe fn l_Std_IterM_filterM___boxed(
    mut v_00_u03b1_1056_: *mut LeanObject,
    mut v_00_u03b2_1057_: *mut LeanObject,
    mut v_m_1058_: *mut LeanObject,
    mut v_n_1059_: *mut LeanObject,
    mut v_inst_1060_: *mut LeanObject,
    mut v_inst_1061_: *mut LeanObject,
    mut v_inst_1062_: *mut LeanObject,
    mut v_inst_1063_: *mut LeanObject,
    mut v_f_1064_: *mut LeanObject,
    mut v_it_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Std_IterM_filterM(
        v_00_u03b1_1056_,
        v_00_u03b2_1057_,
        v_m_1058_,
        v_n_1059_,
        v_inst_1060_,
        v_inst_1061_,
        v_inst_1062_,
        v_inst_1063_,
        v_f_1064_,
        v_it_1065_,
    );
    lean_dec(v_it_1065_);
    lean_dec(v_f_1064_);
    lean_dec(v_inst_1063_);
    lean_dec(v_inst_1062_);
    lean_dec_ref(v_inst_1061_);
    lean_dec(v_inst_1060_);
    return v_res_1066_;
}
pub unsafe fn l_Std_IterM_filterMap___redArg(mut v_it_1067_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_1067_);
    return v_it_1067_;
}
pub unsafe fn l_Std_IterM_filterMap___redArg___boxed(
    mut v_it_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1069_: *mut LeanObject = core::ptr::null_mut();
    v_res_1069_ = l_Std_IterM_filterMap___redArg(v_it_1068_);
    lean_dec(v_it_1068_);
    return v_res_1069_;
}
pub unsafe fn l_Std_IterM_filterMap(
    mut v_00_u03b1_1070_: *mut LeanObject,
    mut v_00_u03b2_1071_: *mut LeanObject,
    mut v_00_u03b3_1072_: *mut LeanObject,
    mut v_m_1073_: *mut LeanObject,
    mut v_inst_1074_: *mut LeanObject,
    mut v_inst_1075_: *mut LeanObject,
    mut v_f_1076_: *mut LeanObject,
    mut v_it_1077_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_1077_);
    return v_it_1077_;
}
pub unsafe fn l_Std_IterM_filterMap___boxed(
    mut v_00_u03b1_1078_: *mut LeanObject,
    mut v_00_u03b2_1079_: *mut LeanObject,
    mut v_00_u03b3_1080_: *mut LeanObject,
    mut v_m_1081_: *mut LeanObject,
    mut v_inst_1082_: *mut LeanObject,
    mut v_inst_1083_: *mut LeanObject,
    mut v_f_1084_: *mut LeanObject,
    mut v_it_1085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1086_: *mut LeanObject = core::ptr::null_mut();
    v_res_1086_ = l_Std_IterM_filterMap(
        v_00_u03b1_1078_,
        v_00_u03b2_1079_,
        v_00_u03b3_1080_,
        v_m_1081_,
        v_inst_1082_,
        v_inst_1083_,
        v_f_1084_,
        v_it_1085_,
    );
    lean_dec(v_it_1085_);
    lean_dec_ref(v_f_1084_);
    lean_dec_ref(v_inst_1083_);
    lean_dec(v_inst_1082_);
    return v_res_1086_;
}
pub unsafe fn l_Std_IterM_map___redArg(mut v_it_1087_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_1087_);
    return v_it_1087_;
}
pub unsafe fn l_Std_IterM_map___redArg___boxed(mut v_it_1088_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1089_: *mut LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Std_IterM_map___redArg(v_it_1088_);
    lean_dec(v_it_1088_);
    return v_res_1089_;
}
pub unsafe fn l_Std_IterM_map(
    mut v_00_u03b1_1090_: *mut LeanObject,
    mut v_00_u03b2_1091_: *mut LeanObject,
    mut v_00_u03b3_1092_: *mut LeanObject,
    mut v_m_1093_: *mut LeanObject,
    mut v_inst_1094_: *mut LeanObject,
    mut v_inst_1095_: *mut LeanObject,
    mut v_f_1096_: *mut LeanObject,
    mut v_it_1097_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_1097_);
    return v_it_1097_;
}
pub unsafe fn l_Std_IterM_map___boxed(
    mut v_00_u03b1_1098_: *mut LeanObject,
    mut v_00_u03b2_1099_: *mut LeanObject,
    mut v_00_u03b3_1100_: *mut LeanObject,
    mut v_m_1101_: *mut LeanObject,
    mut v_inst_1102_: *mut LeanObject,
    mut v_inst_1103_: *mut LeanObject,
    mut v_f_1104_: *mut LeanObject,
    mut v_it_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1106_: *mut LeanObject = core::ptr::null_mut();
    v_res_1106_ = l_Std_IterM_map(
        v_00_u03b1_1098_,
        v_00_u03b2_1099_,
        v_00_u03b3_1100_,
        v_m_1101_,
        v_inst_1102_,
        v_inst_1103_,
        v_f_1104_,
        v_it_1105_,
    );
    lean_dec(v_it_1105_);
    lean_dec(v_f_1104_);
    lean_dec_ref(v_inst_1103_);
    lean_dec(v_inst_1102_);
    return v_res_1106_;
}
pub unsafe fn l_Std_IterM_filter___redArg(mut v_it_1107_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_1107_);
    return v_it_1107_;
}
pub unsafe fn l_Std_IterM_filter___redArg___boxed(
    mut v_it_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Std_IterM_filter___redArg(v_it_1108_);
    lean_dec(v_it_1108_);
    return v_res_1109_;
}
pub unsafe fn l_Std_IterM_filter(
    mut v_00_u03b1_1110_: *mut LeanObject,
    mut v_00_u03b2_1111_: *mut LeanObject,
    mut v_m_1112_: *mut LeanObject,
    mut v_inst_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_f_1115_: *mut LeanObject,
    mut v_it_1116_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_1116_);
    return v_it_1116_;
}
pub unsafe fn l_Std_IterM_filter___boxed(
    mut v_00_u03b1_1117_: *mut LeanObject,
    mut v_00_u03b2_1118_: *mut LeanObject,
    mut v_m_1119_: *mut LeanObject,
    mut v_inst_1120_: *mut LeanObject,
    mut v_inst_1121_: *mut LeanObject,
    mut v_f_1122_: *mut LeanObject,
    mut v_it_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1124_: *mut LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_Std_IterM_filter(
        v_00_u03b1_1117_,
        v_00_u03b2_1118_,
        v_m_1119_,
        v_inst_1120_,
        v_inst_1121_,
        v_f_1122_,
        v_it_1123_,
    );
    lean_dec(v_it_1123_);
    lean_dec_ref(v_f_1122_);
    lean_dec_ref(v_inst_1121_);
    lean_dec(v_inst_1120_);
    return v_res_1124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
}
