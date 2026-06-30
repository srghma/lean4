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
pub static l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap___redArg(
    mut v_it_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_563_);
    return v_it_563_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap___redArg___boxed(
    mut v_it_564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Std_IterM_InternalCombinators_filterMap___redArg(v_it_564_);
    leanh::lean_dec(v_it_564_);
    return v_res_565_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap(
    mut v_00_u03b1_566_: *mut leanh::LeanObject,
    mut v_00_u03b2_567_: *mut leanh::LeanObject,
    mut v_00_u03b3_568_: *mut leanh::LeanObject,
    mut v_m_569_: *mut leanh::LeanObject,
    mut v_n_570_: *mut leanh::LeanObject,
    mut v_lift_571_: *mut leanh::LeanObject,
    mut v_inst_572_: *mut leanh::LeanObject,
    mut v_f_573_: *mut leanh::LeanObject,
    mut v_it_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_574_);
    return v_it_574_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_filterMap___boxed(
    mut v_00_u03b1_575_: *mut leanh::LeanObject,
    mut v_00_u03b2_576_: *mut leanh::LeanObject,
    mut v_00_u03b3_577_: *mut leanh::LeanObject,
    mut v_m_578_: *mut leanh::LeanObject,
    mut v_n_579_: *mut leanh::LeanObject,
    mut v_lift_580_: *mut leanh::LeanObject,
    mut v_inst_581_: *mut leanh::LeanObject,
    mut v_f_582_: *mut leanh::LeanObject,
    mut v_it_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_584_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_583_);
    leanh::lean_dec(v_f_582_);
    leanh::lean_dec(v_inst_581_);
    leanh::lean_dec(v_lift_580_);
    return v_res_584_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map___redArg(
    mut v_it_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_585_);
    return v_it_585_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map___redArg___boxed(
    mut v_it_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_587_ = l_Std_IterM_InternalCombinators_map___redArg(v_it_586_);
    leanh::lean_dec(v_it_586_);
    return v_res_587_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map(
    mut v_00_u03b1_588_: *mut leanh::LeanObject,
    mut v_00_u03b2_589_: *mut leanh::LeanObject,
    mut v_00_u03b3_590_: *mut leanh::LeanObject,
    mut v_m_591_: *mut leanh::LeanObject,
    mut v_n_592_: *mut leanh::LeanObject,
    mut v_inst_593_: *mut leanh::LeanObject,
    mut v_lift_594_: *mut leanh::LeanObject,
    mut v_inst_595_: *mut leanh::LeanObject,
    mut v_f_596_: *mut leanh::LeanObject,
    mut v_it_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_597_);
    return v_it_597_;
}
pub unsafe fn l_Std_IterM_InternalCombinators_map___boxed(
    mut v_00_u03b1_598_: *mut leanh::LeanObject,
    mut v_00_u03b2_599_: *mut leanh::LeanObject,
    mut v_00_u03b3_600_: *mut leanh::LeanObject,
    mut v_m_601_: *mut leanh::LeanObject,
    mut v_n_602_: *mut leanh::LeanObject,
    mut v_inst_603_: *mut leanh::LeanObject,
    mut v_lift_604_: *mut leanh::LeanObject,
    mut v_inst_605_: *mut leanh::LeanObject,
    mut v_f_606_: *mut leanh::LeanObject,
    mut v_it_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_608_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_607_);
    leanh::lean_dec(v_f_606_);
    leanh::lean_dec(v_inst_605_);
    leanh::lean_dec(v_lift_604_);
    leanh::lean_dec_ref(v_inst_603_);
    return v_res_608_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition___redArg(
    mut v_it_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_609_);
    return v_it_609_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition___redArg___boxed(
    mut v_it_610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Std_IterM_filterMapWithPostcondition___redArg(v_it_610_);
    leanh::lean_dec(v_it_610_);
    return v_res_611_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition(
    mut v_00_u03b1_612_: *mut leanh::LeanObject,
    mut v_00_u03b2_613_: *mut leanh::LeanObject,
    mut v_00_u03b3_614_: *mut leanh::LeanObject,
    mut v_m_615_: *mut leanh::LeanObject,
    mut v_n_616_: *mut leanh::LeanObject,
    mut v_inst_617_: *mut leanh::LeanObject,
    mut v_inst_618_: *mut leanh::LeanObject,
    mut v_f_619_: *mut leanh::LeanObject,
    mut v_it_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_620_);
    return v_it_620_;
}
pub unsafe fn l_Std_IterM_filterMapWithPostcondition___boxed(
    mut v_00_u03b1_621_: *mut leanh::LeanObject,
    mut v_00_u03b2_622_: *mut leanh::LeanObject,
    mut v_00_u03b3_623_: *mut leanh::LeanObject,
    mut v_m_624_: *mut leanh::LeanObject,
    mut v_n_625_: *mut leanh::LeanObject,
    mut v_inst_626_: *mut leanh::LeanObject,
    mut v_inst_627_: *mut leanh::LeanObject,
    mut v_f_628_: *mut leanh::LeanObject,
    mut v_it_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_630_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_629_);
    leanh::lean_dec(v_f_628_);
    leanh::lean_dec(v_inst_627_);
    leanh::lean_dec(v_inst_626_);
    return v_res_630_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(
    mut v_it_631_: *mut leanh::LeanObject,
    mut v_toPure_632_: *mut leanh::LeanObject,
    mut v_____do__lift_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_633_) == 0 {
        let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_634_, 0, v_it_631_);
        v___x_635_ =
            leanh::lean_apply_2(v_toPure_632_, leanh::lean_box(0), v___x_634_);
        return v___x_635_;
    } else {
        let mut v_val_636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_636_ = leanh::lean_ctor_get(v_____do__lift_633_, 0);
        leanh::lean_inc(v_val_636_);
        v___x_637_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_637_, 0, v_it_631_);
        leanh::lean_ctor_set(v___x_637_, 1, v_val_636_);
        v___x_638_ =
            leanh::lean_apply_2(v_toPure_632_, leanh::lean_box(0), v___x_637_);
        return v___x_638_;
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed(
    mut v_it_639_: *mut leanh::LeanObject,
    mut v_toPure_640_: *mut leanh::LeanObject,
    mut v_____do__lift_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(
        v_it_639_,
        v_toPure_640_,
        v_____do__lift_641_,
    );
    leanh::lean_dec(v_____do__lift_641_);
    return v_res_642_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1(
    mut v_toPure_643_: *mut leanh::LeanObject,
    mut v_f_644_: *mut leanh::LeanObject,
    mut v_toBind_645_: *mut leanh::LeanObject,
    mut v_____do__lift_646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_646_) {
                0 => {
                    v_it_647_ = leanh::lean_ctor_get(v_____do__lift_646_, 0);
                    leanh::lean_inc(v_it_647_);
                    v_out_648_ = leanh::lean_ctor_get(v_____do__lift_646_, 1);
                    leanh::lean_inc(v_out_648_);
                    leanh::lean_dec_ref_known(v_____do__lift_646_, 2);
                    v___f_649_ = leanh::lean_alloc_closure(
                        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_649_, 0, v_it_647_);
                    leanh::lean_closure_set(v___f_649_, 1, v_toPure_643_);
                    v___x_650_ = leanh::lean_apply_1(v_f_644_, v_out_648_);
                    v___x_651_ = leanh::lean_apply_4(
                        v_toBind_645_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_650_,
                        v___f_649_,
                    );
                    return v___x_651_;
                }
                1 => {
                    leanh::lean_dec(v_toBind_645_);
                    leanh::lean_dec(v_f_644_);
                    v_it_652_ = leanh::lean_ctor_get(v_____do__lift_646_, 0);
                    v_isSharedCheck_660_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_646_)) as u8;
                    if v_isSharedCheck_660_ == 0 {
                        v___x_654_ = v_____do__lift_646_;
                        v_isShared_655_ = v_isSharedCheck_660_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_652_);
                        leanh::lean_dec(v_____do__lift_646_);
                        v___x_654_ = leanh::lean_box(0);
                        v_isShared_655_ = v_isSharedCheck_660_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_toBind_645_);
                    leanh::lean_dec(v_f_644_);
                    v___x_661_ = leanh::lean_box(2);
                    v___x_662_ = leanh::lean_apply_2(
                        v_toPure_643_,
                        leanh::lean_box(0),
                        v___x_661_,
                    );
                    return v___x_662_;
                }
            },
            1 => {
                if v_isShared_655_ == 0 {
                    v___x_657_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v_it_652_);
                    v___x_657_ = v_reuseFailAlloc_659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_658_ = leanh::lean_apply_2(
                    v_toPure_643_,
                    leanh::lean_box(0),
                    v___x_657_,
                );
                return v___x_658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2(
    mut v_inst_663_: *mut leanh::LeanObject,
    mut v_lift_664_: *mut leanh::LeanObject,
    mut v_toBind_665_: *mut leanh::LeanObject,
    mut v___f_666_: *mut leanh::LeanObject,
    mut v_it_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = leanh::lean_apply_1(v_inst_663_, v_it_667_);
    v___x_669_ = leanh::lean_apply_2(v_lift_664_, leanh::lean_box(0), v___x_668_);
    v___x_670_ = leanh::lean_apply_4(
        v_toBind_665_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_669_,
        v___f_666_,
    );
    return v___x_670_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator___redArg(
    mut v_lift_671_: *mut leanh::LeanObject,
    mut v_f_672_: *mut leanh::LeanObject,
    mut v_inst_673_: *mut leanh::LeanObject,
    mut v_inst_674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_675_ = leanh::lean_ctor_get(v_inst_674_, 0);
    leanh::lean_inc_ref(v_toApplicative_675_);
    v_toBind_676_ = leanh::lean_ctor_get(v_inst_674_, 1);
    leanh::lean_inc_n(v_toBind_676_, 2);
    leanh::lean_dec_ref(v_inst_674_);
    v_toPure_677_ = leanh::lean_ctor_get(v_toApplicative_675_, 1);
    leanh::lean_inc(v_toPure_677_);
    leanh::lean_dec_ref(v_toApplicative_675_);
    v___f_678_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_678_, 0, v_toPure_677_);
    leanh::lean_closure_set(v___f_678_, 1, v_f_672_);
    leanh::lean_closure_set(v___f_678_, 2, v_toBind_676_);
    v___f_679_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_679_, 0, v_inst_673_);
    leanh::lean_closure_set(v___f_679_, 1, v_lift_671_);
    leanh::lean_closure_set(v___f_679_, 2, v_toBind_676_);
    leanh::lean_closure_set(v___f_679_, 3, v___f_678_);
    return v___f_679_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIterator(
    mut v_00_u03b1_680_: *mut leanh::LeanObject,
    mut v_00_u03b2_681_: *mut leanh::LeanObject,
    mut v_00_u03b3_682_: *mut leanh::LeanObject,
    mut v_m_683_: *mut leanh::LeanObject,
    mut v_n_684_: *mut leanh::LeanObject,
    mut v_lift_685_: *mut leanh::LeanObject,
    mut v_f_686_: *mut leanh::LeanObject,
    mut v_inst_687_: *mut leanh::LeanObject,
    mut v_inst_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg(
        v_lift_685_,
        v_f_686_,
        v_inst_687_,
        v_inst_688_,
    );
    return v___x_689_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0(
    mut v_a_690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_691_, 0, v_a_690_);
    return v___x_691_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2(
    mut v_toFunctor_692_: *mut leanh::LeanObject,
    mut v_toPure_693_: *mut leanh::LeanObject,
    mut v_f_694_: *mut leanh::LeanObject,
    mut v___f_695_: *mut leanh::LeanObject,
    mut v_toBind_696_: *mut leanh::LeanObject,
    mut v_____do__lift_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_708_: u8 = 0;
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_697_) {
                0 => {
                    v_it_698_ = leanh::lean_ctor_get(v_____do__lift_697_, 0);
                    leanh::lean_inc(v_it_698_);
                    v_out_699_ = leanh::lean_ctor_get(v_____do__lift_697_, 1);
                    leanh::lean_inc(v_out_699_);
                    leanh::lean_dec_ref_known(v_____do__lift_697_, 2);
                    v_map_700_ = leanh::lean_ctor_get(v_toFunctor_692_, 0);
                    leanh::lean_inc(v_map_700_);
                    leanh::lean_dec_ref(v_toFunctor_692_);
                    v___f_701_ = leanh::lean_alloc_closure(
                        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_701_, 0, v_it_698_);
                    leanh::lean_closure_set(v___f_701_, 1, v_toPure_693_);
                    v___x_702_ = leanh::lean_apply_1(v_f_694_, v_out_699_);
                    v___x_703_ = leanh::lean_apply_4(
                        v_map_700_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_695_,
                        v___x_702_,
                    );
                    v___x_704_ = leanh::lean_apply_4(
                        v_toBind_696_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_703_,
                        v___f_701_,
                    );
                    return v___x_704_;
                }
                1 => {
                    leanh::lean_dec(v_toBind_696_);
                    leanh::lean_dec_ref(v___f_695_);
                    leanh::lean_dec(v_f_694_);
                    leanh::lean_dec_ref(v_toFunctor_692_);
                    v_it_705_ = leanh::lean_ctor_get(v_____do__lift_697_, 0);
                    v_isSharedCheck_713_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_697_)) as u8;
                    if v_isSharedCheck_713_ == 0 {
                        v___x_707_ = v_____do__lift_697_;
                        v_isShared_708_ = v_isSharedCheck_713_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_705_);
                        leanh::lean_dec(v_____do__lift_697_);
                        v___x_707_ = leanh::lean_box(0);
                        v_isShared_708_ = v_isSharedCheck_713_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_toBind_696_);
                    leanh::lean_dec_ref(v___f_695_);
                    leanh::lean_dec(v_f_694_);
                    leanh::lean_dec_ref(v_toFunctor_692_);
                    v___x_714_ = leanh::lean_box(2);
                    v___x_715_ = leanh::lean_apply_2(
                        v_toPure_693_,
                        leanh::lean_box(0),
                        v___x_714_,
                    );
                    return v___x_715_;
                }
            },
            1 => {
                if v_isShared_708_ == 0 {
                    v___x_710_ = v___x_707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_712_, 0, v_it_705_);
                    v___x_710_ = v_reuseFailAlloc_712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_711_ = leanh::lean_apply_2(
                    v_toPure_693_,
                    leanh::lean_box(0),
                    v___x_710_,
                );
                return v___x_711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3___redArg(
    mut v_inst_717_: *mut leanh::LeanObject,
    mut v_inst_718_: *mut leanh::LeanObject,
    mut v_lift_719_: *mut leanh::LeanObject,
    mut v_f_720_: *mut leanh::LeanObject,
    mut v_it_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_722_ = leanh::lean_ctor_get(v_inst_717_, 0);
    leanh::lean_inc_ref(v_toApplicative_722_);
    v_toBind_723_ = leanh::lean_ctor_get(v_inst_717_, 1);
    leanh::lean_inc_n(v_toBind_723_, 2);
    leanh::lean_dec_ref(v_inst_717_);
    v_toFunctor_724_ = leanh::lean_ctor_get(v_toApplicative_722_, 0);
    leanh::lean_inc_ref(v_toFunctor_724_);
    v_toPure_725_ = leanh::lean_ctor_get(v_toApplicative_722_, 1);
    leanh::lean_inc(v_toPure_725_);
    leanh::lean_dec_ref(v_toApplicative_722_);
    v___f_726_ = l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0;
    v___x_727_ = leanh::lean_apply_1(v_inst_718_, v_it_721_);
    v___x_728_ = leanh::lean_apply_2(v_lift_719_, leanh::lean_box(0), v___x_727_);
    v___f_729_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_729_, 0, v_toFunctor_724_);
    leanh::lean_closure_set(v___f_729_, 1, v_toPure_725_);
    leanh::lean_closure_set(v___f_729_, 2, v_f_720_);
    leanh::lean_closure_set(v___f_729_, 3, v___f_726_);
    leanh::lean_closure_set(v___f_729_, 4, v_toBind_723_);
    v___x_730_ = leanh::lean_apply_4(
        v_toBind_723_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_728_,
        v___f_729_,
    );
    return v___x_730_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___aux__3(
    mut v_00_u03b1_731_: *mut leanh::LeanObject,
    mut v_00_u03b2_732_: *mut leanh::LeanObject,
    mut v_00_u03b3_733_: *mut leanh::LeanObject,
    mut v_m_734_: *mut leanh::LeanObject,
    mut v_n_735_: *mut leanh::LeanObject,
    mut v_inst_736_: *mut leanh::LeanObject,
    mut v_inst_737_: *mut leanh::LeanObject,
    mut v_lift_738_: *mut leanh::LeanObject,
    mut v_f_739_: *mut leanh::LeanObject,
    mut v_it_740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_741_ = leanh::lean_ctor_get(v_inst_736_, 0);
    leanh::lean_inc_ref(v_toApplicative_741_);
    v_toBind_742_ = leanh::lean_ctor_get(v_inst_736_, 1);
    leanh::lean_inc_n(v_toBind_742_, 2);
    leanh::lean_dec_ref(v_inst_736_);
    v_toFunctor_743_ = leanh::lean_ctor_get(v_toApplicative_741_, 0);
    leanh::lean_inc_ref(v_toFunctor_743_);
    v_toPure_744_ = leanh::lean_ctor_get(v_toApplicative_741_, 1);
    leanh::lean_inc(v_toPure_744_);
    leanh::lean_dec_ref(v_toApplicative_741_);
    v___f_745_ = l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0;
    v___x_746_ = leanh::lean_apply_1(v_inst_737_, v_it_740_);
    v___x_747_ = leanh::lean_apply_2(v_lift_738_, leanh::lean_box(0), v___x_746_);
    v___f_748_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_748_, 0, v_toFunctor_743_);
    leanh::lean_closure_set(v___f_748_, 1, v_toPure_744_);
    leanh::lean_closure_set(v___f_748_, 2, v_f_739_);
    leanh::lean_closure_set(v___f_748_, 3, v___f_745_);
    leanh::lean_closure_set(v___f_748_, 4, v_toBind_742_);
    v___x_749_ = leanh::lean_apply_4(
        v_toBind_742_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_747_,
        v___f_748_,
    );
    return v___x_749_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator___redArg(
    mut v_inst_750_: *mut leanh::LeanObject,
    mut v_inst_751_: *mut leanh::LeanObject,
    mut v_lift_752_: *mut leanh::LeanObject,
    mut v_f_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___x_754_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_754_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_754_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_754_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_754_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_754_, 5, v_inst_750_);
    leanh::lean_closure_set(v___x_754_, 6, v_inst_751_);
    leanh::lean_closure_set(v___x_754_, 7, v_lift_752_);
    leanh::lean_closure_set(v___x_754_, 8, v_f_753_);
    return v___x_754_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIterator(
    mut v_00_u03b1_755_: *mut leanh::LeanObject,
    mut v_00_u03b2_756_: *mut leanh::LeanObject,
    mut v_00_u03b3_757_: *mut leanh::LeanObject,
    mut v_m_758_: *mut leanh::LeanObject,
    mut v_n_759_: *mut leanh::LeanObject,
    mut v_inst_760_: *mut leanh::LeanObject,
    mut v_inst_761_: *mut leanh::LeanObject,
    mut v_lift_762_: *mut leanh::LeanObject,
    mut v_f_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___x_764_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_764_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_764_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_764_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_764_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_764_, 5, v_inst_760_);
    leanh::lean_closure_set(v___x_764_, 6, v_inst_761_);
    leanh::lean_closure_set(v___x_764_, 7, v_lift_762_);
    leanh::lean_closure_set(v___x_764_, 8, v_f_763_);
    return v___x_764_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(
    mut v_00_u03b1_765_: *mut leanh::LeanObject,
    mut v_00_u03b2_766_: *mut leanh::LeanObject,
    mut v_00_u03b3_767_: *mut leanh::LeanObject,
    mut v_m_768_: *mut leanh::LeanObject,
    mut v_n_769_: *mut leanh::LeanObject,
    mut v_inst_770_: *mut leanh::LeanObject,
    mut v_inst_771_: *mut leanh::LeanObject,
    mut v_lift_772_: *mut leanh::LeanObject,
    mut v_f_773_: *mut leanh::LeanObject,
    mut v_inst_774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_775_ = leanh::lean_box(0);
    return v___x_775_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(
    mut v_00_u03b1_776_: *mut leanh::LeanObject,
    mut v_00_u03b2_777_: *mut leanh::LeanObject,
    mut v_00_u03b3_778_: *mut leanh::LeanObject,
    mut v_m_779_: *mut leanh::LeanObject,
    mut v_n_780_: *mut leanh::LeanObject,
    mut v_inst_781_: *mut leanh::LeanObject,
    mut v_inst_782_: *mut leanh::LeanObject,
    mut v_lift_783_: *mut leanh::LeanObject,
    mut v_f_784_: *mut leanh::LeanObject,
    mut v_inst_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(v_00_u03b1_776_, v_00_u03b2_777_, v_00_u03b3_778_, v_m_779_, v_n_780_, v_inst_781_, v_inst_782_, v_lift_783_, v_f_784_, v_inst_785_);
    leanh::lean_dec(v_f_784_);
    leanh::lean_dec(v_lift_783_);
    leanh::lean_dec(v_inst_782_);
    leanh::lean_dec_ref(v_inst_781_);
    return v_res_786_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(
    mut v_00_u03b1_787_: *mut leanh::LeanObject,
    mut v_00_u03b2_788_: *mut leanh::LeanObject,
    mut v_00_u03b3_789_: *mut leanh::LeanObject,
    mut v_m_790_: *mut leanh::LeanObject,
    mut v_n_791_: *mut leanh::LeanObject,
    mut v_inst_792_: *mut leanh::LeanObject,
    mut v_inst_793_: *mut leanh::LeanObject,
    mut v_lift_794_: *mut leanh::LeanObject,
    mut v_f_795_: *mut leanh::LeanObject,
    mut v_inst_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = leanh::lean_box(0);
    return v___x_797_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(
    mut v_00_u03b1_798_: *mut leanh::LeanObject,
    mut v_00_u03b2_799_: *mut leanh::LeanObject,
    mut v_00_u03b3_800_: *mut leanh::LeanObject,
    mut v_m_801_: *mut leanh::LeanObject,
    mut v_n_802_: *mut leanh::LeanObject,
    mut v_inst_803_: *mut leanh::LeanObject,
    mut v_inst_804_: *mut leanh::LeanObject,
    mut v_lift_805_: *mut leanh::LeanObject,
    mut v_f_806_: *mut leanh::LeanObject,
    mut v_inst_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(v_00_u03b1_798_, v_00_u03b2_799_, v_00_u03b3_800_, v_m_801_, v_n_802_, v_inst_803_, v_inst_804_, v_lift_805_, v_f_806_, v_inst_807_);
    leanh::lean_dec(v_f_806_);
    leanh::lean_dec(v_lift_805_);
    leanh::lean_dec(v_inst_804_);
    leanh::lean_dec_ref(v_inst_803_);
    return v_res_808_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(
    mut v_toPure_809_: *mut leanh::LeanObject,
    mut v_recur_810_: *mut leanh::LeanObject,
    mut v_it_811_: *mut leanh::LeanObject,
    mut v_____do__lift_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_812_) == 0 {
        let mut v_a_813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_it_811_);
        leanh::lean_dec(v_recur_810_);
        v_a_813_ = leanh::lean_ctor_get(v_____do__lift_812_, 0);
        leanh::lean_inc(v_a_813_);
        leanh::lean_dec_ref_known(v_____do__lift_812_, 1);
        v___x_814_ = leanh::lean_apply_2(v_toPure_809_, leanh::lean_box(0), v_a_813_);
        return v___x_814_;
    } else {
        let mut v_a_815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_809_);
        v_a_815_ = leanh::lean_ctor_get(v_____do__lift_812_, 0);
        leanh::lean_inc(v_a_815_);
        leanh::lean_dec_ref_known(v_____do__lift_812_, 1);
        v___x_816_ = leanh::lean_apply_4(
            v_recur_810_,
            v_it_811_,
            v_a_815_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_816_;
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(
    mut v_toPure_817_: *mut leanh::LeanObject,
    mut v_recur_818_: *mut leanh::LeanObject,
    mut v___y_819_: *mut leanh::LeanObject,
    mut v_acc_820_: *mut leanh::LeanObject,
    mut v_toBind_821_: *mut leanh::LeanObject,
    mut v_s_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_822_) {
        0 => {
            let mut v_it_823_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_824_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_825_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_823_ = leanh::lean_ctor_get(v_s_822_, 0);
            leanh::lean_inc(v_it_823_);
            v_out_824_ = leanh::lean_ctor_get(v_s_822_, 1);
            leanh::lean_inc(v_out_824_);
            leanh::lean_dec_ref_known(v_s_822_, 2);
            v___f_825_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_825_, 0, v_toPure_817_);
            leanh::lean_closure_set(v___f_825_, 1, v_recur_818_);
            leanh::lean_closure_set(v___f_825_, 2, v_it_823_);
            v___x_826_ = leanh::lean_apply_3(
                v___y_819_,
                v_out_824_,
                leanh::lean_box(0),
                v_acc_820_,
            );
            v___x_827_ = leanh::lean_apply_4(
                v_toBind_821_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_826_,
                v___f_825_,
            );
            return v___x_827_;
        }
        1 => {
            let mut v_it_828_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_821_);
            leanh::lean_dec(v___y_819_);
            leanh::lean_dec(v_toPure_817_);
            v_it_828_ = leanh::lean_ctor_get(v_s_822_, 0);
            leanh::lean_inc(v_it_828_);
            leanh::lean_dec_ref_known(v_s_822_, 1);
            v___x_829_ = leanh::lean_apply_4(
                v_recur_818_,
                v_it_828_,
                v_acc_820_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_829_;
        }
        _ => {
            let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_821_);
            leanh::lean_dec(v___y_819_);
            leanh::lean_dec(v_recur_818_);
            v___x_830_ =
                leanh::lean_apply_2(v_toPure_817_, leanh::lean_box(0), v_acc_820_);
            return v___x_830_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(
    mut v_inst_831_: *mut leanh::LeanObject,
    mut v_toPure_832_: *mut leanh::LeanObject,
    mut v___y_833_: *mut leanh::LeanObject,
    mut v_toBind_834_: *mut leanh::LeanObject,
    mut v_f_835_: *mut leanh::LeanObject,
    mut v_inst_836_: *mut leanh::LeanObject,
    mut v_lift_837_: *mut leanh::LeanObject,
    mut v_lift_838_: *mut leanh::LeanObject,
    mut v_it_839_: *mut leanh::LeanObject,
    mut v_acc_840_: *mut leanh::LeanObject,
    mut v_hP_841_: *mut leanh::LeanObject,
    mut v_recur_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_843_ = leanh::lean_ctor_get(v_inst_831_, 0);
    leanh::lean_inc_ref(v_toApplicative_843_);
    v_toBind_844_ = leanh::lean_ctor_get(v_inst_831_, 1);
    leanh::lean_inc_n(v_toBind_844_, 2);
    leanh::lean_dec_ref(v_inst_831_);
    v_toPure_845_ = leanh::lean_ctor_get(v_toApplicative_843_, 1);
    leanh::lean_inc(v_toPure_845_);
    leanh::lean_dec_ref(v_toApplicative_843_);
    v___f_846_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_846_, 0, v_toPure_832_);
    leanh::lean_closure_set(v___f_846_, 1, v_recur_842_);
    leanh::lean_closure_set(v___f_846_, 2, v___y_833_);
    leanh::lean_closure_set(v___f_846_, 3, v_acc_840_);
    leanh::lean_closure_set(v___f_846_, 4, v_toBind_834_);
    v___f_847_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_847_, 0, v_toPure_845_);
    leanh::lean_closure_set(v___f_847_, 1, v_f_835_);
    leanh::lean_closure_set(v___f_847_, 2, v_toBind_844_);
    v___x_848_ = leanh::lean_apply_1(v_inst_836_, v_it_839_);
    v___x_849_ = leanh::lean_apply_2(v_lift_837_, leanh::lean_box(0), v___x_848_);
    v___x_850_ = leanh::lean_apply_4(
        v_toBind_844_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_849_,
        v___f_847_,
    );
    v___x_851_ = leanh::lean_apply_4(
        v_lift_838_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_846_,
        v___x_850_,
    );
    return v___x_851_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(
    mut v_inst_852_: *mut leanh::LeanObject,
    mut v_inst_853_: *mut leanh::LeanObject,
    mut v_f_854_: *mut leanh::LeanObject,
    mut v_inst_855_: *mut leanh::LeanObject,
    mut v_lift_856_: *mut leanh::LeanObject,
    mut v_lift_857_: *mut leanh::LeanObject,
    mut v_00_u03b3_858_: *mut leanh::LeanObject,
    mut v_Pl_859_: *mut leanh::LeanObject,
    mut v_it_860_: *mut leanh::LeanObject,
    mut v_init_861_: *mut leanh::LeanObject,
    mut v___y_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_863_ = leanh::lean_ctor_get(v_inst_852_, 0);
    leanh::lean_inc_ref(v_toApplicative_863_);
    v_toBind_864_ = leanh::lean_ctor_get(v_inst_852_, 1);
    leanh::lean_inc(v_toBind_864_);
    leanh::lean_dec_ref(v_inst_852_);
    v_toPure_865_ = leanh::lean_ctor_get(v_toApplicative_863_, 1);
    leanh::lean_inc(v_toPure_865_);
    leanh::lean_dec_ref(v_toApplicative_863_);
    v___f_866_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4
            as *mut core::ffi::c_void,
        12,
        8,
    );
    leanh::lean_closure_set(v___f_866_, 0, v_inst_853_);
    leanh::lean_closure_set(v___f_866_, 1, v_toPure_865_);
    leanh::lean_closure_set(v___f_866_, 2, v___y_862_);
    leanh::lean_closure_set(v___f_866_, 3, v_toBind_864_);
    leanh::lean_closure_set(v___f_866_, 4, v_f_854_);
    leanh::lean_closure_set(v___f_866_, 5, v_inst_855_);
    leanh::lean_closure_set(v___f_866_, 6, v_lift_856_);
    leanh::lean_closure_set(v___f_866_, 7, v_lift_857_);
    v___x_867_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_866_,
        v_it_860_,
        v_init_861_,
        leanh::lean_box(0),
    );
    return v___x_867_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(
    mut v_inst_868_: *mut leanh::LeanObject,
    mut v_inst_869_: *mut leanh::LeanObject,
    mut v_inst_870_: *mut leanh::LeanObject,
    mut v_lift_871_: *mut leanh::LeanObject,
    mut v_f_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_873_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        11,
        5,
    );
    leanh::lean_closure_set(v___f_873_, 0, v_inst_869_);
    leanh::lean_closure_set(v___f_873_, 1, v_inst_868_);
    leanh::lean_closure_set(v___f_873_, 2, v_f_872_);
    leanh::lean_closure_set(v___f_873_, 3, v_inst_870_);
    leanh::lean_closure_set(v___f_873_, 4, v_lift_871_);
    return v___f_873_;
}
pub unsafe fn l_Std_Iterators_Types_FilterMap_instIteratorLoop(
    mut v_00_u03b1_874_: *mut leanh::LeanObject,
    mut v_00_u03b2_875_: *mut leanh::LeanObject,
    mut v_00_u03b3_876_: *mut leanh::LeanObject,
    mut v_m_877_: *mut leanh::LeanObject,
    mut v_n_878_: *mut leanh::LeanObject,
    mut v_o_879_: *mut leanh::LeanObject,
    mut v_inst_880_: *mut leanh::LeanObject,
    mut v_inst_881_: *mut leanh::LeanObject,
    mut v_inst_882_: *mut leanh::LeanObject,
    mut v_lift_883_: *mut leanh::LeanObject,
    mut v_f_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_885_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        11,
        5,
    );
    leanh::lean_closure_set(v___f_885_, 0, v_inst_881_);
    leanh::lean_closure_set(v___f_885_, 1, v_inst_880_);
    leanh::lean_closure_set(v___f_885_, 2, v_f_884_);
    leanh::lean_closure_set(v___f_885_, 3, v_inst_882_);
    leanh::lean_closure_set(v___f_885_, 4, v_lift_883_);
    return v___f_885_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5(
    mut v_inst_886_: *mut leanh::LeanObject,
    mut v_toPure_887_: *mut leanh::LeanObject,
    mut v___y_888_: *mut leanh::LeanObject,
    mut v_toBind_889_: *mut leanh::LeanObject,
    mut v_inst_890_: *mut leanh::LeanObject,
    mut v_lift_891_: *mut leanh::LeanObject,
    mut v_f_892_: *mut leanh::LeanObject,
    mut v___f_893_: *mut leanh::LeanObject,
    mut v_lift_894_: *mut leanh::LeanObject,
    mut v_it_895_: *mut leanh::LeanObject,
    mut v_acc_896_: *mut leanh::LeanObject,
    mut v_hP_897_: *mut leanh::LeanObject,
    mut v_recur_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_899_ = leanh::lean_ctor_get(v_inst_886_, 0);
    leanh::lean_inc_ref(v_toApplicative_899_);
    v_toBind_900_ = leanh::lean_ctor_get(v_inst_886_, 1);
    leanh::lean_inc_n(v_toBind_900_, 2);
    leanh::lean_dec_ref(v_inst_886_);
    v_toFunctor_901_ = leanh::lean_ctor_get(v_toApplicative_899_, 0);
    leanh::lean_inc_ref(v_toFunctor_901_);
    v_toPure_902_ = leanh::lean_ctor_get(v_toApplicative_899_, 1);
    leanh::lean_inc(v_toPure_902_);
    leanh::lean_dec_ref(v_toApplicative_899_);
    v___f_903_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_903_, 0, v_toPure_887_);
    leanh::lean_closure_set(v___f_903_, 1, v_recur_898_);
    leanh::lean_closure_set(v___f_903_, 2, v___y_888_);
    leanh::lean_closure_set(v___f_903_, 3, v_acc_896_);
    leanh::lean_closure_set(v___f_903_, 4, v_toBind_889_);
    v___x_904_ = leanh::lean_apply_1(v_inst_890_, v_it_895_);
    v___x_905_ = leanh::lean_apply_2(v_lift_891_, leanh::lean_box(0), v___x_904_);
    v___f_906_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_906_, 0, v_toFunctor_901_);
    leanh::lean_closure_set(v___f_906_, 1, v_toPure_902_);
    leanh::lean_closure_set(v___f_906_, 2, v_f_892_);
    leanh::lean_closure_set(v___f_906_, 3, v___f_893_);
    leanh::lean_closure_set(v___f_906_, 4, v_toBind_900_);
    v___x_907_ = leanh::lean_apply_4(
        v_toBind_900_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_905_,
        v___f_906_,
    );
    v___x_908_ = leanh::lean_apply_4(
        v_lift_894_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_903_,
        v___x_907_,
    );
    return v___x_908_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(
    mut v_inst_909_: *mut leanh::LeanObject,
    mut v_inst_910_: *mut leanh::LeanObject,
    mut v_inst_911_: *mut leanh::LeanObject,
    mut v_lift_912_: *mut leanh::LeanObject,
    mut v_f_913_: *mut leanh::LeanObject,
    mut v___f_914_: *mut leanh::LeanObject,
    mut v_lift_915_: *mut leanh::LeanObject,
    mut v_00_u03b3_916_: *mut leanh::LeanObject,
    mut v_Pl_917_: *mut leanh::LeanObject,
    mut v_it_918_: *mut leanh::LeanObject,
    mut v_init_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_921_ = leanh::lean_ctor_get(v_inst_909_, 0);
    leanh::lean_inc_ref(v_toApplicative_921_);
    v_toBind_922_ = leanh::lean_ctor_get(v_inst_909_, 1);
    leanh::lean_inc(v_toBind_922_);
    leanh::lean_dec_ref(v_inst_909_);
    v_toPure_923_ = leanh::lean_ctor_get(v_toApplicative_921_, 1);
    leanh::lean_inc(v_toPure_923_);
    leanh::lean_dec_ref(v_toApplicative_921_);
    v___f_924_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5 as *mut core::ffi::c_void,
        13,
        9,
    );
    leanh::lean_closure_set(v___f_924_, 0, v_inst_910_);
    leanh::lean_closure_set(v___f_924_, 1, v_toPure_923_);
    leanh::lean_closure_set(v___f_924_, 2, v___y_920_);
    leanh::lean_closure_set(v___f_924_, 3, v_toBind_922_);
    leanh::lean_closure_set(v___f_924_, 4, v_inst_911_);
    leanh::lean_closure_set(v___f_924_, 5, v_lift_912_);
    leanh::lean_closure_set(v___f_924_, 6, v_f_913_);
    leanh::lean_closure_set(v___f_924_, 7, v___f_914_);
    leanh::lean_closure_set(v___f_924_, 8, v_lift_915_);
    v___x_925_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_924_,
        v_it_918_,
        v_init_919_,
        leanh::lean_box(0),
    );
    return v___x_925_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop___redArg(
    mut v_inst_926_: *mut leanh::LeanObject,
    mut v_inst_927_: *mut leanh::LeanObject,
    mut v_inst_928_: *mut leanh::LeanObject,
    mut v_lift_929_: *mut leanh::LeanObject,
    mut v_f_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_931_ = l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0;
    v___f_932_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        12,
        6,
    );
    leanh::lean_closure_set(v___f_932_, 0, v_inst_927_);
    leanh::lean_closure_set(v___f_932_, 1, v_inst_926_);
    leanh::lean_closure_set(v___f_932_, 2, v_inst_928_);
    leanh::lean_closure_set(v___f_932_, 3, v_lift_929_);
    leanh::lean_closure_set(v___f_932_, 4, v_f_930_);
    leanh::lean_closure_set(v___f_932_, 5, v___f_931_);
    return v___f_932_;
}
pub unsafe fn l_Std_Iterators_Types_Map_instIteratorLoop(
    mut v_00_u03b1_933_: *mut leanh::LeanObject,
    mut v_00_u03b2_934_: *mut leanh::LeanObject,
    mut v_00_u03b3_935_: *mut leanh::LeanObject,
    mut v_m_936_: *mut leanh::LeanObject,
    mut v_n_937_: *mut leanh::LeanObject,
    mut v_o_938_: *mut leanh::LeanObject,
    mut v_inst_939_: *mut leanh::LeanObject,
    mut v_inst_940_: *mut leanh::LeanObject,
    mut v_inst_941_: *mut leanh::LeanObject,
    mut v_lift_942_: *mut leanh::LeanObject,
    mut v_f_943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_it_945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_945_);
    return v_it_945_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition___redArg___boxed(
    mut v_it_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = l_Std_IterM_mapWithPostcondition___redArg(v_it_946_);
    leanh::lean_dec(v_it_946_);
    return v_res_947_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition(
    mut v_00_u03b1_948_: *mut leanh::LeanObject,
    mut v_00_u03b2_949_: *mut leanh::LeanObject,
    mut v_00_u03b3_950_: *mut leanh::LeanObject,
    mut v_m_951_: *mut leanh::LeanObject,
    mut v_n_952_: *mut leanh::LeanObject,
    mut v_inst_953_: *mut leanh::LeanObject,
    mut v_inst_954_: *mut leanh::LeanObject,
    mut v_inst_955_: *mut leanh::LeanObject,
    mut v_f_956_: *mut leanh::LeanObject,
    mut v_it_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_957_);
    return v_it_957_;
}
pub unsafe fn l_Std_IterM_mapWithPostcondition___boxed(
    mut v_00_u03b1_958_: *mut leanh::LeanObject,
    mut v_00_u03b2_959_: *mut leanh::LeanObject,
    mut v_00_u03b3_960_: *mut leanh::LeanObject,
    mut v_m_961_: *mut leanh::LeanObject,
    mut v_n_962_: *mut leanh::LeanObject,
    mut v_inst_963_: *mut leanh::LeanObject,
    mut v_inst_964_: *mut leanh::LeanObject,
    mut v_inst_965_: *mut leanh::LeanObject,
    mut v_f_966_: *mut leanh::LeanObject,
    mut v_it_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_968_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_967_);
    leanh::lean_dec(v_f_966_);
    leanh::lean_dec(v_inst_965_);
    leanh::lean_dec(v_inst_964_);
    leanh::lean_dec_ref(v_inst_963_);
    return v_res_968_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition___redArg(
    mut v_it_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_969_);
    return v_it_969_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition___redArg___boxed(
    mut v_it_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Std_IterM_filterWithPostcondition___redArg(v_it_970_);
    leanh::lean_dec(v_it_970_);
    return v_res_971_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition(
    mut v_00_u03b1_972_: *mut leanh::LeanObject,
    mut v_00_u03b2_973_: *mut leanh::LeanObject,
    mut v_m_974_: *mut leanh::LeanObject,
    mut v_n_975_: *mut leanh::LeanObject,
    mut v_inst_976_: *mut leanh::LeanObject,
    mut v_inst_977_: *mut leanh::LeanObject,
    mut v_inst_978_: *mut leanh::LeanObject,
    mut v_f_979_: *mut leanh::LeanObject,
    mut v_it_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_980_);
    return v_it_980_;
}
pub unsafe fn l_Std_IterM_filterWithPostcondition___boxed(
    mut v_00_u03b1_981_: *mut leanh::LeanObject,
    mut v_00_u03b2_982_: *mut leanh::LeanObject,
    mut v_m_983_: *mut leanh::LeanObject,
    mut v_n_984_: *mut leanh::LeanObject,
    mut v_inst_985_: *mut leanh::LeanObject,
    mut v_inst_986_: *mut leanh::LeanObject,
    mut v_inst_987_: *mut leanh::LeanObject,
    mut v_f_988_: *mut leanh::LeanObject,
    mut v_it_989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_990_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_989_);
    leanh::lean_dec(v_f_988_);
    leanh::lean_dec(v_inst_987_);
    leanh::lean_dec(v_inst_986_);
    leanh::lean_dec_ref(v_inst_985_);
    return v_res_990_;
}
pub unsafe fn l_Std_IterM_filterMapM___redArg(
    mut v_it_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_991_);
    return v_it_991_;
}
pub unsafe fn l_Std_IterM_filterMapM___redArg___boxed(
    mut v_it_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Std_IterM_filterMapM___redArg(v_it_992_);
    leanh::lean_dec(v_it_992_);
    return v_res_993_;
}
pub unsafe fn l_Std_IterM_filterMapM(
    mut v_00_u03b1_994_: *mut leanh::LeanObject,
    mut v_00_u03b2_995_: *mut leanh::LeanObject,
    mut v_00_u03b3_996_: *mut leanh::LeanObject,
    mut v_m_997_: *mut leanh::LeanObject,
    mut v_n_998_: *mut leanh::LeanObject,
    mut v_inst_999_: *mut leanh::LeanObject,
    mut v_inst_1000_: *mut leanh::LeanObject,
    mut v_inst_1001_: *mut leanh::LeanObject,
    mut v_inst_1002_: *mut leanh::LeanObject,
    mut v_f_1003_: *mut leanh::LeanObject,
    mut v_it_1004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1004_);
    return v_it_1004_;
}
pub unsafe fn l_Std_IterM_filterMapM___boxed(
    mut v_00_u03b1_1005_: *mut leanh::LeanObject,
    mut v_00_u03b2_1006_: *mut leanh::LeanObject,
    mut v_00_u03b3_1007_: *mut leanh::LeanObject,
    mut v_m_1008_: *mut leanh::LeanObject,
    mut v_n_1009_: *mut leanh::LeanObject,
    mut v_inst_1010_: *mut leanh::LeanObject,
    mut v_inst_1011_: *mut leanh::LeanObject,
    mut v_inst_1012_: *mut leanh::LeanObject,
    mut v_inst_1013_: *mut leanh::LeanObject,
    mut v_f_1014_: *mut leanh::LeanObject,
    mut v_it_1015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_1015_);
    leanh::lean_dec(v_f_1014_);
    leanh::lean_dec(v_inst_1013_);
    leanh::lean_dec(v_inst_1012_);
    leanh::lean_dec_ref(v_inst_1011_);
    leanh::lean_dec(v_inst_1010_);
    return v_res_1016_;
}
pub unsafe fn l_Std_IterM_mapM___redArg(
    mut v_it_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1017_);
    return v_it_1017_;
}
pub unsafe fn l_Std_IterM_mapM___redArg___boxed(
    mut v_it_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Std_IterM_mapM___redArg(v_it_1018_);
    leanh::lean_dec(v_it_1018_);
    return v_res_1019_;
}
pub unsafe fn l_Std_IterM_mapM(
    mut v_00_u03b1_1020_: *mut leanh::LeanObject,
    mut v_00_u03b2_1021_: *mut leanh::LeanObject,
    mut v_00_u03b3_1022_: *mut leanh::LeanObject,
    mut v_m_1023_: *mut leanh::LeanObject,
    mut v_n_1024_: *mut leanh::LeanObject,
    mut v_inst_1025_: *mut leanh::LeanObject,
    mut v_inst_1026_: *mut leanh::LeanObject,
    mut v_inst_1027_: *mut leanh::LeanObject,
    mut v_inst_1028_: *mut leanh::LeanObject,
    mut v_f_1029_: *mut leanh::LeanObject,
    mut v_it_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1030_);
    return v_it_1030_;
}
pub unsafe fn l_Std_IterM_mapM___boxed(
    mut v_00_u03b1_1031_: *mut leanh::LeanObject,
    mut v_00_u03b2_1032_: *mut leanh::LeanObject,
    mut v_00_u03b3_1033_: *mut leanh::LeanObject,
    mut v_m_1034_: *mut leanh::LeanObject,
    mut v_n_1035_: *mut leanh::LeanObject,
    mut v_inst_1036_: *mut leanh::LeanObject,
    mut v_inst_1037_: *mut leanh::LeanObject,
    mut v_inst_1038_: *mut leanh::LeanObject,
    mut v_inst_1039_: *mut leanh::LeanObject,
    mut v_f_1040_: *mut leanh::LeanObject,
    mut v_it_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_1041_);
    leanh::lean_dec(v_f_1040_);
    leanh::lean_dec(v_inst_1039_);
    leanh::lean_dec(v_inst_1038_);
    leanh::lean_dec_ref(v_inst_1037_);
    leanh::lean_dec(v_inst_1036_);
    return v_res_1042_;
}
pub unsafe fn l_Std_IterM_filterM___redArg(
    mut v_it_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1043_);
    return v_it_1043_;
}
pub unsafe fn l_Std_IterM_filterM___redArg___boxed(
    mut v_it_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Std_IterM_filterM___redArg(v_it_1044_);
    leanh::lean_dec(v_it_1044_);
    return v_res_1045_;
}
pub unsafe fn l_Std_IterM_filterM(
    mut v_00_u03b1_1046_: *mut leanh::LeanObject,
    mut v_00_u03b2_1047_: *mut leanh::LeanObject,
    mut v_m_1048_: *mut leanh::LeanObject,
    mut v_n_1049_: *mut leanh::LeanObject,
    mut v_inst_1050_: *mut leanh::LeanObject,
    mut v_inst_1051_: *mut leanh::LeanObject,
    mut v_inst_1052_: *mut leanh::LeanObject,
    mut v_inst_1053_: *mut leanh::LeanObject,
    mut v_f_1054_: *mut leanh::LeanObject,
    mut v_it_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1055_);
    return v_it_1055_;
}
pub unsafe fn l_Std_IterM_filterM___boxed(
    mut v_00_u03b1_1056_: *mut leanh::LeanObject,
    mut v_00_u03b2_1057_: *mut leanh::LeanObject,
    mut v_m_1058_: *mut leanh::LeanObject,
    mut v_n_1059_: *mut leanh::LeanObject,
    mut v_inst_1060_: *mut leanh::LeanObject,
    mut v_inst_1061_: *mut leanh::LeanObject,
    mut v_inst_1062_: *mut leanh::LeanObject,
    mut v_inst_1063_: *mut leanh::LeanObject,
    mut v_f_1064_: *mut leanh::LeanObject,
    mut v_it_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_1065_);
    leanh::lean_dec(v_f_1064_);
    leanh::lean_dec(v_inst_1063_);
    leanh::lean_dec(v_inst_1062_);
    leanh::lean_dec_ref(v_inst_1061_);
    leanh::lean_dec(v_inst_1060_);
    return v_res_1066_;
}
pub unsafe fn l_Std_IterM_filterMap___redArg(
    mut v_it_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1067_);
    return v_it_1067_;
}
pub unsafe fn l_Std_IterM_filterMap___redArg___boxed(
    mut v_it_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1069_ = l_Std_IterM_filterMap___redArg(v_it_1068_);
    leanh::lean_dec(v_it_1068_);
    return v_res_1069_;
}
pub unsafe fn l_Std_IterM_filterMap(
    mut v_00_u03b1_1070_: *mut leanh::LeanObject,
    mut v_00_u03b2_1071_: *mut leanh::LeanObject,
    mut v_00_u03b3_1072_: *mut leanh::LeanObject,
    mut v_m_1073_: *mut leanh::LeanObject,
    mut v_inst_1074_: *mut leanh::LeanObject,
    mut v_inst_1075_: *mut leanh::LeanObject,
    mut v_f_1076_: *mut leanh::LeanObject,
    mut v_it_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1077_);
    return v_it_1077_;
}
pub unsafe fn l_Std_IterM_filterMap___boxed(
    mut v_00_u03b1_1078_: *mut leanh::LeanObject,
    mut v_00_u03b2_1079_: *mut leanh::LeanObject,
    mut v_00_u03b3_1080_: *mut leanh::LeanObject,
    mut v_m_1081_: *mut leanh::LeanObject,
    mut v_inst_1082_: *mut leanh::LeanObject,
    mut v_inst_1083_: *mut leanh::LeanObject,
    mut v_f_1084_: *mut leanh::LeanObject,
    mut v_it_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_1085_);
    leanh::lean_dec_ref(v_f_1084_);
    leanh::lean_dec_ref(v_inst_1083_);
    leanh::lean_dec(v_inst_1082_);
    return v_res_1086_;
}
pub unsafe fn l_Std_IterM_map___redArg(
    mut v_it_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1087_);
    return v_it_1087_;
}
pub unsafe fn l_Std_IterM_map___redArg___boxed(
    mut v_it_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Std_IterM_map___redArg(v_it_1088_);
    leanh::lean_dec(v_it_1088_);
    return v_res_1089_;
}
pub unsafe fn l_Std_IterM_map(
    mut v_00_u03b1_1090_: *mut leanh::LeanObject,
    mut v_00_u03b2_1091_: *mut leanh::LeanObject,
    mut v_00_u03b3_1092_: *mut leanh::LeanObject,
    mut v_m_1093_: *mut leanh::LeanObject,
    mut v_inst_1094_: *mut leanh::LeanObject,
    mut v_inst_1095_: *mut leanh::LeanObject,
    mut v_f_1096_: *mut leanh::LeanObject,
    mut v_it_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1097_);
    return v_it_1097_;
}
pub unsafe fn l_Std_IterM_map___boxed(
    mut v_00_u03b1_1098_: *mut leanh::LeanObject,
    mut v_00_u03b2_1099_: *mut leanh::LeanObject,
    mut v_00_u03b3_1100_: *mut leanh::LeanObject,
    mut v_m_1101_: *mut leanh::LeanObject,
    mut v_inst_1102_: *mut leanh::LeanObject,
    mut v_inst_1103_: *mut leanh::LeanObject,
    mut v_f_1104_: *mut leanh::LeanObject,
    mut v_it_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_it_1105_);
    leanh::lean_dec(v_f_1104_);
    leanh::lean_dec_ref(v_inst_1103_);
    leanh::lean_dec(v_inst_1102_);
    return v_res_1106_;
}
pub unsafe fn l_Std_IterM_filter___redArg(
    mut v_it_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1107_);
    return v_it_1107_;
}
pub unsafe fn l_Std_IterM_filter___redArg___boxed(
    mut v_it_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Std_IterM_filter___redArg(v_it_1108_);
    leanh::lean_dec(v_it_1108_);
    return v_res_1109_;
}
pub unsafe fn l_Std_IterM_filter(
    mut v_00_u03b1_1110_: *mut leanh::LeanObject,
    mut v_00_u03b2_1111_: *mut leanh::LeanObject,
    mut v_m_1112_: *mut leanh::LeanObject,
    mut v_inst_1113_: *mut leanh::LeanObject,
    mut v_inst_1114_: *mut leanh::LeanObject,
    mut v_f_1115_: *mut leanh::LeanObject,
    mut v_it_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_1116_);
    return v_it_1116_;
}
pub unsafe fn l_Std_IterM_filter___boxed(
    mut v_00_u03b1_1117_: *mut leanh::LeanObject,
    mut v_00_u03b2_1118_: *mut leanh::LeanObject,
    mut v_m_1119_: *mut leanh::LeanObject,
    mut v_inst_1120_: *mut leanh::LeanObject,
    mut v_inst_1121_: *mut leanh::LeanObject,
    mut v_f_1122_: *mut leanh::LeanObject,
    mut v_it_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_Std_IterM_filter(
        v_00_u03b1_1117_,
        v_00_u03b2_1118_,
        v_m_1119_,
        v_inst_1120_,
        v_inst_1121_,
        v_f_1122_,
        v_it_1123_,
    );
    leanh::lean_dec(v_it_1123_);
    leanh::lean_dec_ref(v_f_1122_);
    leanh::lean_dec_ref(v_inst_1121_);
    leanh::lean_dec(v_inst_1120_);
    return v_res_1124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
}