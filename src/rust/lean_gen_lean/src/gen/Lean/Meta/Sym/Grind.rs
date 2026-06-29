// Lean compiler output
// Module: Lean.Meta.Sym.Grind
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.Apply Lean.Meta.Tactic.Grind.Main Lean.Meta.Sym.Simp.Goal Lean.Meta.Sym.Intro Lean.Meta.Sym.Util Lean.Meta.Tactic.Grind.Solve Lean.Meta.Tactic.Assumption
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Lean::Meta::Sym::Apply::{
    initialize_Lean_Meta_Sym_Apply, l_Lean_Meta_Sym_BackwardRule_apply,
    runtime_initialize_Lean_Meta_Sym_Apply,
};
use crate::r#gen::Lean::Meta::Sym::Intro::{
    initialize_Lean_Meta_Sym_Intro, l_Lean_Meta_Sym_introN, l_Lean_Meta_Sym_intros,
    runtime_initialize_Lean_Meta_Sym_Intro,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Goal::{
    initialize_Lean_Meta_Sym_Simp_Goal, l_Lean_Meta_Sym_simpGoal,
    runtime_initialize_Lean_Meta_Sym_Simp_Goal,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_preprocessMVar,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_MVarId_assumptionCore,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    initialize_Lean_Meta_Tactic_Grind_Main, l_Lean_Meta_Grind_mkGoalCore,
    l_Lean_Meta_Grind_processHypotheses, runtime_initialize_Lean_Meta_Tactic_Grind_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Solve::{
    initialize_Lean_Meta_Tactic_Grind_Solve, l_Lean_Meta_Grind_solve,
    runtime_initialize_Lean_Meta_Tactic_Grind_Solve,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
pub unsafe fn l_Lean_Meta_Grind_mkGoal(
    mut v_mvarId_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
    mut v_a_630_: *mut crate::leanh::LeanObject,
    mut v_a_631_: *mut crate::leanh::LeanObject,
    mut v_a_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_638_ = l_Lean_Meta_Sym_preprocessMVar(
                    v_mvarId_627_,
                    v_a_631_,
                    v_a_632_,
                    v_a_633_,
                    v_a_634_,
                    v_a_635_,
                    v_a_636_,
                );
                if crate::leanh::lean_obj_tag(v___x_638_) == 0 {
                    v_a_639_ = crate::leanh::lean_ctor_get(v___x_638_, 0);
                    crate::leanh::lean_inc(v_a_639_);
                    crate::leanh::lean_dec_ref_known(v___x_638_, 1);
                    v___x_640_ = l_Lean_Meta_Grind_mkGoalCore(
                        v_a_639_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_,
                        v_a_634_, v_a_635_, v_a_636_,
                    );
                    return v___x_640_;
                } else {
                    v_a_641_ = crate::leanh::lean_ctor_get(v___x_638_, 0);
                    v_isSharedCheck_648_ = (!crate::leanh::lean_is_exclusive(v___x_638_)) as u8;
                    if v_isSharedCheck_648_ == 0 {
                        v___x_643_ = v___x_638_;
                        v_isShared_644_ = v_isSharedCheck_648_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_641_);
                        crate::leanh::lean_dec(v___x_638_);
                        v___x_643_ = crate::leanh::lean_box(0);
                        v_isShared_644_ = v_isSharedCheck_648_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_644_ == 0 {
                    v___x_646_ = v___x_643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
                    v___x_646_ = v_reuseFailAlloc_647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkGoal___boxed(
    mut v_mvarId_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
    mut v_a_651_: *mut crate::leanh::LeanObject,
    mut v_a_652_: *mut crate::leanh::LeanObject,
    mut v_a_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
    mut v_a_656_: *mut crate::leanh::LeanObject,
    mut v_a_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lean_Meta_Grind_mkGoal(
        v_mvarId_649_,
        v_a_650_,
        v_a_651_,
        v_a_652_,
        v_a_653_,
        v_a_654_,
        v_a_655_,
        v_a_656_,
        v_a_657_,
        v_a_658_,
    );
    crate::leanh::lean_dec(v_a_658_);
    crate::leanh::lean_dec_ref(v_a_657_);
    crate::leanh::lean_dec(v_a_656_);
    crate::leanh::lean_dec_ref(v_a_655_);
    crate::leanh::lean_dec(v_a_654_);
    crate::leanh::lean_dec_ref(v_a_653_);
    crate::leanh::lean_dec(v_a_652_);
    crate::leanh::lean_dec_ref(v_a_651_);
    crate::leanh::lean_dec(v_a_650_);
    return v_res_660_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_ctorIdx(
    mut v_x_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_661_) == 0 {
        let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_662_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_662_;
    } else {
        let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_663_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_663_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_ctorIdx___boxed(
    mut v_x_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Lean_Meta_Grind_IntrosResult_ctorIdx(v_x_664_);
    crate::leanh::lean_dec(v_x_664_);
    return v_res_665_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(
    mut v_t_666_: *mut crate::leanh::LeanObject,
    mut v_k_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_666_) == 0 {
        return v_k_667_;
    } else {
        let mut v_newDecls_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_goal_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_newDecls_668_ = crate::leanh::lean_ctor_get(v_t_666_, 0);
        crate::leanh::lean_inc_ref(v_newDecls_668_);
        v_goal_669_ = crate::leanh::lean_ctor_get(v_t_666_, 1);
        crate::leanh::lean_inc_ref(v_goal_669_);
        crate::leanh::lean_dec_ref_known(v_t_666_, 2);
        v___x_670_ = crate::leanh::lean_apply_2(v_k_667_, v_newDecls_668_, v_goal_669_);
        return v___x_670_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_ctorElim(
    mut v_motive_671_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_672_: *mut crate::leanh::LeanObject,
    mut v_t_673_: *mut crate::leanh::LeanObject,
    mut v_h_674_: *mut crate::leanh::LeanObject,
    mut v_k_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_673_, v_k_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_ctorElim___boxed(
    mut v_motive_677_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_678_: *mut crate::leanh::LeanObject,
    mut v_t_679_: *mut crate::leanh::LeanObject,
    mut v_h_680_: *mut crate::leanh::LeanObject,
    mut v_k_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Lean_Meta_Grind_IntrosResult_ctorElim(
        v_motive_677_,
        v_ctorIdx_678_,
        v_t_679_,
        v_h_680_,
        v_k_681_,
    );
    crate::leanh::lean_dec(v_ctorIdx_678_);
    return v_res_682_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_failed_elim___redArg(
    mut v_t_683_: *mut crate::leanh::LeanObject,
    mut v_failed_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_683_, v_failed_684_);
    return v___x_685_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_failed_elim(
    mut v_motive_686_: *mut crate::leanh::LeanObject,
    mut v_t_687_: *mut crate::leanh::LeanObject,
    mut v_h_688_: *mut crate::leanh::LeanObject,
    mut v_failed_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_687_, v_failed_689_);
    return v___x_690_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_goal_elim___redArg(
    mut v_t_691_: *mut crate::leanh::LeanObject,
    mut v_goal_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_691_, v_goal_692_);
    return v___x_693_;
}
pub unsafe fn l_Lean_Meta_Grind_IntrosResult_goal_elim(
    mut v_motive_694_: *mut crate::leanh::LeanObject,
    mut v_t_695_: *mut crate::leanh::LeanObject,
    mut v_h_696_: *mut crate::leanh::LeanObject,
    mut v_goal_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_695_, v_goal_697_);
    return v___x_698_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_introN(
    mut v_goal_699_: *mut crate::leanh::LeanObject,
    mut v_num_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_a_705_: *mut crate::leanh::LeanObject,
    mut v_a_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_717_: u8 = 0;
    let mut v_newDecls_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_732_: u8 = 0;
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_737_: u8 = 0;
    let mut v_a_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_741_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_708_ = crate::leanh::lean_ctor_get(v_goal_699_, 0);
                v_mvarId_709_ = crate::leanh::lean_ctor_get(v_goal_699_, 1);
                v_isSharedCheck_746_ = (!crate::leanh::lean_is_exclusive(v_goal_699_)) as u8;
                if v_isSharedCheck_746_ == 0 {
                    v___x_711_ = v_goal_699_;
                    v_isShared_712_ = v_isSharedCheck_746_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_709_);
                    crate::leanh::lean_inc(v_toGoalState_708_);
                    crate::leanh::lean_dec(v_goal_699_);
                    v___x_711_ = crate::leanh::lean_box(0);
                    v_isShared_712_ = v_isSharedCheck_746_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_713_ = l_Lean_Meta_Sym_introN(
                    v_mvarId_709_,
                    v_num_700_,
                    v_a_701_,
                    v_a_702_,
                    v_a_703_,
                    v_a_704_,
                    v_a_705_,
                    v_a_706_,
                );
                if crate::leanh::lean_obj_tag(v___x_713_) == 0 {
                    v_a_714_ = crate::leanh::lean_ctor_get(v___x_713_, 0);
                    v_isSharedCheck_737_ = (!crate::leanh::lean_is_exclusive(v___x_713_)) as u8;
                    if v_isSharedCheck_737_ == 0 {
                        v___x_716_ = v___x_713_;
                        v_isShared_717_ = v_isSharedCheck_737_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_714_);
                        crate::leanh::lean_dec(v___x_713_);
                        v___x_716_ = crate::leanh::lean_box(0);
                        v_isShared_717_ = v_isSharedCheck_737_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_711_);
                    crate::leanh::lean_dec_ref(v_toGoalState_708_);
                    v_a_738_ = crate::leanh::lean_ctor_get(v___x_713_, 0);
                    v_isSharedCheck_745_ = (!crate::leanh::lean_is_exclusive(v___x_713_)) as u8;
                    if v_isSharedCheck_745_ == 0 {
                        v___x_740_ = v___x_713_;
                        v_isShared_741_ = v_isSharedCheck_745_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_738_);
                        crate::leanh::lean_dec(v___x_713_);
                        v___x_740_ = crate::leanh::lean_box(0);
                        v_isShared_741_ = v_isSharedCheck_745_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_714_) == 1 {
                    v_newDecls_718_ = crate::leanh::lean_ctor_get(v_a_714_, 0);
                    v_mvarId_719_ = crate::leanh::lean_ctor_get(v_a_714_, 1);
                    v_isSharedCheck_732_ = (!crate::leanh::lean_is_exclusive(v_a_714_)) as u8;
                    if v_isSharedCheck_732_ == 0 {
                        v___x_721_ = v_a_714_;
                        v_isShared_722_ = v_isSharedCheck_732_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_719_);
                        crate::leanh::lean_inc(v_newDecls_718_);
                        crate::leanh::lean_dec(v_a_714_);
                        v___x_721_ = crate::leanh::lean_box(0);
                        v_isShared_722_ = v_isSharedCheck_732_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_714_);
                    crate::leanh::lean_del_object(v___x_711_);
                    crate::leanh::lean_dec_ref(v_toGoalState_708_);
                    v___x_733_ = crate::leanh::lean_box(0);
                    if v_isShared_717_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_716_, 0, v___x_733_);
                        v___x_735_ = v___x_716_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
                        v___x_735_ = v_reuseFailAlloc_736_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_711_, 1, v_mvarId_719_);
                    v___x_724_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 0, v_toGoalState_708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 1, v_mvarId_719_);
                    v___x_724_ = v_reuseFailAlloc_731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_721_, 1, v___x_724_);
                    v___x_726_ = v___x_721_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_730_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_730_, 0, v_newDecls_718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_724_);
                    v___x_726_ = v_reuseFailAlloc_730_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_716_, 0, v___x_726_);
                    v___x_728_ = v___x_716_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
                    v___x_728_ = v_reuseFailAlloc_729_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_728_;
            }
            7 => {
                return v___x_735_;
            }
            8 => {
                if v_isShared_741_ == 0 {
                    v___x_743_ = v___x_740_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
                    v___x_743_ = v_reuseFailAlloc_744_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_introN___boxed(
    mut v_goal_747_: *mut crate::leanh::LeanObject,
    mut v_num_748_: *mut crate::leanh::LeanObject,
    mut v_a_749_: *mut crate::leanh::LeanObject,
    mut v_a_750_: *mut crate::leanh::LeanObject,
    mut v_a_751_: *mut crate::leanh::LeanObject,
    mut v_a_752_: *mut crate::leanh::LeanObject,
    mut v_a_753_: *mut crate::leanh::LeanObject,
    mut v_a_754_: *mut crate::leanh::LeanObject,
    mut v_a_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_Meta_Grind_Goal_introN(
        v_goal_747_,
        v_num_748_,
        v_a_749_,
        v_a_750_,
        v_a_751_,
        v_a_752_,
        v_a_753_,
        v_a_754_,
    );
    crate::leanh::lean_dec(v_a_754_);
    crate::leanh::lean_dec_ref(v_a_753_);
    crate::leanh::lean_dec(v_a_752_);
    crate::leanh::lean_dec_ref(v_a_751_);
    crate::leanh::lean_dec(v_a_750_);
    crate::leanh::lean_dec_ref(v_a_749_);
    return v_res_756_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_intros(
    mut v_goal_757_: *mut crate::leanh::LeanObject,
    mut v_names_758_: *mut crate::leanh::LeanObject,
    mut v_a_759_: *mut crate::leanh::LeanObject,
    mut v_a_760_: *mut crate::leanh::LeanObject,
    mut v_a_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_770_: u8 = 0;
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v_newDecls_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_795_: u8 = 0;
    let mut v_a_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut v_isSharedCheck_804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_766_ = crate::leanh::lean_ctor_get(v_goal_757_, 0);
                v_mvarId_767_ = crate::leanh::lean_ctor_get(v_goal_757_, 1);
                v_isSharedCheck_804_ = (!crate::leanh::lean_is_exclusive(v_goal_757_)) as u8;
                if v_isSharedCheck_804_ == 0 {
                    v___x_769_ = v_goal_757_;
                    v_isShared_770_ = v_isSharedCheck_804_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_767_);
                    crate::leanh::lean_inc(v_toGoalState_766_);
                    crate::leanh::lean_dec(v_goal_757_);
                    v___x_769_ = crate::leanh::lean_box(0);
                    v_isShared_770_ = v_isSharedCheck_804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_771_ = l_Lean_Meta_Sym_intros(
                    v_mvarId_767_,
                    v_names_758_,
                    v_a_759_,
                    v_a_760_,
                    v_a_761_,
                    v_a_762_,
                    v_a_763_,
                    v_a_764_,
                );
                if crate::leanh::lean_obj_tag(v___x_771_) == 0 {
                    v_a_772_ = crate::leanh::lean_ctor_get(v___x_771_, 0);
                    v_isSharedCheck_795_ = (!crate::leanh::lean_is_exclusive(v___x_771_)) as u8;
                    if v_isSharedCheck_795_ == 0 {
                        v___x_774_ = v___x_771_;
                        v_isShared_775_ = v_isSharedCheck_795_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_772_);
                        crate::leanh::lean_dec(v___x_771_);
                        v___x_774_ = crate::leanh::lean_box(0);
                        v_isShared_775_ = v_isSharedCheck_795_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_769_);
                    crate::leanh::lean_dec_ref(v_toGoalState_766_);
                    v_a_796_ = crate::leanh::lean_ctor_get(v___x_771_, 0);
                    v_isSharedCheck_803_ = (!crate::leanh::lean_is_exclusive(v___x_771_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_798_ = v___x_771_;
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_796_);
                        crate::leanh::lean_dec(v___x_771_);
                        v___x_798_ = crate::leanh::lean_box(0);
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_772_) == 1 {
                    v_newDecls_776_ = crate::leanh::lean_ctor_get(v_a_772_, 0);
                    v_mvarId_777_ = crate::leanh::lean_ctor_get(v_a_772_, 1);
                    v_isSharedCheck_790_ = (!crate::leanh::lean_is_exclusive(v_a_772_)) as u8;
                    if v_isSharedCheck_790_ == 0 {
                        v___x_779_ = v_a_772_;
                        v_isShared_780_ = v_isSharedCheck_790_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_777_);
                        crate::leanh::lean_inc(v_newDecls_776_);
                        crate::leanh::lean_dec(v_a_772_);
                        v___x_779_ = crate::leanh::lean_box(0);
                        v_isShared_780_ = v_isSharedCheck_790_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_772_);
                    crate::leanh::lean_del_object(v___x_769_);
                    crate::leanh::lean_dec_ref(v_toGoalState_766_);
                    v___x_791_ = crate::leanh::lean_box(0);
                    if v_isShared_775_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_774_, 0, v___x_791_);
                        v___x_793_ = v___x_774_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
                        v___x_793_ = v_reuseFailAlloc_794_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_769_, 1, v_mvarId_777_);
                    v___x_782_ = v___x_769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v_toGoalState_766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 1, v_mvarId_777_);
                    v___x_782_ = v_reuseFailAlloc_789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_779_, 1, v___x_782_);
                    v___x_784_ = v___x_779_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 0, v_newDecls_776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_782_);
                    v___x_784_ = v_reuseFailAlloc_788_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_774_, 0, v___x_784_);
                    v___x_786_ = v___x_774_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
                    v___x_786_ = v_reuseFailAlloc_787_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_786_;
            }
            7 => {
                return v___x_793_;
            }
            8 => {
                if v_isShared_799_ == 0 {
                    v___x_801_ = v___x_798_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
                    v___x_801_ = v_reuseFailAlloc_802_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_intros___boxed(
    mut v_goal_805_: *mut crate::leanh::LeanObject,
    mut v_names_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_a_811_: *mut crate::leanh::LeanObject,
    mut v_a_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_Meta_Grind_Goal_intros(
        v_goal_805_,
        v_names_806_,
        v_a_807_,
        v_a_808_,
        v_a_809_,
        v_a_810_,
        v_a_811_,
        v_a_812_,
    );
    crate::leanh::lean_dec(v_a_812_);
    crate::leanh::lean_dec_ref(v_a_811_);
    crate::leanh::lean_dec(v_a_810_);
    crate::leanh::lean_dec_ref(v_a_809_);
    crate::leanh::lean_dec(v_a_808_);
    crate::leanh::lean_dec_ref(v_a_807_);
    return v_res_814_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_ctorIdx(
    mut v_x_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_815_) == 0 {
        let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_816_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_816_;
    } else {
        let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_817_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_817_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_ctorIdx___boxed(
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Lean_Meta_Grind_ApplyResult_ctorIdx(v_x_818_);
    crate::leanh::lean_dec(v_x_818_);
    return v_res_819_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(
    mut v_t_820_: *mut crate::leanh::LeanObject,
    mut v_k_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_820_) == 0 {
        return v_k_821_;
    } else {
        let mut v_subgoals_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_subgoals_822_ = crate::leanh::lean_ctor_get(v_t_820_, 0);
        crate::leanh::lean_inc(v_subgoals_822_);
        crate::leanh::lean_dec_ref_known(v_t_820_, 1);
        v___x_823_ = crate::leanh::lean_apply_1(v_k_821_, v_subgoals_822_);
        return v___x_823_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_ctorElim(
    mut v_motive_824_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_825_: *mut crate::leanh::LeanObject,
    mut v_t_826_: *mut crate::leanh::LeanObject,
    mut v_h_827_: *mut crate::leanh::LeanObject,
    mut v_k_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_826_, v_k_828_);
    return v___x_829_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_ctorElim___boxed(
    mut v_motive_830_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_831_: *mut crate::leanh::LeanObject,
    mut v_t_832_: *mut crate::leanh::LeanObject,
    mut v_h_833_: *mut crate::leanh::LeanObject,
    mut v_k_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lean_Meta_Grind_ApplyResult_ctorElim(
        v_motive_830_,
        v_ctorIdx_831_,
        v_t_832_,
        v_h_833_,
        v_k_834_,
    );
    crate::leanh::lean_dec(v_ctorIdx_831_);
    return v_res_835_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_failed_elim___redArg(
    mut v_t_836_: *mut crate::leanh::LeanObject,
    mut v_failed_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_836_, v_failed_837_);
    return v___x_838_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_failed_elim(
    mut v_motive_839_: *mut crate::leanh::LeanObject,
    mut v_t_840_: *mut crate::leanh::LeanObject,
    mut v_h_841_: *mut crate::leanh::LeanObject,
    mut v_failed_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_840_, v_failed_842_);
    return v___x_843_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_goals_elim___redArg(
    mut v_t_844_: *mut crate::leanh::LeanObject,
    mut v_goals_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_844_, v_goals_845_);
    return v___x_846_;
}
pub unsafe fn l_Lean_Meta_Grind_ApplyResult_goals_elim(
    mut v_motive_847_: *mut crate::leanh::LeanObject,
    mut v_t_848_: *mut crate::leanh::LeanObject,
    mut v_h_849_: *mut crate::leanh::LeanObject,
    mut v_goals_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_848_, v_goals_850_);
    return v___x_851_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(
    mut v_goal_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v_toGoalState_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_853_) == 0 {
                    v___x_855_ = l_List_reverse___redArg(v_a_854_);
                    return v___x_855_;
                } else {
                    v_head_856_ = crate::leanh::lean_ctor_get(v_a_853_, 0);
                    v_tail_857_ = crate::leanh::lean_ctor_get(v_a_853_, 1);
                    v_isSharedCheck_867_ = (!crate::leanh::lean_is_exclusive(v_a_853_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v___x_859_ = v_a_853_;
                        v_isShared_860_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_857_);
                        crate::leanh::lean_inc(v_head_856_);
                        crate::leanh::lean_dec(v_a_853_);
                        v___x_859_ = crate::leanh::lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toGoalState_861_ = crate::leanh::lean_ctor_get(v_goal_852_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_861_);
                v___x_862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_862_, 0, v_toGoalState_861_);
                crate::leanh::lean_ctor_set(v___x_862_, 1, v_head_856_);
                if v_isShared_860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_859_, 1, v_a_854_);
                    crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_862_);
                    v___x_864_ = v___x_859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_866_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_854_);
                    v___x_864_ = v_reuseFailAlloc_866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_853_ = v_tail_857_;
                v_a_854_ = v___x_864_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0___boxed(
    mut v_goal_868_: *mut crate::leanh::LeanObject,
    mut v_a_869_: *mut crate::leanh::LeanObject,
    mut v_a_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_871_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(
        v_goal_868_,
        v_a_869_,
        v_a_870_,
    );
    crate::leanh::lean_dec_ref(v_goal_868_);
    return v_res_871_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_apply(
    mut v_goal_872_: *mut crate::leanh::LeanObject,
    mut v_rule_873_: *mut crate::leanh::LeanObject,
    mut v_a_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_a_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
    mut v_a_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_886_: u8 = 0;
    let mut v_mvarIds_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_899_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_904_: u8 = 0;
    let mut v_a_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_881_ = crate::leanh::lean_ctor_get(v_goal_872_, 1);
                crate::leanh::lean_inc(v_mvarId_881_);
                v___x_882_ = l_Lean_Meta_Sym_BackwardRule_apply(
                    v_mvarId_881_,
                    v_rule_873_,
                    v_a_874_,
                    v_a_875_,
                    v_a_876_,
                    v_a_877_,
                    v_a_878_,
                    v_a_879_,
                );
                if crate::leanh::lean_obj_tag(v___x_882_) == 0 {
                    v_a_883_ = crate::leanh::lean_ctor_get(v___x_882_, 0);
                    v_isSharedCheck_904_ = (!crate::leanh::lean_is_exclusive(v___x_882_)) as u8;
                    if v_isSharedCheck_904_ == 0 {
                        v___x_885_ = v___x_882_;
                        v_isShared_886_ = v_isSharedCheck_904_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_883_);
                        crate::leanh::lean_dec(v___x_882_);
                        v___x_885_ = crate::leanh::lean_box(0);
                        v_isShared_886_ = v_isSharedCheck_904_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goal_872_);
                    v_a_905_ = crate::leanh::lean_ctor_get(v___x_882_, 0);
                    v_isSharedCheck_912_ = (!crate::leanh::lean_is_exclusive(v___x_882_)) as u8;
                    if v_isSharedCheck_912_ == 0 {
                        v___x_907_ = v___x_882_;
                        v_isShared_908_ = v_isSharedCheck_912_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_905_);
                        crate::leanh::lean_dec(v___x_882_);
                        v___x_907_ = crate::leanh::lean_box(0);
                        v_isShared_908_ = v_isSharedCheck_912_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_883_) == 1 {
                    v_mvarIds_887_ = crate::leanh::lean_ctor_get(v_a_883_, 0);
                    v_isSharedCheck_899_ = (!crate::leanh::lean_is_exclusive(v_a_883_)) as u8;
                    if v_isSharedCheck_899_ == 0 {
                        v___x_889_ = v_a_883_;
                        v_isShared_890_ = v_isSharedCheck_899_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarIds_887_);
                        crate::leanh::lean_dec(v_a_883_);
                        v___x_889_ = crate::leanh::lean_box(0);
                        v_isShared_890_ = v_isSharedCheck_899_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_883_);
                    crate::leanh::lean_dec_ref(v_goal_872_);
                    v___x_900_ = crate::leanh::lean_box(0);
                    if v_isShared_886_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_885_, 0, v___x_900_);
                        v___x_902_ = v___x_885_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
                        v___x_902_ = v_reuseFailAlloc_903_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_891_ = crate::leanh::lean_box(0);
                v___x_892_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(
                    v_goal_872_,
                    v_mvarIds_887_,
                    v___x_891_,
                );
                crate::leanh::lean_dec_ref(v_goal_872_);
                if v_isShared_890_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_889_, 0, v___x_892_);
                    v___x_894_ = v___x_889_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
                    v___x_894_ = v_reuseFailAlloc_898_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_886_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_885_, 0, v___x_894_);
                    v___x_896_ = v___x_885_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
                    v___x_896_ = v_reuseFailAlloc_897_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_896_;
            }
            5 => {
                return v___x_902_;
            }
            6 => {
                if v_isShared_908_ == 0 {
                    v___x_910_ = v___x_907_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
                    v___x_910_ = v_reuseFailAlloc_911_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_apply___boxed(
    mut v_goal_913_: *mut crate::leanh::LeanObject,
    mut v_rule_914_: *mut crate::leanh::LeanObject,
    mut v_a_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_922_ = l_Lean_Meta_Grind_Goal_apply(
        v_goal_913_,
        v_rule_914_,
        v_a_915_,
        v_a_916_,
        v_a_917_,
        v_a_918_,
        v_a_919_,
        v_a_920_,
    );
    crate::leanh::lean_dec(v_a_920_);
    crate::leanh::lean_dec_ref(v_a_919_);
    crate::leanh::lean_dec(v_a_918_);
    crate::leanh::lean_dec_ref(v_a_917_);
    crate::leanh::lean_dec(v_a_916_);
    crate::leanh::lean_dec_ref(v_a_915_);
    return v_res_922_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_ctorIdx(
    mut v_x_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_923_) {
        0 => {
            let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_924_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_924_;
        }
        1 => {
            let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_925_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_925_;
        }
        _ => {
            let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_926_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_926_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___boxed(
    mut v_x_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Lean_Meta_Grind_SimpGoalResult_ctorIdx(v_x_927_);
    crate::leanh::lean_dec(v_x_927_);
    return v_res_928_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(
    mut v_t_929_: *mut crate::leanh::LeanObject,
    mut v_k_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_929_) == 2 {
        let mut v_goal_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_goal_931_ = crate::leanh::lean_ctor_get(v_t_929_, 0);
        crate::leanh::lean_inc_ref(v_goal_931_);
        crate::leanh::lean_dec_ref_known(v_t_929_, 1);
        v___x_932_ = crate::leanh::lean_apply_1(v_k_930_, v_goal_931_);
        return v___x_932_;
    } else {
        crate::leanh::lean_dec(v_t_929_);
        return v_k_930_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_ctorElim(
    mut v_motive_933_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_934_: *mut crate::leanh::LeanObject,
    mut v_t_935_: *mut crate::leanh::LeanObject,
    mut v_h_936_: *mut crate::leanh::LeanObject,
    mut v_k_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_935_, v_k_937_);
    return v___x_938_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_ctorElim___boxed(
    mut v_motive_939_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_940_: *mut crate::leanh::LeanObject,
    mut v_t_941_: *mut crate::leanh::LeanObject,
    mut v_h_942_: *mut crate::leanh::LeanObject,
    mut v_k_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_944_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim(
        v_motive_939_,
        v_ctorIdx_940_,
        v_t_941_,
        v_h_942_,
        v_k_943_,
    );
    crate::leanh::lean_dec(v_ctorIdx_940_);
    return v_res_944_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim___redArg(
    mut v_t_945_: *mut crate::leanh::LeanObject,
    mut v_noProgress_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_945_, v_noProgress_946_);
    return v___x_947_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim(
    mut v_motive_948_: *mut crate::leanh::LeanObject,
    mut v_t_949_: *mut crate::leanh::LeanObject,
    mut v_h_950_: *mut crate::leanh::LeanObject,
    mut v_noProgress_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_949_, v_noProgress_951_);
    return v___x_952_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_closed_elim___redArg(
    mut v_t_953_: *mut crate::leanh::LeanObject,
    mut v_closed_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_953_, v_closed_954_);
    return v___x_955_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_closed_elim(
    mut v_motive_956_: *mut crate::leanh::LeanObject,
    mut v_t_957_: *mut crate::leanh::LeanObject,
    mut v_h_958_: *mut crate::leanh::LeanObject,
    mut v_closed_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_957_, v_closed_959_);
    return v___x_960_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_goal_elim___redArg(
    mut v_t_961_: *mut crate::leanh::LeanObject,
    mut v_goal_962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_961_, v_goal_962_);
    return v___x_963_;
}
pub unsafe fn l_Lean_Meta_Grind_SimpGoalResult_goal_elim(
    mut v_motive_964_: *mut crate::leanh::LeanObject,
    mut v_t_965_: *mut crate::leanh::LeanObject,
    mut v_h_966_: *mut crate::leanh::LeanObject,
    mut v_goal_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_965_, v_goal_967_);
    return v___x_968_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_simp(
    mut v_goal_969_: *mut crate::leanh::LeanObject,
    mut v_methods_970_: *mut crate::leanh::LeanObject,
    mut v_config_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_983_: u8 = 0;
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_988_: u8 = 0;
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1000_: u8 = 0;
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut v_a_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut v_isSharedCheck_1020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_979_ = crate::leanh::lean_ctor_get(v_goal_969_, 0);
                v_mvarId_980_ = crate::leanh::lean_ctor_get(v_goal_969_, 1);
                v_isSharedCheck_1020_ = (!crate::leanh::lean_is_exclusive(v_goal_969_)) as u8;
                if v_isSharedCheck_1020_ == 0 {
                    v___x_982_ = v_goal_969_;
                    v_isShared_983_ = v_isSharedCheck_1020_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_980_);
                    crate::leanh::lean_inc(v_toGoalState_979_);
                    crate::leanh::lean_dec(v_goal_969_);
                    v___x_982_ = crate::leanh::lean_box(0);
                    v_isShared_983_ = v_isSharedCheck_1020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_984_ = l_Lean_Meta_Sym_simpGoal(
                    v_mvarId_980_,
                    v_methods_970_,
                    v_config_971_,
                    v_a_972_,
                    v_a_973_,
                    v_a_974_,
                    v_a_975_,
                    v_a_976_,
                    v_a_977_,
                );
                if crate::leanh::lean_obj_tag(v___x_984_) == 0 {
                    v_a_985_ = crate::leanh::lean_ctor_get(v___x_984_, 0);
                    v_isSharedCheck_1011_ = (!crate::leanh::lean_is_exclusive(v___x_984_)) as u8;
                    if v_isSharedCheck_1011_ == 0 {
                        v___x_987_ = v___x_984_;
                        v_isShared_988_ = v_isSharedCheck_1011_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_985_);
                        crate::leanh::lean_dec(v___x_984_);
                        v___x_987_ = crate::leanh::lean_box(0);
                        v_isShared_988_ = v_isSharedCheck_1011_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_982_);
                    crate::leanh::lean_dec_ref(v_toGoalState_979_);
                    v_a_1012_ = crate::leanh::lean_ctor_get(v___x_984_, 0);
                    v_isSharedCheck_1019_ = (!crate::leanh::lean_is_exclusive(v___x_984_)) as u8;
                    if v_isSharedCheck_1019_ == 0 {
                        v___x_1014_ = v___x_984_;
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1012_);
                        crate::leanh::lean_dec(v___x_984_);
                        v___x_1014_ = crate::leanh::lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => match crate::leanh::lean_obj_tag(v_a_985_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_982_);
                    crate::leanh::lean_dec_ref(v_toGoalState_979_);
                    v___x_989_ = crate::leanh::lean_box(0);
                    if v_isShared_988_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_989_);
                        v___x_991_ = v___x_987_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
                        v___x_991_ = v_reuseFailAlloc_992_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_982_);
                    crate::leanh::lean_dec_ref(v_toGoalState_979_);
                    v___x_993_ = crate::leanh::lean_box(1);
                    if v_isShared_988_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_993_);
                        v___x_995_ = v___x_987_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
                        v___x_995_ = v_reuseFailAlloc_996_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_mvarId_997_ = crate::leanh::lean_ctor_get(v_a_985_, 0);
                    v_isSharedCheck_1010_ = (!crate::leanh::lean_is_exclusive(v_a_985_)) as u8;
                    if v_isSharedCheck_1010_ == 0 {
                        v___x_999_ = v_a_985_;
                        v_isShared_1000_ = v_isSharedCheck_1010_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_997_);
                        crate::leanh::lean_dec(v_a_985_);
                        v___x_999_ = crate::leanh::lean_box(0);
                        v_isShared_1000_ = v_isSharedCheck_1010_;
                        state = 5;
                        continue;
                    }
                }
            },
            3 => {
                return v___x_991_;
            }
            4 => {
                return v___x_995_;
            }
            5 => {
                if v_isShared_983_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_982_, 1, v_mvarId_997_);
                    v___x_1002_ = v___x_982_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_toGoalState_979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_mvarId_997_);
                    v___x_1002_ = v_reuseFailAlloc_1009_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_999_, 0, v___x_1002_);
                    v___x_1004_ = v___x_999_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1002_);
                    v___x_1004_ = v_reuseFailAlloc_1008_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_1004_);
                    v___x_1006_ = v___x_987_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
                    v___x_1006_ = v_reuseFailAlloc_1007_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1006_;
            }
            9 => {
                if v_isShared_1015_ == 0 {
                    v___x_1017_ = v___x_1014_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
                    v___x_1017_ = v_reuseFailAlloc_1018_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_simp___boxed(
    mut v_goal_1021_: *mut crate::leanh::LeanObject,
    mut v_methods_1022_: *mut crate::leanh::LeanObject,
    mut v_config_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
    mut v_a_1026_: *mut crate::leanh::LeanObject,
    mut v_a_1027_: *mut crate::leanh::LeanObject,
    mut v_a_1028_: *mut crate::leanh::LeanObject,
    mut v_a_1029_: *mut crate::leanh::LeanObject,
    mut v_a_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lean_Meta_Grind_Goal_simp(
        v_goal_1021_,
        v_methods_1022_,
        v_config_1023_,
        v_a_1024_,
        v_a_1025_,
        v_a_1026_,
        v_a_1027_,
        v_a_1028_,
        v_a_1029_,
    );
    crate::leanh::lean_dec(v_a_1029_);
    crate::leanh::lean_dec_ref(v_a_1028_);
    crate::leanh::lean_dec(v_a_1027_);
    crate::leanh::lean_dec_ref(v_a_1026_);
    crate::leanh::lean_dec(v_a_1025_);
    crate::leanh::lean_dec_ref(v_a_1024_);
    return v_res_1031_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(
    mut v_goal_1032_: *mut crate::leanh::LeanObject,
    mut v_methods_1033_: *mut crate::leanh::LeanObject,
    mut v_config_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
    mut v_a_1036_: *mut crate::leanh::LeanObject,
    mut v_a_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
    mut v_a_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v_mvarId_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v_isSharedCheck_1074_: u8 = 0;
    let mut v_unused_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_a_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_1042_ = crate::leanh::lean_ctor_get(v_goal_1032_, 0);
                v_mvarId_1043_ = crate::leanh::lean_ctor_get(v_goal_1032_, 1);
                crate::leanh::lean_inc(v_mvarId_1043_);
                v___x_1044_ = l_Lean_Meta_Sym_simpGoal(
                    v_mvarId_1043_,
                    v_methods_1033_,
                    v_config_1034_,
                    v_a_1035_,
                    v_a_1036_,
                    v_a_1037_,
                    v_a_1038_,
                    v_a_1039_,
                    v_a_1040_,
                );
                if crate::leanh::lean_obj_tag(v___x_1044_) == 0 {
                    v_a_1045_ = crate::leanh::lean_ctor_get(v___x_1044_, 0);
                    v_isSharedCheck_1077_ = (!crate::leanh::lean_is_exclusive(v___x_1044_)) as u8;
                    if v_isSharedCheck_1077_ == 0 {
                        v___x_1047_ = v___x_1044_;
                        v_isShared_1048_ = v_isSharedCheck_1077_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1045_);
                        crate::leanh::lean_dec(v___x_1044_);
                        v___x_1047_ = crate::leanh::lean_box(0);
                        v_isShared_1048_ = v_isSharedCheck_1077_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goal_1032_);
                    v_a_1078_ = crate::leanh::lean_ctor_get(v___x_1044_, 0);
                    v_isSharedCheck_1085_ = (!crate::leanh::lean_is_exclusive(v___x_1044_)) as u8;
                    if v_isSharedCheck_1085_ == 0 {
                        v___x_1080_ = v___x_1044_;
                        v_isShared_1081_ = v_isSharedCheck_1085_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1078_);
                        crate::leanh::lean_dec(v___x_1044_);
                        v___x_1080_ = crate::leanh::lean_box(0);
                        v_isShared_1081_ = v_isSharedCheck_1085_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_1045_) {
                0 => {
                    v___x_1049_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1049_, 0, v_goal_1032_);
                    if v_isShared_1048_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1049_);
                        v___x_1051_ = v___x_1047_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
                        v___x_1051_ = v_reuseFailAlloc_1052_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_dec_ref(v_goal_1032_);
                    v___x_1053_ = crate::leanh::lean_box(1);
                    if v_isShared_1048_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1053_);
                        v___x_1055_ = v___x_1047_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
                        v___x_1055_ = v_reuseFailAlloc_1056_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_inc_ref(v_toGoalState_1042_);
                    v_isSharedCheck_1074_ = (!crate::leanh::lean_is_exclusive(v_goal_1032_)) as u8;
                    if v_isSharedCheck_1074_ == 0 {
                        v_unused_1075_ = crate::leanh::lean_ctor_get(v_goal_1032_, 1);
                        crate::leanh::lean_dec(v_unused_1075_);
                        v_unused_1076_ = crate::leanh::lean_ctor_get(v_goal_1032_, 0);
                        crate::leanh::lean_dec(v_unused_1076_);
                        v___x_1058_ = v_goal_1032_;
                        v_isShared_1059_ = v_isSharedCheck_1074_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_goal_1032_);
                        v___x_1058_ = crate::leanh::lean_box(0);
                        v_isShared_1059_ = v_isSharedCheck_1074_;
                        state = 4;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_1051_;
            }
            3 => {
                return v___x_1055_;
            }
            4 => {
                v_mvarId_1060_ = crate::leanh::lean_ctor_get(v_a_1045_, 0);
                v_isSharedCheck_1073_ = (!crate::leanh::lean_is_exclusive(v_a_1045_)) as u8;
                if v_isSharedCheck_1073_ == 0 {
                    v___x_1062_ = v_a_1045_;
                    v_isShared_1063_ = v_isSharedCheck_1073_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_1060_);
                    crate::leanh::lean_dec(v_a_1045_);
                    v___x_1062_ = crate::leanh::lean_box(0);
                    v_isShared_1063_ = v_isSharedCheck_1073_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1059_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1058_, 1, v_mvarId_1060_);
                    v___x_1065_ = v___x_1058_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_toGoalState_1042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_mvarId_1060_);
                    v___x_1065_ = v_reuseFailAlloc_1072_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1062_, 0, v___x_1065_);
                    v___x_1067_ = v___x_1062_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1071_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1065_);
                    v___x_1067_ = v_reuseFailAlloc_1071_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1048_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1047_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1069_;
            }
            9 => {
                if v_isShared_1081_ == 0 {
                    v___x_1083_ = v___x_1080_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress___boxed(
    mut v_goal_1086_: *mut crate::leanh::LeanObject,
    mut v_methods_1087_: *mut crate::leanh::LeanObject,
    mut v_config_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(
        v_goal_1086_,
        v_methods_1087_,
        v_config_1088_,
        v_a_1089_,
        v_a_1090_,
        v_a_1091_,
        v_a_1092_,
        v_a_1093_,
        v_a_1094_,
    );
    crate::leanh::lean_dec(v_a_1094_);
    crate::leanh::lean_dec_ref(v_a_1093_);
    crate::leanh::lean_dec(v_a_1092_);
    crate::leanh::lean_dec_ref(v_a_1091_);
    crate::leanh::lean_dec(v_a_1090_);
    crate::leanh::lean_dec_ref(v_a_1089_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_internalize(
    mut v_goal_1097_: *mut crate::leanh::LeanObject,
    mut v_num_1098_: *mut crate::leanh::LeanObject,
    mut v_a_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1109_, 0, v_num_1098_);
    v___x_1110_ = l_Lean_Meta_Grind_processHypotheses(
        v_goal_1097_,
        v___x_1109_,
        v_a_1099_,
        v_a_1100_,
        v_a_1101_,
        v_a_1102_,
        v_a_1103_,
        v_a_1104_,
        v_a_1105_,
        v_a_1106_,
        v_a_1107_,
    );
    return v___x_1110_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_internalize___boxed(
    mut v_goal_1111_: *mut crate::leanh::LeanObject,
    mut v_num_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1123_ = l_Lean_Meta_Grind_Goal_internalize(
        v_goal_1111_,
        v_num_1112_,
        v_a_1113_,
        v_a_1114_,
        v_a_1115_,
        v_a_1116_,
        v_a_1117_,
        v_a_1118_,
        v_a_1119_,
        v_a_1120_,
        v_a_1121_,
    );
    crate::leanh::lean_dec(v_a_1121_);
    crate::leanh::lean_dec_ref(v_a_1120_);
    crate::leanh::lean_dec(v_a_1119_);
    crate::leanh::lean_dec_ref(v_a_1118_);
    crate::leanh::lean_dec(v_a_1117_);
    crate::leanh::lean_dec_ref(v_a_1116_);
    crate::leanh::lean_dec(v_a_1115_);
    crate::leanh::lean_dec_ref(v_a_1114_);
    crate::leanh::lean_dec(v_a_1113_);
    return v_res_1123_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_internalizeAll(
    mut v_goal_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = crate::leanh::lean_box(0);
    v___x_1136_ = l_Lean_Meta_Grind_processHypotheses(
        v_goal_1124_,
        v___x_1135_,
        v_a_1125_,
        v_a_1126_,
        v_a_1127_,
        v_a_1128_,
        v_a_1129_,
        v_a_1130_,
        v_a_1131_,
        v_a_1132_,
        v_a_1133_,
    );
    return v___x_1136_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_internalizeAll___boxed(
    mut v_goal_1137_: *mut crate::leanh::LeanObject,
    mut v_a_1138_: *mut crate::leanh::LeanObject,
    mut v_a_1139_: *mut crate::leanh::LeanObject,
    mut v_a_1140_: *mut crate::leanh::LeanObject,
    mut v_a_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
    mut v_a_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_Meta_Grind_Goal_internalizeAll(
        v_goal_1137_,
        v_a_1138_,
        v_a_1139_,
        v_a_1140_,
        v_a_1141_,
        v_a_1142_,
        v_a_1143_,
        v_a_1144_,
        v_a_1145_,
        v_a_1146_,
    );
    crate::leanh::lean_dec(v_a_1146_);
    crate::leanh::lean_dec_ref(v_a_1145_);
    crate::leanh::lean_dec(v_a_1144_);
    crate::leanh::lean_dec_ref(v_a_1143_);
    crate::leanh::lean_dec(v_a_1142_);
    crate::leanh::lean_dec_ref(v_a_1141_);
    crate::leanh::lean_dec(v_a_1140_);
    crate::leanh::lean_dec_ref(v_a_1139_);
    crate::leanh::lean_dec(v_a_1138_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_ctorIdx(
    mut v_x_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1149_) == 0 {
        let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1150_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1150_;
    } else {
        let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1151_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1151_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_ctorIdx___boxed(
    mut v_x_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1153_ = l_Lean_Meta_Grind_GrindResult_ctorIdx(v_x_1152_);
    crate::leanh::lean_dec(v_x_1152_);
    return v_res_1153_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(
    mut v_t_1154_: *mut crate::leanh::LeanObject,
    mut v_k_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1154_) == 0 {
        let mut v_goal_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_goal_1156_ = crate::leanh::lean_ctor_get(v_t_1154_, 0);
        crate::leanh::lean_inc_ref(v_goal_1156_);
        crate::leanh::lean_dec_ref_known(v_t_1154_, 1);
        v___x_1157_ = crate::leanh::lean_apply_1(v_k_1155_, v_goal_1156_);
        return v___x_1157_;
    } else {
        return v_k_1155_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_ctorElim(
    mut v_motive_1158_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1159_: *mut crate::leanh::LeanObject,
    mut v_t_1160_: *mut crate::leanh::LeanObject,
    mut v_h_1161_: *mut crate::leanh::LeanObject,
    mut v_k_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_1160_, v_k_1162_);
    return v___x_1163_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_ctorElim___boxed(
    mut v_motive_1164_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1165_: *mut crate::leanh::LeanObject,
    mut v_t_1166_: *mut crate::leanh::LeanObject,
    mut v_h_1167_: *mut crate::leanh::LeanObject,
    mut v_k_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Lean_Meta_Grind_GrindResult_ctorElim(
        v_motive_1164_,
        v_ctorIdx_1165_,
        v_t_1166_,
        v_h_1167_,
        v_k_1168_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1165_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_failed_elim___redArg(
    mut v_t_1170_: *mut crate::leanh::LeanObject,
    mut v_failed_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_1170_, v_failed_1171_);
    return v___x_1172_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_failed_elim(
    mut v_motive_1173_: *mut crate::leanh::LeanObject,
    mut v_t_1174_: *mut crate::leanh::LeanObject,
    mut v_h_1175_: *mut crate::leanh::LeanObject,
    mut v_failed_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_1174_, v_failed_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_closed_elim___redArg(
    mut v_t_1178_: *mut crate::leanh::LeanObject,
    mut v_closed_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_1178_, v_closed_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Lean_Meta_Grind_GrindResult_closed_elim(
    mut v_motive_1181_: *mut crate::leanh::LeanObject,
    mut v_t_1182_: *mut crate::leanh::LeanObject,
    mut v_h_1183_: *mut crate::leanh::LeanObject,
    mut v_closed_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_1182_, v_closed_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_grind(
    mut v_goal_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v_val_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1205_: u8 = 0;
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_a_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1197_ = l_Lean_Meta_Grind_solve(
                    v_goal_1186_,
                    v_a_1187_,
                    v_a_1188_,
                    v_a_1189_,
                    v_a_1190_,
                    v_a_1191_,
                    v_a_1192_,
                    v_a_1193_,
                    v_a_1194_,
                    v_a_1195_,
                );
                if crate::leanh::lean_obj_tag(v___x_1197_) == 0 {
                    v_a_1198_ = crate::leanh::lean_ctor_get(v___x_1197_, 0);
                    v_isSharedCheck_1217_ = (!crate::leanh::lean_is_exclusive(v___x_1197_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1200_ = v___x_1197_;
                        v_isShared_1201_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1198_);
                        crate::leanh::lean_dec(v___x_1197_);
                        v___x_1200_ = crate::leanh::lean_box(0);
                        v_isShared_1201_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1218_ = crate::leanh::lean_ctor_get(v___x_1197_, 0);
                    v_isSharedCheck_1225_ = (!crate::leanh::lean_is_exclusive(v___x_1197_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1220_ = v___x_1197_;
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1218_);
                        crate::leanh::lean_dec(v___x_1197_);
                        v___x_1220_ = crate::leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1198_) == 1 {
                    v_val_1202_ = crate::leanh::lean_ctor_get(v_a_1198_, 0);
                    v_isSharedCheck_1212_ = (!crate::leanh::lean_is_exclusive(v_a_1198_)) as u8;
                    if v_isSharedCheck_1212_ == 0 {
                        v___x_1204_ = v_a_1198_;
                        v_isShared_1205_ = v_isSharedCheck_1212_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1202_);
                        crate::leanh::lean_dec(v_a_1198_);
                        v___x_1204_ = crate::leanh::lean_box(0);
                        v_isShared_1205_ = v_isSharedCheck_1212_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1198_);
                    v___x_1213_ = crate::leanh::lean_box(1);
                    if v_isShared_1201_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1213_);
                        v___x_1215_ = v___x_1200_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
                        v___x_1215_ = v_reuseFailAlloc_1216_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1205_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1204_, 0);
                    v___x_1207_ = v___x_1204_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_val_1202_);
                    v___x_1207_ = v_reuseFailAlloc_1211_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1207_);
                    v___x_1209_ = v___x_1200_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
                    v___x_1209_ = v_reuseFailAlloc_1210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1209_;
            }
            5 => {
                return v___x_1215_;
            }
            6 => {
                if v_isShared_1221_ == 0 {
                    v___x_1223_ = v___x_1220_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_grind___boxed(
    mut v_goal_1226_: *mut crate::leanh::LeanObject,
    mut v_a_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lean_Meta_Grind_Goal_grind(
        v_goal_1226_,
        v_a_1227_,
        v_a_1228_,
        v_a_1229_,
        v_a_1230_,
        v_a_1231_,
        v_a_1232_,
        v_a_1233_,
        v_a_1234_,
        v_a_1235_,
    );
    crate::leanh::lean_dec(v_a_1235_);
    crate::leanh::lean_dec_ref(v_a_1234_);
    crate::leanh::lean_dec(v_a_1233_);
    crate::leanh::lean_dec_ref(v_a_1232_);
    crate::leanh::lean_dec(v_a_1231_);
    crate::leanh::lean_dec_ref(v_a_1230_);
    crate::leanh::lean_dec(v_a_1229_);
    crate::leanh::lean_dec_ref(v_a_1228_);
    crate::leanh::lean_dec(v_a_1227_);
    return v_res_1237_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_assumption(
    mut v_goal_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mvarId_1244_ = crate::leanh::lean_ctor_get(v_goal_1238_, 1);
    crate::leanh::lean_inc(v_mvarId_1244_);
    crate::leanh::lean_dec_ref(v_goal_1238_);
    v___x_1245_ =
        l_Lean_MVarId_assumptionCore(v_mvarId_1244_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
    return v___x_1245_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_assumption___boxed(
    mut v_goal_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
    mut v_a_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_a_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ =
        l_Lean_Meta_Grind_Goal_assumption(v_goal_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
    crate::leanh::lean_dec(v_a_1250_);
    crate::leanh::lean_dec_ref(v_a_1249_);
    crate::leanh::lean_dec(v_a_1248_);
    crate::leanh::lean_dec_ref(v_a_1247_);
    return v_res_1252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Grind(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Grind(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Grind(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Grind(builtin);
}
