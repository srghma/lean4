// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Goal
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Tactic.Util Lean.Meta.Sym.InferType
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_isTrue, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp4, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getDecl,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_getLevel___redArg,
    runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg,
    l_Lean_Meta_Sym_Simp_simp___boxed, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
    runtime_initialize_Lean_Meta_Tactic_Util,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        96, 83, 121, 109, 46, 115, 105, 109, 112, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112,
        114, 111, 103, 114, 101, 115, 115, 32, 0,
    ],
};
static mut l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 112, 114, 0],
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0_value)
            as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1_value)
            as *mut leanh::LeanObject,
        503120329516084626 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3_value)
            as *mut leanh::LeanObject,
        11870096045526947150 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4_value)
            as *mut leanh::LeanObject,
        18067798339771668657 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ctorIdx(
    mut v_x_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_687_) {
        0 => {
            let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_688_ = leanh::lean_unsigned_to_nat(0);
            return v___x_688_;
        }
        1 => {
            let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_689_ = leanh::lean_unsigned_to_nat(1);
            return v___x_689_;
        }
        _ => {
            let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_690_ = leanh::lean_unsigned_to_nat(2);
            return v___x_690_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___boxed(
    mut v_x_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Lean_Meta_Sym_SimpGoalResult_ctorIdx(v_x_691_);
    leanh::lean_dec(v_x_691_);
    return v_res_692_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(
    mut v_t_693_: *mut leanh::LeanObject,
    mut v_k_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_693_) == 2 {
        let mut v_mvarId_695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_695_ = leanh::lean_ctor_get(v_t_693_, 0);
        leanh::lean_inc(v_mvarId_695_);
        leanh::lean_dec_ref_known(v_t_693_, 1);
        v___x_696_ = leanh::lean_apply_1(v_k_694_, v_mvarId_695_);
        return v___x_696_;
    } else {
        leanh::lean_dec(v_t_693_);
        return v_k_694_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ctorElim(
    mut v_motive_697_: *mut leanh::LeanObject,
    mut v_ctorIdx_698_: *mut leanh::LeanObject,
    mut v_t_699_: *mut leanh::LeanObject,
    mut v_h_700_: *mut leanh::LeanObject,
    mut v_k_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_699_, v_k_701_);
    return v___x_702_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ctorElim___boxed(
    mut v_motive_703_: *mut leanh::LeanObject,
    mut v_ctorIdx_704_: *mut leanh::LeanObject,
    mut v_t_705_: *mut leanh::LeanObject,
    mut v_h_706_: *mut leanh::LeanObject,
    mut v_k_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim(
        v_motive_703_,
        v_ctorIdx_704_,
        v_t_705_,
        v_h_706_,
        v_k_707_,
    );
    leanh::lean_dec(v_ctorIdx_704_);
    return v_res_708_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim___redArg(
    mut v_t_709_: *mut leanh::LeanObject,
    mut v_noProgress_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_709_, v_noProgress_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim(
    mut v_motive_712_: *mut leanh::LeanObject,
    mut v_t_713_: *mut leanh::LeanObject,
    mut v_h_714_: *mut leanh::LeanObject,
    mut v_noProgress_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_713_, v_noProgress_715_);
    return v___x_716_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_closed_elim___redArg(
    mut v_t_717_: *mut leanh::LeanObject,
    mut v_closed_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_717_, v_closed_718_);
    return v___x_719_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_closed_elim(
    mut v_motive_720_: *mut leanh::LeanObject,
    mut v_t_721_: *mut leanh::LeanObject,
    mut v_h_722_: *mut leanh::LeanObject,
    mut v_closed_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_721_, v_closed_723_);
    return v___x_724_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_goal_elim___redArg(
    mut v_t_725_: *mut leanh::LeanObject,
    mut v_goal_726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_725_, v_goal_726_);
    return v___x_727_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_goal_elim(
    mut v_motive_728_: *mut leanh::LeanObject,
    mut v_t_729_: *mut leanh::LeanObject,
    mut v_h_730_: *mut leanh::LeanObject,
    mut v_goal_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_729_, v_goal_731_);
    return v___x_732_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_733_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0);
    v___x_735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_735_, 0, v___x_734_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1);
    v___x_737_ = leanh::lean_unsigned_to_nat(0);
    v___x_738_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
    leanh::lean_ctor_set(v___x_738_, 1, v___x_737_);
    leanh::lean_ctor_set(v___x_738_, 2, v___x_737_);
    leanh::lean_ctor_set(v___x_738_, 3, v___x_737_);
    leanh::lean_ctor_set(v___x_738_, 4, v___x_736_);
    leanh::lean_ctor_set(v___x_738_, 5, v___x_736_);
    leanh::lean_ctor_set(v___x_738_, 6, v___x_736_);
    leanh::lean_ctor_set(v___x_738_, 7, v___x_736_);
    leanh::lean_ctor_set(v___x_738_, 8, v___x_736_);
    leanh::lean_ctor_set(v___x_738_, 9, v___x_736_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_739_ = leanh::lean_unsigned_to_nat(32);
    v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
    v___x_741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_741_, 0, v___x_740_);
    return v___x_741_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_742_: usize = 0;
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_742_ = 5usize;
    v___x_743_ = leanh::lean_unsigned_to_nat(0);
    v___x_744_ = leanh::lean_unsigned_to_nat(32);
    v___x_745_ = lean_mk_empty_array_with_capacity(v___x_744_);
    v___x_746_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3);
    v___x_747_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_747_, 0, v___x_746_);
    leanh::lean_ctor_set(v___x_747_, 1, v___x_745_);
    leanh::lean_ctor_set(v___x_747_, 2, v___x_743_);
    leanh::lean_ctor_set(v___x_747_, 3, v___x_743_);
    leanh::lean_ctor_set_usize(v___x_747_, 4, v___x_742_);
    return v___x_747_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_748_ = leanh::lean_box(1);
    v___x_749_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4);
    v___x_750_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1);
    v___x_751_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_751_, 0, v___x_750_);
    leanh::lean_ctor_set(v___x_751_, 1, v___x_749_);
    leanh::lean_ctor_set(v___x_751_, 2, v___x_748_);
    return v___x_751_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(
    mut v_msgData_752_: *mut leanh::LeanObject,
    mut v___y_753_: *mut leanh::LeanObject,
    mut v___y_754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = lean_st_ref_get(v___y_754_);
    v_env_757_ = leanh::lean_ctor_get(v___x_756_, 0);
    leanh::lean_inc_ref(v_env_757_);
    leanh::lean_dec(v___x_756_);
    v_options_758_ = leanh::lean_ctor_get(v___y_753_, 2);
    v___x_759_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2);
    v___x_760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_758_);
    v___x_761_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_761_, 0, v_env_757_);
    leanh::lean_ctor_set(v___x_761_, 1, v___x_759_);
    leanh::lean_ctor_set(v___x_761_, 2, v___x_760_);
    leanh::lean_ctor_set(v___x_761_, 3, v_options_758_);
    v___x_762_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_762_, 0, v___x_761_);
    leanh::lean_ctor_set(v___x_762_, 1, v_msgData_752_);
    v___x_763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_763_, 0, v___x_762_);
    return v___x_763_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___boxed(
    mut v_msgData_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
    mut v___y_766_: *mut leanh::LeanObject,
    mut v___y_767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_768_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msgData_764_, v___y_765_, v___y_766_);
    leanh::lean_dec(v___y_766_);
    leanh::lean_dec_ref(v___y_765_);
    return v_res_768_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(
    mut v_msg_769_: *mut leanh::LeanObject,
    mut v___y_770_: *mut leanh::LeanObject,
    mut v___y_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_778_: u8 = 0;
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_773_ = leanh::lean_ctor_get(v___y_770_, 5);
                v___x_774_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msg_769_, v___y_770_, v___y_771_);
                v_a_775_ = leanh::lean_ctor_get(v___x_774_, 0);
                v_isSharedCheck_783_ = (!leanh::lean_is_exclusive(v___x_774_)) as u8;
                if v_isSharedCheck_783_ == 0 {
                    v___x_777_ = v___x_774_;
                    v_isShared_778_ = v_isSharedCheck_783_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_775_);
                    leanh::lean_dec(v___x_774_);
                    v___x_777_ = leanh::lean_box(0);
                    v_isShared_778_ = v_isSharedCheck_783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_773_);
                v___x_779_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_779_, 0, v_ref_773_);
                leanh::lean_ctor_set(v___x_779_, 1, v_a_775_);
                if v_isShared_778_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_777_, 1);
                    leanh::lean_ctor_set(v___x_777_, 0, v___x_779_);
                    v___x_781_ = v___x_777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                    v___x_781_ = v_reuseFailAlloc_782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg___boxed(
    mut v_msg_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(
        v_msg_784_, v___y_785_, v___y_786_,
    );
    leanh::lean_dec(v___y_786_);
    leanh::lean_dec_ref(v___y_785_);
    return v_res_788_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0;
    v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
    return v___x_791_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_toOption(
    mut v_x_792_: *mut leanh::LeanObject,
    mut v_a_793_: *mut leanh::LeanObject,
    mut v_a_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_803_: u8 = 0;
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_792_) {
                0 => {
                    v___x_796_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1,
                    );
                    v___x_797_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v___x_796_, v_a_793_, v_a_794_);
                    return v___x_797_;
                }
                1 => {
                    v___x_798_ = leanh::lean_box(0);
                    v___x_799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_799_, 0, v___x_798_);
                    return v___x_799_;
                }
                _ => {
                    v_mvarId_800_ = leanh::lean_ctor_get(v_x_792_, 0);
                    v_isSharedCheck_808_ = (!leanh::lean_is_exclusive(v_x_792_)) as u8;
                    if v_isSharedCheck_808_ == 0 {
                        v___x_802_ = v_x_792_;
                        v_isShared_803_ = v_isSharedCheck_808_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_mvarId_800_);
                        leanh::lean_dec(v_x_792_);
                        v___x_802_ = leanh::lean_box(0);
                        v_isShared_803_ = v_isSharedCheck_808_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_803_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_802_, 1);
                    v___x_805_ = v___x_802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_807_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_807_, 0, v_mvarId_800_);
                    v___x_805_ = v_reuseFailAlloc_807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_806_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_806_, 0, v___x_805_);
                return v___x_806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_toOption___boxed(
    mut v_x_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_Meta_Sym_SimpGoalResult_toOption(v_x_809_, v_a_810_, v_a_811_);
    leanh::lean_dec(v_a_811_);
    leanh::lean_dec_ref(v_a_810_);
    return v_res_813_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(
    mut v_00_u03b1_814_: *mut leanh::LeanObject,
    mut v_msg_815_: *mut leanh::LeanObject,
    mut v___y_816_: *mut leanh::LeanObject,
    mut v___y_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(
        v_msg_815_, v___y_816_, v___y_817_,
    );
    return v___x_819_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___boxed(
    mut v_00_u03b1_820_: *mut leanh::LeanObject,
    mut v_msg_821_: *mut leanh::LeanObject,
    mut v___y_822_: *mut leanh::LeanObject,
    mut v___y_823_: *mut leanh::LeanObject,
    mut v___y_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(
        v_00_u03b1_820_,
        v_msg_821_,
        v___y_822_,
        v___y_823_,
    );
    leanh::lean_dec(v___y_823_);
    leanh::lean_dec_ref(v___y_822_);
    return v_res_825_;
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(
    mut v_x_826_: *mut leanh::LeanObject,
    mut v_x_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_826_) == 0 {
        let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_828_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_828_, 0, v_x_827_);
        return v___x_828_;
    } else {
        leanh::lean_dec(v_x_827_);
        leanh::lean_inc(v_x_826_);
        return v_x_826_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress___boxed(
    mut v_x_829_: *mut leanh::LeanObject,
    mut v_x_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(v_x_829_, v_x_830_);
    leanh::lean_dec(v_x_829_);
    return v_res_831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_832_: *mut leanh::LeanObject,
    mut v_x_833_: *mut leanh::LeanObject,
    mut v_x_834_: *mut leanh::LeanObject,
    mut v_x_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_840_: u8 = 0;
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: u8 = 0;
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_836_ = leanh::lean_ctor_get(v_x_832_, 0);
                v_vs_837_ = leanh::lean_ctor_get(v_x_832_, 1);
                v_isSharedCheck_861_ = (!leanh::lean_is_exclusive(v_x_832_)) as u8;
                if v_isSharedCheck_861_ == 0 {
                    v___x_839_ = v_x_832_;
                    v_isShared_840_ = v_isSharedCheck_861_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_837_);
                    leanh::lean_inc(v_ks_836_);
                    leanh::lean_dec(v_x_832_);
                    v___x_839_ = leanh::lean_box(0);
                    v_isShared_840_ = v_isSharedCheck_861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_841_ = lean_array_get_size(v_ks_836_);
                v___x_842_ = lean_nat_dec_lt(v_x_833_, v___x_841_);
                if v___x_842_ == 0 {
                    leanh::lean_dec(v_x_833_);
                    v___x_843_ = lean_array_push(v_ks_836_, v_x_834_);
                    v___x_844_ = lean_array_push(v_vs_837_, v_x_835_);
                    if v_isShared_840_ == 0 {
                        leanh::lean_ctor_set(v___x_839_, 1, v___x_844_);
                        leanh::lean_ctor_set(v___x_839_, 0, v___x_843_);
                        v___x_846_ = v___x_839_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_847_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_843_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
                        v___x_846_ = v_reuseFailAlloc_847_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_848_ = lean_array_fget_borrowed(v_ks_836_, v_x_833_);
                    v___x_849_ = l_Lean_instBEqMVarId_beq(v_x_834_, v_k_x27_848_);
                    if v___x_849_ == 0 {
                        if v_isShared_840_ == 0 {
                            v___x_851_ = v___x_839_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_855_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_855_, 0, v_ks_836_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_855_, 1, v_vs_837_);
                            v___x_851_ = v_reuseFailAlloc_855_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_856_ = lean_array_fset(v_ks_836_, v_x_833_, v_x_834_);
                        v___x_857_ = lean_array_fset(v_vs_837_, v_x_833_, v_x_835_);
                        leanh::lean_dec(v_x_833_);
                        if v_isShared_840_ == 0 {
                            leanh::lean_ctor_set(v___x_839_, 1, v___x_857_);
                            leanh::lean_ctor_set(v___x_839_, 0, v___x_856_);
                            v___x_859_ = v___x_839_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_860_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_856_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_857_);
                            v___x_859_ = v_reuseFailAlloc_860_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_846_;
            }
            3 => {
                v___x_852_ = leanh::lean_unsigned_to_nat(1);
                v___x_853_ = lean_nat_add(v_x_833_, v___x_852_);
                leanh::lean_dec(v_x_833_);
                v_x_832_ = v___x_851_;
                v_x_833_ = v___x_853_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_862_: *mut leanh::LeanObject,
    mut v_k_863_: *mut leanh::LeanObject,
    mut v_v_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = leanh::lean_unsigned_to_nat(0);
    v___x_866_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_862_, v___x_865_, v_k_863_, v_v_864_);
    return v___x_866_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_867_: usize = 0;
    let mut v___x_868_: usize = 0;
    let mut v___x_869_: usize = 0;
    v___x_867_ = 5usize;
    v___x_868_ = 1usize;
    v___x_869_ = lean_usize_shift_left(v___x_868_, v___x_867_);
    return v___x_869_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_870_: usize = 0;
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: usize = 0;
    v___x_870_ = 1usize;
    v___x_871_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_872_ = lean_usize_sub(v___x_871_, v___x_870_);
    return v___x_872_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_873_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_873_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(
    mut v_x_874_: *mut leanh::LeanObject,
    mut v_x_875_: usize,
    mut v_x_876_: usize,
    mut v_x_877_: *mut leanh::LeanObject,
    mut v_x_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: usize = 0;
    let mut v___x_881_: usize = 0;
    let mut v___x_882_: usize = 0;
    let mut v___x_883_: usize = 0;
    let mut v_j_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v_v_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut v_node_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_921_: u8 = 0;
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_923_: u8 = 0;
    let mut v_unused_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_934_: u8 = 0;
    let mut v_ks_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: usize = 0;
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: u8 = 0;
    let mut v_reuseFailAlloc_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_874_) == 0 {
                    v_es_879_ = leanh::lean_ctor_get(v_x_874_, 0);
                    v___x_880_ = 5usize;
                    v___x_881_ = 1usize;
                    v___x_882_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_883_ = lean_usize_land(v_x_875_, v___x_882_);
                    v_j_884_ = lean_usize_to_nat(v___x_883_);
                    v___x_885_ = lean_array_get_size(v_es_879_);
                    v___x_886_ = lean_nat_dec_lt(v_j_884_, v___x_885_);
                    if v___x_886_ == 0 {
                        leanh::lean_dec(v_j_884_);
                        leanh::lean_dec(v_x_878_);
                        leanh::lean_dec(v_x_877_);
                        return v_x_874_;
                    } else {
                        leanh::lean_inc_ref(v_es_879_);
                        v_isSharedCheck_923_ = (!leanh::lean_is_exclusive(v_x_874_)) as u8;
                        if v_isSharedCheck_923_ == 0 {
                            v_unused_924_ = leanh::lean_ctor_get(v_x_874_, 0);
                            leanh::lean_dec(v_unused_924_);
                            v___x_888_ = v_x_874_;
                            v_isShared_889_ = v_isSharedCheck_923_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_874_);
                            v___x_888_ = leanh::lean_box(0);
                            v_isShared_889_ = v_isSharedCheck_923_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_925_ = leanh::lean_ctor_get(v_x_874_, 0);
                    v_vs_926_ = leanh::lean_ctor_get(v_x_874_, 1);
                    v_isSharedCheck_946_ = (!leanh::lean_is_exclusive(v_x_874_)) as u8;
                    if v_isSharedCheck_946_ == 0 {
                        v___x_928_ = v_x_874_;
                        v_isShared_929_ = v_isSharedCheck_946_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_926_);
                        leanh::lean_inc(v_ks_925_);
                        leanh::lean_dec(v_x_874_);
                        v___x_928_ = leanh::lean_box(0);
                        v_isShared_929_ = v_isSharedCheck_946_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_890_ = lean_array_fget(v_es_879_, v_j_884_);
                v___x_891_ = leanh::lean_box(0);
                v_xs_x27_892_ = lean_array_fset(v_es_879_, v_j_884_, v___x_891_);
                match leanh::lean_obj_tag(v_v_890_) {
                    0 => {
                        v_key_899_ = leanh::lean_ctor_get(v_v_890_, 0);
                        v_val_900_ = leanh::lean_ctor_get(v_v_890_, 1);
                        v_isSharedCheck_910_ = (!leanh::lean_is_exclusive(v_v_890_)) as u8;
                        if v_isSharedCheck_910_ == 0 {
                            v___x_902_ = v_v_890_;
                            v_isShared_903_ = v_isSharedCheck_910_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_900_);
                            leanh::lean_inc(v_key_899_);
                            leanh::lean_dec(v_v_890_);
                            v___x_902_ = leanh::lean_box(0);
                            v_isShared_903_ = v_isSharedCheck_910_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_911_ = leanh::lean_ctor_get(v_v_890_, 0);
                        v_isSharedCheck_921_ = (!leanh::lean_is_exclusive(v_v_890_)) as u8;
                        if v_isSharedCheck_921_ == 0 {
                            v___x_913_ = v_v_890_;
                            v_isShared_914_ = v_isSharedCheck_921_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_911_);
                            leanh::lean_dec(v_v_890_);
                            v___x_913_ = leanh::lean_box(0);
                            v_isShared_914_ = v_isSharedCheck_921_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_922_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_922_, 0, v_x_877_);
                        leanh::lean_ctor_set(v___x_922_, 1, v_x_878_);
                        v___y_894_ = v___x_922_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_895_ = lean_array_fset(v_xs_x27_892_, v_j_884_, v___y_894_);
                leanh::lean_dec(v_j_884_);
                if v_isShared_889_ == 0 {
                    leanh::lean_ctor_set(v___x_888_, 0, v___x_895_);
                    v___x_897_ = v___x_888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_898_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
                    v___x_897_ = v_reuseFailAlloc_898_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_897_;
            }
            4 => {
                v___x_904_ = l_Lean_instBEqMVarId_beq(v_x_877_, v_key_899_);
                if v___x_904_ == 0 {
                    leanh::lean_del_object(v___x_902_);
                    v___x_905_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_899_, v_val_900_, v_x_877_, v_x_878_,
                    );
                    v___x_906_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_906_, 0, v___x_905_);
                    v___y_894_ = v___x_906_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_900_);
                    leanh::lean_dec(v_key_899_);
                    if v_isShared_903_ == 0 {
                        leanh::lean_ctor_set(v___x_902_, 1, v_x_878_);
                        leanh::lean_ctor_set(v___x_902_, 0, v_x_877_);
                        v___x_908_ = v___x_902_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_909_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_909_, 0, v_x_877_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_909_, 1, v_x_878_);
                        v___x_908_ = v_reuseFailAlloc_909_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_894_ = v___x_908_;
                state = 2;
                continue;
            }
            6 => {
                v___x_915_ = lean_usize_shift_right(v_x_875_, v___x_880_);
                v___x_916_ = lean_usize_add(v_x_876_, v___x_881_);
                v___x_917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_node_911_, v___x_915_, v___x_916_, v_x_877_, v_x_878_);
                if v_isShared_914_ == 0 {
                    leanh::lean_ctor_set(v___x_913_, 0, v___x_917_);
                    v___x_919_ = v___x_913_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
                    v___x_919_ = v_reuseFailAlloc_920_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_894_ = v___x_919_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_929_ == 0 {
                    v___x_931_ = v___x_928_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_945_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_945_, 0, v_ks_925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_945_, 1, v_vs_926_);
                    v___x_931_ = v_reuseFailAlloc_945_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_932_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v___x_931_, v_x_877_, v_x_878_);
                v___x_940_ = 7usize;
                v___x_941_ = lean_usize_dec_le(v___x_940_, v_x_876_);
                if v___x_941_ == 0 {
                    v___x_942_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_932_);
                    v___x_943_ = leanh::lean_unsigned_to_nat(4);
                    v___x_944_ = lean_nat_dec_lt(v___x_942_, v___x_943_);
                    leanh::lean_dec(v___x_942_);
                    v___y_934_ = v___x_944_;
                    state = 10;
                    continue;
                } else {
                    v___y_934_ = v___x_941_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_934_ == 0 {
                    v_ks_935_ = leanh::lean_ctor_get(v_newNode_932_, 0);
                    leanh::lean_inc_ref(v_ks_935_);
                    v_vs_936_ = leanh::lean_ctor_get(v_newNode_932_, 1);
                    leanh::lean_inc_ref(v_vs_936_);
                    leanh::lean_dec_ref(v_newNode_932_);
                    v___x_937_ = leanh::lean_unsigned_to_nat(0);
                    v___x_938_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_x_876_, v_ks_935_, v_vs_936_, v___x_937_, v___x_938_);
                    leanh::lean_dec_ref(v_vs_936_);
                    leanh::lean_dec_ref(v_ks_935_);
                    return v___x_939_;
                } else {
                    return v_newNode_932_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_947_: usize,
    mut v_keys_948_: *mut leanh::LeanObject,
    mut v_vals_949_: *mut leanh::LeanObject,
    mut v_i_950_: *mut leanh::LeanObject,
    mut v_entries_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: u8 = 0;
    let mut v_k_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u64 = 0;
    let mut v_h_957_: usize = 0;
    let mut v___x_958_: usize = 0;
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: usize = 0;
    let mut v___x_962_: usize = 0;
    let mut v_h_963_: usize = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_952_ = lean_array_get_size(v_keys_948_);
                v___x_953_ = lean_nat_dec_lt(v_i_950_, v___x_952_);
                if v___x_953_ == 0 {
                    leanh::lean_dec(v_i_950_);
                    return v_entries_951_;
                } else {
                    v_k_954_ = lean_array_fget_borrowed(v_keys_948_, v_i_950_);
                    v_v_955_ = lean_array_fget_borrowed(v_vals_949_, v_i_950_);
                    v___x_956_ = l_Lean_instHashableMVarId_hash(v_k_954_);
                    v_h_957_ = lean_uint64_to_usize(v___x_956_);
                    v___x_958_ = 5usize;
                    v___x_959_ = leanh::lean_unsigned_to_nat(1);
                    v___x_960_ = 1usize;
                    v___x_961_ = lean_usize_sub(v_depth_947_, v___x_960_);
                    v___x_962_ = lean_usize_mul(v___x_958_, v___x_961_);
                    v_h_963_ = lean_usize_shift_right(v_h_957_, v___x_962_);
                    v___x_964_ = lean_nat_add(v_i_950_, v___x_959_);
                    leanh::lean_dec(v_i_950_);
                    leanh::lean_inc(v_v_955_);
                    leanh::lean_inc(v_k_954_);
                    v___x_965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_entries_951_, v_h_963_, v_depth_947_, v_k_954_, v_v_955_);
                    v_i_950_ = v___x_964_;
                    v_entries_951_ = v___x_965_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_967_: *mut leanh::LeanObject,
    mut v_keys_968_: *mut leanh::LeanObject,
    mut v_vals_969_: *mut leanh::LeanObject,
    mut v_i_970_: *mut leanh::LeanObject,
    mut v_entries_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_972_: usize = 0;
    let mut v_res_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_972_ = leanh::lean_unbox_usize(v_depth_967_);
    leanh::lean_dec(v_depth_967_);
    v_res_973_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_972_, v_keys_968_, v_vals_969_, v_i_970_, v_entries_971_);
    leanh::lean_dec_ref(v_vals_969_);
    leanh::lean_dec_ref(v_keys_968_);
    return v_res_973_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_974_: *mut leanh::LeanObject,
    mut v_x_975_: *mut leanh::LeanObject,
    mut v_x_976_: *mut leanh::LeanObject,
    mut v_x_977_: *mut leanh::LeanObject,
    mut v_x_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3383__boxed_979_: usize = 0;
    let mut v_x_3384__boxed_980_: usize = 0;
    let mut v_res_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3383__boxed_979_ = leanh::lean_unbox_usize(v_x_975_);
    leanh::lean_dec(v_x_975_);
    v_x_3384__boxed_980_ = leanh::lean_unbox_usize(v_x_976_);
    leanh::lean_dec(v_x_976_);
    v_res_981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_974_, v_x_3383__boxed_979_, v_x_3384__boxed_980_, v_x_977_, v_x_978_);
    return v_res_981_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(
    mut v_x_982_: *mut leanh::LeanObject,
    mut v_x_983_: *mut leanh::LeanObject,
    mut v_x_984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_985_: u64 = 0;
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = l_Lean_instHashableMVarId_hash(v_x_983_);
    v___x_986_ = lean_uint64_to_usize(v___x_985_);
    v___x_987_ = 1usize;
    v___x_988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_982_, v___x_986_, v___x_987_, v_x_983_, v_x_984_);
    return v___x_988_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(
    mut v_mvarId_989_: *mut leanh::LeanObject,
    mut v_val_990_: *mut leanh::LeanObject,
    mut v___y_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1001_: u8 = 0;
    let mut v_depth_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1025_: u8 = 0;
    let mut v_isSharedCheck_1026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_993_ = lean_st_ref_take(v___y_991_);
                v_mctx_994_ = leanh::lean_ctor_get(v___x_993_, 0);
                v_cache_995_ = leanh::lean_ctor_get(v___x_993_, 1);
                v_zetaDeltaFVarIds_996_ = leanh::lean_ctor_get(v___x_993_, 2);
                v_postponed_997_ = leanh::lean_ctor_get(v___x_993_, 3);
                v_diag_998_ = leanh::lean_ctor_get(v___x_993_, 4);
                v_isSharedCheck_1026_ = (!leanh::lean_is_exclusive(v___x_993_)) as u8;
                if v_isSharedCheck_1026_ == 0 {
                    v___x_1000_ = v___x_993_;
                    v_isShared_1001_ = v_isSharedCheck_1026_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_998_);
                    leanh::lean_inc(v_postponed_997_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_996_);
                    leanh::lean_inc(v_cache_995_);
                    leanh::lean_inc(v_mctx_994_);
                    leanh::lean_dec(v___x_993_);
                    v___x_1000_ = leanh::lean_box(0);
                    v_isShared_1001_ = v_isSharedCheck_1026_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1002_ = leanh::lean_ctor_get(v_mctx_994_, 0);
                v_levelAssignDepth_1003_ = leanh::lean_ctor_get(v_mctx_994_, 1);
                v_lmvarCounter_1004_ = leanh::lean_ctor_get(v_mctx_994_, 2);
                v_mvarCounter_1005_ = leanh::lean_ctor_get(v_mctx_994_, 3);
                v_lDecls_1006_ = leanh::lean_ctor_get(v_mctx_994_, 4);
                v_decls_1007_ = leanh::lean_ctor_get(v_mctx_994_, 5);
                v_userNames_1008_ = leanh::lean_ctor_get(v_mctx_994_, 6);
                v_lAssignment_1009_ = leanh::lean_ctor_get(v_mctx_994_, 7);
                v_eAssignment_1010_ = leanh::lean_ctor_get(v_mctx_994_, 8);
                v_dAssignment_1011_ = leanh::lean_ctor_get(v_mctx_994_, 9);
                v_isSharedCheck_1025_ = (!leanh::lean_is_exclusive(v_mctx_994_)) as u8;
                if v_isSharedCheck_1025_ == 0 {
                    v___x_1013_ = v_mctx_994_;
                    v_isShared_1014_ = v_isSharedCheck_1025_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1011_);
                    leanh::lean_inc(v_eAssignment_1010_);
                    leanh::lean_inc(v_lAssignment_1009_);
                    leanh::lean_inc(v_userNames_1008_);
                    leanh::lean_inc(v_decls_1007_);
                    leanh::lean_inc(v_lDecls_1006_);
                    leanh::lean_inc(v_mvarCounter_1005_);
                    leanh::lean_inc(v_lmvarCounter_1004_);
                    leanh::lean_inc(v_levelAssignDepth_1003_);
                    leanh::lean_inc(v_depth_1002_);
                    leanh::lean_dec(v_mctx_994_);
                    v___x_1013_ = leanh::lean_box(0);
                    v_isShared_1014_ = v_isSharedCheck_1025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1015_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_eAssignment_1010_, v_mvarId_989_, v_val_990_);
                if v_isShared_1014_ == 0 {
                    leanh::lean_ctor_set(v___x_1013_, 8, v___x_1015_);
                    v___x_1017_ = v___x_1013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1024_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_depth_1002_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1024_,
                        1,
                        v_levelAssignDepth_1003_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_lmvarCounter_1004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_mvarCounter_1005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_lDecls_1006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 5, v_decls_1007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 6, v_userNames_1008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 7, v_lAssignment_1009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 8, v___x_1015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 9, v_dAssignment_1011_);
                    v___x_1017_ = v_reuseFailAlloc_1024_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1001_ == 0 {
                    leanh::lean_ctor_set(v___x_1000_, 0, v___x_1017_);
                    v___x_1019_ = v___x_1000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1023_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_cache_995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_zetaDeltaFVarIds_996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_postponed_997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_diag_998_);
                    v___x_1019_ = v_reuseFailAlloc_1023_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1020_ = lean_st_ref_set(v___y_991_, v___x_1019_);
                v___x_1021_ = leanh::lean_box(0);
                v___x_1022_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1022_, 0, v___x_1021_);
                return v___x_1022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg___boxed(
    mut v_mvarId_1027_: *mut leanh::LeanObject,
    mut v_val_1028_: *mut leanh::LeanObject,
    mut v___y_1029_: *mut leanh::LeanObject,
    mut v___y_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(
            v_mvarId_1027_,
            v_val_1028_,
            v___y_1029_,
        );
    leanh::lean_dec(v___y_1029_);
    return v_res_1031_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = leanh::lean_box(0);
    v___x_1043_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5;
    v___x_1044_ = l_Lean_mkConst(v___x_1043_, v___x_1042_);
    return v___x_1044_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(
    mut v_result_1045_: *mut leanh::LeanObject,
    mut v_mvarId_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
    mut v_a_1050_: *mut leanh::LeanObject,
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_a_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1057_: u8 = 0;
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1062_: u8 = 0;
    let mut v_unused_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1082_: u8 = 0;
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_unused_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut v_unused_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_a_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut v_a_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1121_: u8 = 0;
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1046_);
                v___x_1054_ = l_Lean_MVarId_getDecl(
                    v_mvarId_1046_,
                    v_a_1049_,
                    v_a_1050_,
                    v_a_1051_,
                    v_a_1052_,
                );
                if leanh::lean_obj_tag(v___x_1054_) == 0 {
                    if leanh::lean_obj_tag(v_result_1045_) == 0 {
                        leanh::lean_dec_ref_known(v_result_1045_, 0);
                        leanh::lean_dec(v_mvarId_1046_);
                        v_isSharedCheck_1062_ =
                            (!leanh::lean_is_exclusive(v___x_1054_)) as u8;
                        if v_isSharedCheck_1062_ == 0 {
                            v_unused_1063_ = leanh::lean_ctor_get(v___x_1054_, 0);
                            leanh::lean_dec(v_unused_1063_);
                            v___x_1056_ = v___x_1054_;
                            v_isShared_1057_ = v_isSharedCheck_1062_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1054_);
                            v___x_1056_ = leanh::lean_box(0);
                            v_isShared_1057_ = v_isSharedCheck_1062_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1064_ = leanh::lean_ctor_get(v___x_1054_, 0);
                        leanh::lean_inc(v_a_1064_);
                        leanh::lean_dec_ref_known(v___x_1054_, 1);
                        v_e_x27_1065_ = leanh::lean_ctor_get(v_result_1045_, 0);
                        leanh::lean_inc_ref_n(v_e_x27_1065_, 2);
                        v_proof_1066_ = leanh::lean_ctor_get(v_result_1045_, 1);
                        leanh::lean_inc_ref(v_proof_1066_);
                        leanh::lean_dec_ref_known(v_result_1045_, 2);
                        v_userName_1067_ = leanh::lean_ctor_get(v_a_1064_, 0);
                        leanh::lean_inc(v_userName_1067_);
                        v_type_1068_ = leanh::lean_ctor_get(v_a_1064_, 2);
                        leanh::lean_inc_ref(v_type_1068_);
                        leanh::lean_dec(v_a_1064_);
                        v___x_1069_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v_e_x27_1065_,
                            v_userName_1067_,
                            v_a_1049_,
                            v_a_1050_,
                            v_a_1051_,
                            v_a_1052_,
                        );
                        if leanh::lean_obj_tag(v___x_1069_) == 0 {
                            v_a_1070_ = leanh::lean_ctor_get(v___x_1069_, 0);
                            leanh::lean_inc(v_a_1070_);
                            leanh::lean_dec_ref_known(v___x_1069_, 1);
                            leanh::lean_inc_ref(v_type_1068_);
                            v___x_1071_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_type_1068_,
                                v_a_1048_,
                                v_a_1049_,
                                v_a_1050_,
                                v_a_1051_,
                                v_a_1052_,
                            );
                            if leanh::lean_obj_tag(v___x_1071_) == 0 {
                                v_a_1072_ = leanh::lean_ctor_get(v___x_1071_, 0);
                                leanh::lean_inc(v_a_1072_);
                                leanh::lean_dec_ref_known(v___x_1071_, 1);
                                v___x_1073_ =
                                    l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2;
                                v___x_1074_ = leanh::lean_box(0);
                                v___x_1075_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1075_, 0, v_a_1072_);
                                leanh::lean_ctor_set(v___x_1075_, 1, v___x_1074_);
                                v___x_1076_ = l_Lean_mkConst(v___x_1073_, v___x_1075_);
                                leanh::lean_inc(v_a_1070_);
                                leanh::lean_inc_ref(v_e_x27_1065_);
                                v___x_1077_ = l_Lean_mkApp4(
                                    v___x_1076_,
                                    v_type_1068_,
                                    v_e_x27_1065_,
                                    v_proof_1066_,
                                    v_a_1070_,
                                );
                                v___x_1078_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_1046_, v___x_1077_, v_a_1050_);
                                v_isSharedCheck_1100_ =
                                    (!leanh::lean_is_exclusive(v___x_1078_)) as u8;
                                if v_isSharedCheck_1100_ == 0 {
                                    v_unused_1101_ = leanh::lean_ctor_get(v___x_1078_, 0);
                                    leanh::lean_dec(v_unused_1101_);
                                    v___x_1080_ = v___x_1078_;
                                    v_isShared_1081_ = v_isSharedCheck_1100_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1078_);
                                    v___x_1080_ = leanh::lean_box(0);
                                    v_isShared_1081_ = v_isSharedCheck_1100_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1070_);
                                leanh::lean_dec_ref(v_type_1068_);
                                leanh::lean_dec_ref(v_proof_1066_);
                                leanh::lean_dec_ref(v_e_x27_1065_);
                                leanh::lean_dec(v_mvarId_1046_);
                                v_a_1102_ = leanh::lean_ctor_get(v___x_1071_, 0);
                                v_isSharedCheck_1109_ =
                                    (!leanh::lean_is_exclusive(v___x_1071_)) as u8;
                                if v_isSharedCheck_1109_ == 0 {
                                    v___x_1104_ = v___x_1071_;
                                    v_isShared_1105_ = v_isSharedCheck_1109_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1102_);
                                    leanh::lean_dec(v___x_1071_);
                                    v___x_1104_ = leanh::lean_box(0);
                                    v_isShared_1105_ = v_isSharedCheck_1109_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_type_1068_);
                            leanh::lean_dec_ref(v_proof_1066_);
                            leanh::lean_dec_ref(v_e_x27_1065_);
                            leanh::lean_dec(v_mvarId_1046_);
                            v_a_1110_ = leanh::lean_ctor_get(v___x_1069_, 0);
                            v_isSharedCheck_1117_ =
                                (!leanh::lean_is_exclusive(v___x_1069_)) as u8;
                            if v_isSharedCheck_1117_ == 0 {
                                v___x_1112_ = v___x_1069_;
                                v_isShared_1113_ = v_isSharedCheck_1117_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1110_);
                                leanh::lean_dec(v___x_1069_);
                                v___x_1112_ = leanh::lean_box(0);
                                v_isShared_1113_ = v_isSharedCheck_1117_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1046_);
                    leanh::lean_dec_ref(v_result_1045_);
                    v_a_1118_ = leanh::lean_ctor_get(v___x_1054_, 0);
                    v_isSharedCheck_1125_ = (!leanh::lean_is_exclusive(v___x_1054_)) as u8;
                    if v_isSharedCheck_1125_ == 0 {
                        v___x_1120_ = v___x_1054_;
                        v_isShared_1121_ = v_isSharedCheck_1125_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1118_);
                        leanh::lean_dec(v___x_1054_);
                        v___x_1120_ = leanh::lean_box(0);
                        v_isShared_1121_ = v_isSharedCheck_1125_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1058_ = leanh::lean_box(0);
                if v_isShared_1057_ == 0 {
                    leanh::lean_ctor_set(v___x_1056_, 0, v___x_1058_);
                    v___x_1060_ = v___x_1056_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
                    v___x_1060_ = v_reuseFailAlloc_1061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1060_;
            }
            3 => {
                v___x_1082_ = l_Lean_Expr_isTrue(v_e_x27_1065_);
                if v___x_1082_ == 0 {
                    v___x_1083_ = l_Lean_Expr_mvarId_x21(v_a_1070_);
                    leanh::lean_dec(v_a_1070_);
                    v___x_1084_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1084_, 0, v___x_1083_);
                    if v_isShared_1081_ == 0 {
                        leanh::lean_ctor_set(v___x_1080_, 0, v___x_1084_);
                        v___x_1086_ = v___x_1080_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
                        v___x_1086_ = v_reuseFailAlloc_1087_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1080_);
                    v___x_1088_ = l_Lean_Expr_mvarId_x21(v_a_1070_);
                    leanh::lean_dec(v_a_1070_);
                    v___x_1089_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once
                        ),
                        _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6,
                    );
                    v___x_1090_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v___x_1088_, v___x_1089_, v_a_1050_);
                    v_isSharedCheck_1098_ = (!leanh::lean_is_exclusive(v___x_1090_)) as u8;
                    if v_isSharedCheck_1098_ == 0 {
                        v_unused_1099_ = leanh::lean_ctor_get(v___x_1090_, 0);
                        leanh::lean_dec(v_unused_1099_);
                        v___x_1092_ = v___x_1090_;
                        v_isShared_1093_ = v_isSharedCheck_1098_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1090_);
                        v___x_1092_ = leanh::lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1098_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1086_;
            }
            5 => {
                v___x_1094_ = leanh::lean_box(1);
                if v_isShared_1093_ == 0 {
                    leanh::lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1096_ = v___x_1092_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1096_;
            }
            7 => {
                if v_isShared_1105_ == 0 {
                    v___x_1107_ = v___x_1104_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1107_;
            }
            9 => {
                if v_isShared_1113_ == 0 {
                    v___x_1115_ = v___x_1112_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
                    v___x_1115_ = v_reuseFailAlloc_1116_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1115_;
            }
            11 => {
                if v_isShared_1121_ == 0 {
                    v___x_1123_ = v___x_1120_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
                    v___x_1123_ = v_reuseFailAlloc_1124_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___boxed(
    mut v_result_1126_: *mut leanh::LeanObject,
    mut v_mvarId_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
    mut v_a_1129_: *mut leanh::LeanObject,
    mut v_a_1130_: *mut leanh::LeanObject,
    mut v_a_1131_: *mut leanh::LeanObject,
    mut v_a_1132_: *mut leanh::LeanObject,
    mut v_a_1133_: *mut leanh::LeanObject,
    mut v_a_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(
        v_result_1126_,
        v_mvarId_1127_,
        v_a_1128_,
        v_a_1129_,
        v_a_1130_,
        v_a_1131_,
        v_a_1132_,
        v_a_1133_,
    );
    leanh::lean_dec(v_a_1133_);
    leanh::lean_dec_ref(v_a_1132_);
    leanh::lean_dec(v_a_1131_);
    leanh::lean_dec_ref(v_a_1130_);
    leanh::lean_dec(v_a_1129_);
    leanh::lean_dec_ref(v_a_1128_);
    return v_res_1135_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(
    mut v_mvarId_1136_: *mut leanh::LeanObject,
    mut v_val_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
    mut v___y_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(
            v_mvarId_1136_,
            v_val_1137_,
            v___y_1141_,
        );
    return v___x_1145_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___boxed(
    mut v_mvarId_1146_: *mut leanh::LeanObject,
    mut v_val_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
    mut v___y_1149_: *mut leanh::LeanObject,
    mut v___y_1150_: *mut leanh::LeanObject,
    mut v___y_1151_: *mut leanh::LeanObject,
    mut v___y_1152_: *mut leanh::LeanObject,
    mut v___y_1153_: *mut leanh::LeanObject,
    mut v___y_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(
        v_mvarId_1146_,
        v_val_1147_,
        v___y_1148_,
        v___y_1149_,
        v___y_1150_,
        v___y_1151_,
        v___y_1152_,
        v___y_1153_,
    );
    leanh::lean_dec(v___y_1153_);
    leanh::lean_dec_ref(v___y_1152_);
    leanh::lean_dec(v___y_1151_);
    leanh::lean_dec_ref(v___y_1150_);
    leanh::lean_dec(v___y_1149_);
    leanh::lean_dec_ref(v___y_1148_);
    return v_res_1155_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0(
    mut v_00_u03b2_1156_: *mut leanh::LeanObject,
    mut v_x_1157_: *mut leanh::LeanObject,
    mut v_x_1158_: *mut leanh::LeanObject,
    mut v_x_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_x_1157_, v_x_1158_, v_x_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1161_: *mut leanh::LeanObject,
    mut v_x_1162_: *mut leanh::LeanObject,
    mut v_x_1163_: usize,
    mut v_x_1164_: usize,
    mut v_x_1165_: *mut leanh::LeanObject,
    mut v_x_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_1162_, v_x_1163_, v_x_1164_, v_x_1165_, v_x_1166_);
    return v___x_1167_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1168_: *mut leanh::LeanObject,
    mut v_x_1169_: *mut leanh::LeanObject,
    mut v_x_1170_: *mut leanh::LeanObject,
    mut v_x_1171_: *mut leanh::LeanObject,
    mut v_x_1172_: *mut leanh::LeanObject,
    mut v_x_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3822__boxed_1174_: usize = 0;
    let mut v_x_3823__boxed_1175_: usize = 0;
    let mut v_res_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3822__boxed_1174_ = leanh::lean_unbox_usize(v_x_1170_);
    leanh::lean_dec(v_x_1170_);
    v_x_3823__boxed_1175_ = leanh::lean_unbox_usize(v_x_1171_);
    leanh::lean_dec(v_x_1171_);
    v_res_1176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(v_00_u03b2_1168_, v_x_1169_, v_x_3822__boxed_1174_, v_x_3823__boxed_1175_, v_x_1172_, v_x_1173_);
    return v_res_1176_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1177_: *mut leanh::LeanObject,
    mut v_n_1178_: *mut leanh::LeanObject,
    mut v_k_1179_: *mut leanh::LeanObject,
    mut v_v_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1181_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1178_, v_k_1179_, v_v_1180_);
    return v___x_1181_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1182_: *mut leanh::LeanObject,
    mut v_depth_1183_: usize,
    mut v_keys_1184_: *mut leanh::LeanObject,
    mut v_vals_1185_: *mut leanh::LeanObject,
    mut v_heq_1186_: *mut leanh::LeanObject,
    mut v_i_1187_: *mut leanh::LeanObject,
    mut v_entries_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1183_, v_keys_1184_, v_vals_1185_, v_i_1187_, v_entries_1188_);
    return v___x_1189_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_1190_: *mut leanh::LeanObject,
    mut v_depth_1191_: *mut leanh::LeanObject,
    mut v_keys_1192_: *mut leanh::LeanObject,
    mut v_vals_1193_: *mut leanh::LeanObject,
    mut v_heq_1194_: *mut leanh::LeanObject,
    mut v_i_1195_: *mut leanh::LeanObject,
    mut v_entries_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1197_: usize = 0;
    let mut v_res_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1197_ = leanh::lean_unbox_usize(v_depth_1191_);
    leanh::lean_dec(v_depth_1191_);
    v_res_1198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1190_, v_depth_boxed_1197_, v_keys_1192_, v_vals_1193_, v_heq_1194_, v_i_1195_, v_entries_1196_);
    leanh::lean_dec_ref(v_vals_1193_);
    leanh::lean_dec_ref(v_keys_1192_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1199_: *mut leanh::LeanObject,
    mut v_x_1200_: *mut leanh::LeanObject,
    mut v_x_1201_: *mut leanh::LeanObject,
    mut v_x_1202_: *mut leanh::LeanObject,
    mut v_x_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1200_, v_x_1201_, v_x_1202_, v_x_1203_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(
    mut v_x_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1207_);
    leanh::lean_inc_ref(v___y_1206_);
    v___x_1213_ = leanh::lean_apply_7(
        v_x_1205_,
        v___y_1206_,
        v___y_1207_,
        v___y_1208_,
        v___y_1209_,
        v___y_1210_,
        v___y_1211_,
        leanh::lean_box(0),
    );
    return v___x_1213_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed(
    mut v_x_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
    mut v___y_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
    mut v___y_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(
            v_x_1214_,
            v___y_1215_,
            v___y_1216_,
            v___y_1217_,
            v___y_1218_,
            v___y_1219_,
            v___y_1220_,
        );
    leanh::lean_dec(v___y_1216_);
    leanh::lean_dec_ref(v___y_1215_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(
    mut v_mvarId_1223_: *mut leanh::LeanObject,
    mut v_x_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1226_);
                leanh::lean_inc_ref(v___y_1225_);
                v___f_1232_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___f_1232_, 0, v_x_1224_);
                leanh::lean_closure_set(v___f_1232_, 1, v___y_1225_);
                leanh::lean_closure_set(v___f_1232_, 2, v___y_1226_);
                v___x_1233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1223_,
                    v___f_1232_,
                    v___y_1227_,
                    v___y_1228_,
                    v___y_1229_,
                    v___y_1230_,
                );
                if leanh::lean_obj_tag(v___x_1233_) == 0 {
                    return v___x_1233_;
                } else {
                    v_a_1234_ = leanh::lean_ctor_get(v___x_1233_, 0);
                    v_isSharedCheck_1241_ = (!leanh::lean_is_exclusive(v___x_1233_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1236_ = v___x_1233_;
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1234_);
                        leanh::lean_dec(v___x_1233_);
                        v___x_1236_ = leanh::lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___boxed(
    mut v_mvarId_1242_: *mut leanh::LeanObject,
    mut v_x_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
    mut v___y_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
    mut v___y_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(
        v_mvarId_1242_,
        v_x_1243_,
        v___y_1244_,
        v___y_1245_,
        v___y_1246_,
        v___y_1247_,
        v___y_1248_,
        v___y_1249_,
    );
    leanh::lean_dec(v___y_1249_);
    leanh::lean_dec_ref(v___y_1248_);
    leanh::lean_dec(v___y_1247_);
    leanh::lean_dec_ref(v___y_1246_);
    leanh::lean_dec(v___y_1245_);
    leanh::lean_dec_ref(v___y_1244_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(
    mut v_00_u03b1_1252_: *mut leanh::LeanObject,
    mut v_mvarId_1253_: *mut leanh::LeanObject,
    mut v_x_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(
        v_mvarId_1253_,
        v_x_1254_,
        v___y_1255_,
        v___y_1256_,
        v___y_1257_,
        v___y_1258_,
        v___y_1259_,
        v___y_1260_,
    );
    return v___x_1262_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___boxed(
    mut v_00_u03b1_1263_: *mut leanh::LeanObject,
    mut v_mvarId_1264_: *mut leanh::LeanObject,
    mut v_x_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
    mut v___y_1269_: *mut leanh::LeanObject,
    mut v___y_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(
        v_00_u03b1_1263_,
        v_mvarId_1264_,
        v_x_1265_,
        v___y_1266_,
        v___y_1267_,
        v___y_1268_,
        v___y_1269_,
        v___y_1270_,
        v___y_1271_,
    );
    leanh::lean_dec(v___y_1271_);
    leanh::lean_dec_ref(v___y_1270_);
    leanh::lean_dec(v___y_1269_);
    leanh::lean_dec_ref(v___y_1268_);
    leanh::lean_dec(v___y_1267_);
    leanh::lean_dec_ref(v___y_1266_);
    return v_res_1273_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoal___lam__0(
    mut v_mvarId_1274_: *mut leanh::LeanObject,
    mut v_methods_1275_: *mut leanh::LeanObject,
    mut v_config_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1298_: u8 = 0;
    let mut v_a_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1274_);
                v___x_1284_ = l_Lean_MVarId_getDecl(
                    v_mvarId_1274_,
                    v___y_1279_,
                    v___y_1280_,
                    v___y_1281_,
                    v___y_1282_,
                );
                if leanh::lean_obj_tag(v___x_1284_) == 0 {
                    v_a_1285_ = leanh::lean_ctor_get(v___x_1284_, 0);
                    leanh::lean_inc(v_a_1285_);
                    leanh::lean_dec_ref_known(v___x_1284_, 1);
                    v_type_1286_ = leanh::lean_ctor_get(v_a_1285_, 2);
                    leanh::lean_inc_ref(v_type_1286_);
                    leanh::lean_dec(v_a_1285_);
                    v___x_1287_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Sym_Simp_simp___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    leanh::lean_closure_set(v___x_1287_, 0, v_type_1286_);
                    v___x_1288_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(
                        v___x_1287_,
                        v_methods_1275_,
                        v_config_1276_,
                        v___y_1277_,
                        v___y_1278_,
                        v___y_1279_,
                        v___y_1280_,
                        v___y_1281_,
                        v___y_1282_,
                    );
                    if leanh::lean_obj_tag(v___x_1288_) == 0 {
                        v_a_1289_ = leanh::lean_ctor_get(v___x_1288_, 0);
                        leanh::lean_inc(v_a_1289_);
                        leanh::lean_dec_ref_known(v___x_1288_, 1);
                        v___x_1290_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(
                            v_a_1289_,
                            v_mvarId_1274_,
                            v___y_1277_,
                            v___y_1278_,
                            v___y_1279_,
                            v___y_1280_,
                            v___y_1281_,
                            v___y_1282_,
                        );
                        return v___x_1290_;
                    } else {
                        leanh::lean_dec(v_mvarId_1274_);
                        v_a_1291_ = leanh::lean_ctor_get(v___x_1288_, 0);
                        v_isSharedCheck_1298_ =
                            (!leanh::lean_is_exclusive(v___x_1288_)) as u8;
                        if v_isSharedCheck_1298_ == 0 {
                            v___x_1293_ = v___x_1288_;
                            v_isShared_1294_ = v_isSharedCheck_1298_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1291_);
                            leanh::lean_dec(v___x_1288_);
                            v___x_1293_ = leanh::lean_box(0);
                            v_isShared_1294_ = v_isSharedCheck_1298_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_config_1276_);
                    leanh::lean_dec_ref(v_methods_1275_);
                    leanh::lean_dec(v_mvarId_1274_);
                    v_a_1299_ = leanh::lean_ctor_get(v___x_1284_, 0);
                    v_isSharedCheck_1306_ = (!leanh::lean_is_exclusive(v___x_1284_)) as u8;
                    if v_isSharedCheck_1306_ == 0 {
                        v___x_1301_ = v___x_1284_;
                        v_isShared_1302_ = v_isSharedCheck_1306_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1299_);
                        leanh::lean_dec(v___x_1284_);
                        v___x_1301_ = leanh::lean_box(0);
                        v_isShared_1302_ = v_isSharedCheck_1306_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1294_ == 0 {
                    v___x_1296_ = v___x_1293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
                    v___x_1296_ = v_reuseFailAlloc_1297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1296_;
            }
            3 => {
                if v_isShared_1302_ == 0 {
                    v___x_1304_ = v___x_1301_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
                    v___x_1304_ = v_reuseFailAlloc_1305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_simpGoal___lam__0___boxed(
    mut v_mvarId_1307_: *mut leanh::LeanObject,
    mut v_methods_1308_: *mut leanh::LeanObject,
    mut v_config_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
    mut v___y_1313_: *mut leanh::LeanObject,
    mut v___y_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lean_Meta_Sym_simpGoal___lam__0(
        v_mvarId_1307_,
        v_methods_1308_,
        v_config_1309_,
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
    );
    leanh::lean_dec(v___y_1315_);
    leanh::lean_dec_ref(v___y_1314_);
    leanh::lean_dec(v___y_1313_);
    leanh::lean_dec_ref(v___y_1312_);
    leanh::lean_dec(v___y_1311_);
    leanh::lean_dec_ref(v___y_1310_);
    return v_res_1317_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoal(
    mut v_mvarId_1318_: *mut leanh::LeanObject,
    mut v_methods_1319_: *mut leanh::LeanObject,
    mut v_config_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_a_1322_: *mut leanh::LeanObject,
    mut v_a_1323_: *mut leanh::LeanObject,
    mut v_a_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_1318_);
    v___f_1328_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_simpGoal___lam__0___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    leanh::lean_closure_set(v___f_1328_, 0, v_mvarId_1318_);
    leanh::lean_closure_set(v___f_1328_, 1, v_methods_1319_);
    leanh::lean_closure_set(v___f_1328_, 2, v_config_1320_);
    v___x_1329_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(
        v_mvarId_1318_,
        v___f_1328_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
        v_a_1325_,
        v_a_1326_,
    );
    return v___x_1329_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoal___boxed(
    mut v_mvarId_1330_: *mut leanh::LeanObject,
    mut v_methods_1331_: *mut leanh::LeanObject,
    mut v_config_1332_: *mut leanh::LeanObject,
    mut v_a_1333_: *mut leanh::LeanObject,
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_Meta_Sym_simpGoal(
        v_mvarId_1330_,
        v_methods_1331_,
        v_config_1332_,
        v_a_1333_,
        v_a_1334_,
        v_a_1335_,
        v_a_1336_,
        v_a_1337_,
        v_a_1338_,
    );
    leanh::lean_dec(v_a_1338_);
    leanh::lean_dec_ref(v_a_1337_);
    leanh::lean_dec(v_a_1336_);
    leanh::lean_dec_ref(v_a_1335_);
    leanh::lean_dec(v_a_1334_);
    leanh::lean_dec_ref(v_a_1333_);
    return v_res_1340_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(
    mut v_mvarId_1341_: *mut leanh::LeanObject,
    mut v_methods_1342_: *mut leanh::LeanObject,
    mut v_config_1343_: *mut leanh::LeanObject,
    mut v_a_1344_: *mut leanh::LeanObject,
    mut v_a_1345_: *mut leanh::LeanObject,
    mut v_a_1346_: *mut leanh::LeanObject,
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_a_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut v_unused_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1341_);
                v___x_1351_ = l_Lean_Meta_Sym_simpGoal(
                    v_mvarId_1341_,
                    v_methods_1342_,
                    v_config_1343_,
                    v_a_1344_,
                    v_a_1345_,
                    v_a_1346_,
                    v_a_1347_,
                    v_a_1348_,
                    v_a_1349_,
                );
                if leanh::lean_obj_tag(v___x_1351_) == 0 {
                    v_a_1352_ = leanh::lean_ctor_get(v___x_1351_, 0);
                    leanh::lean_inc(v_a_1352_);
                    if leanh::lean_obj_tag(v_a_1352_) == 0 {
                        v_isSharedCheck_1360_ =
                            (!leanh::lean_is_exclusive(v___x_1351_)) as u8;
                        if v_isSharedCheck_1360_ == 0 {
                            v_unused_1361_ = leanh::lean_ctor_get(v___x_1351_, 0);
                            leanh::lean_dec(v_unused_1361_);
                            v___x_1354_ = v___x_1351_;
                            v_isShared_1355_ = v_isSharedCheck_1360_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1351_);
                            v___x_1354_ = leanh::lean_box(0);
                            v_isShared_1355_ = v_isSharedCheck_1360_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1352_);
                        leanh::lean_dec(v_mvarId_1341_);
                        return v___x_1351_;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1341_);
                    return v___x_1351_;
                }
            }
            1 => {
                v___x_1356_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1356_, 0, v_mvarId_1341_);
                if v_isShared_1355_ == 0 {
                    leanh::lean_ctor_set(v___x_1354_, 0, v___x_1356_);
                    v___x_1358_ = v___x_1354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
                    v___x_1358_ = v_reuseFailAlloc_1359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_simpGoalIgnoringNoProgress___boxed(
    mut v_mvarId_1362_: *mut leanh::LeanObject,
    mut v_methods_1363_: *mut leanh::LeanObject,
    mut v_config_1364_: *mut leanh::LeanObject,
    mut v_a_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
    mut v_a_1370_: *mut leanh::LeanObject,
    mut v_a_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(
        v_mvarId_1362_,
        v_methods_1363_,
        v_config_1364_,
        v_a_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
        v_a_1370_,
    );
    leanh::lean_dec(v_a_1370_);
    leanh::lean_dec_ref(v_a_1369_);
    leanh::lean_dec(v_a_1368_);
    leanh::lean_dec_ref(v_a_1367_);
    leanh::lean_dec(v_a_1366_);
    leanh::lean_dec_ref(v_a_1365_);
    return v_res_1372_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Goal(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Goal(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Goal(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Goal(builtin);
}