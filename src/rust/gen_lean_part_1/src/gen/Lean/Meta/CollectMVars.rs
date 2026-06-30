// Lean compiler output
// Module: Lean.Meta.CollectMVars
// Imports: Lean.Util.CollectMVars Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkMVar,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_MVarId_getDecl, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::CollectMVars::{
    initialize_Lean_Util_CollectMVars, l_Lean_Expr_collectMVars,
    runtime_initialize_Lean_Util_CollectMVars,
};
static mut l_Lean_Meta_getMVars___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getMVars___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_getMVars___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getMVars___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getMVars___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_getMVars___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getMVars___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_getMVars___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getMVars___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
    mut v_e_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_unused_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = l_Lean_Expr_hasMVar(v_e_1665_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1669_, 0, v_e_1665_);
                    return v___x_1669_;
                } else {
                    v___x_1670_ = lean_st_ref_get(v___y_1666_);
                    v_mctx_1671_ = leanh::lean_ctor_get(v___x_1670_, 0);
                    leanh::lean_inc_ref(v_mctx_1671_);
                    leanh::lean_dec(v___x_1670_);
                    v___x_1672_ = l_Lean_instantiateMVarsCore(v_mctx_1671_, v_e_1665_);
                    v_fst_1673_ = leanh::lean_ctor_get(v___x_1672_, 0);
                    leanh::lean_inc(v_fst_1673_);
                    v_snd_1674_ = leanh::lean_ctor_get(v___x_1672_, 1);
                    leanh::lean_inc(v_snd_1674_);
                    leanh::lean_dec_ref(v___x_1672_);
                    v___x_1675_ = lean_st_ref_take(v___y_1666_);
                    v_cache_1676_ = leanh::lean_ctor_get(v___x_1675_, 1);
                    v_zetaDeltaFVarIds_1677_ = leanh::lean_ctor_get(v___x_1675_, 2);
                    v_postponed_1678_ = leanh::lean_ctor_get(v___x_1675_, 3);
                    v_diag_1679_ = leanh::lean_ctor_get(v___x_1675_, 4);
                    v_isSharedCheck_1688_ = (!leanh::lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v_unused_1689_ = leanh::lean_ctor_get(v___x_1675_, 0);
                        leanh::lean_dec(v_unused_1689_);
                        v___x_1681_ = v___x_1675_;
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1679_);
                        leanh::lean_inc(v_postponed_1678_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1677_);
                        leanh::lean_inc(v_cache_1676_);
                        leanh::lean_dec(v___x_1675_);
                        v___x_1681_ = leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1682_ == 0 {
                    leanh::lean_ctor_set(v___x_1681_, 0, v_snd_1674_);
                    v___x_1684_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_snd_1674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_cache_1676_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1687_,
                        2,
                        v_zetaDeltaFVarIds_1677_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_postponed_1678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_diag_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1685_ = lean_st_ref_set(v___y_1666_, v___x_1684_);
                v___x_1686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1686_, 0, v_fst_1673_);
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg___boxed(
    mut v_e_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
        v_e_1690_,
        v___y_1691_,
    );
    leanh::lean_dec(v___y_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(
    mut v_e_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
        v_e_1694_,
        v___y_1697_,
    );
    return v___x_1701_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___boxed(
    mut v_e_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(
        v_e_1702_,
        v___y_1703_,
        v___y_1704_,
        v___y_1705_,
        v___y_1706_,
        v___y_1707_,
    );
    leanh::lean_dec(v___y_1707_);
    leanh::lean_dec_ref(v___y_1706_);
    leanh::lean_dec(v___y_1705_);
    leanh::lean_dec_ref(v___y_1704_);
    leanh::lean_dec(v___y_1703_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(
    mut v_mvarId_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = lean_st_ref_get(v___y_1711_);
    v_mctx_1714_ = leanh::lean_ctor_get(v___x_1713_, 0);
    leanh::lean_inc_ref(v_mctx_1714_);
    leanh::lean_dec(v___x_1713_);
    v___x_1715_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1714_, v_mvarId_1710_);
    leanh::lean_dec_ref(v_mctx_1714_);
    v___x_1716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg___boxed(
    mut v_mvarId_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(
            v_mvarId_1717_,
            v___y_1718_,
        );
    leanh::lean_dec(v___y_1718_);
    leanh::lean_dec(v_mvarId_1717_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(
    mut v_mvarId_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
    mut v___y_1723_: *mut leanh::LeanObject,
    mut v___y_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(
            v_mvarId_1721_,
            v___y_1724_,
        );
    return v___x_1728_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___boxed(
    mut v_mvarId_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
    mut v___y_1732_: *mut leanh::LeanObject,
    mut v___y_1733_: *mut leanh::LeanObject,
    mut v___y_1734_: *mut leanh::LeanObject,
    mut v___y_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(
        v_mvarId_1729_,
        v___y_1730_,
        v___y_1731_,
        v___y_1732_,
        v___y_1733_,
        v___y_1734_,
    );
    leanh::lean_dec(v___y_1734_);
    leanh::lean_dec_ref(v___y_1733_);
    leanh::lean_dec(v___y_1732_);
    leanh::lean_dec_ref(v___y_1731_);
    leanh::lean_dec(v___y_1730_);
    leanh::lean_dec(v_mvarId_1729_);
    return v_res_1736_;
}
pub unsafe fn l_Lean_Meta_collectMVars(
    mut v_e_1737_: *mut leanh::LeanObject,
    mut v_a_1738_: *mut leanh::LeanObject,
    mut v_a_1739_: *mut leanh::LeanObject,
    mut v_a_1740_: *mut leanh::LeanObject,
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v_a_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v_a_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
                        v_e_1737_, v_a_1740_,
                    );
                if leanh::lean_obj_tag(v___x_1744_) == 0 {
                    v_a_1745_ = leanh::lean_ctor_get(v___x_1744_, 0);
                    leanh::lean_inc(v_a_1745_);
                    leanh::lean_dec_ref_known(v___x_1744_, 1);
                    v___x_1746_ = lean_st_ref_get(v_a_1738_);
                    v_result_1747_ = leanh::lean_ctor_get(v___x_1746_, 1);
                    leanh::lean_inc_ref(v_result_1747_);
                    v___x_1748_ = l_Lean_Expr_collectMVars(v___x_1746_, v_a_1745_);
                    leanh::lean_inc_ref(v___x_1748_);
                    v___x_1749_ = lean_st_ref_set(v_a_1738_, v___x_1748_);
                    v_result_1750_ = leanh::lean_ctor_get(v___x_1748_, 1);
                    leanh::lean_inc_ref(v_result_1750_);
                    leanh::lean_dec_ref(v___x_1748_);
                    v___x_1765_ = lean_array_get_size(v_result_1747_);
                    leanh::lean_dec_ref(v_result_1747_);
                    v___x_1766_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1767_ = lean_array_get_size(v_result_1750_);
                    v___x_1768_ = lean_nat_dec_le(v___x_1765_, v___x_1766_);
                    if v___x_1768_ == 0 {
                        v_lower_1752_ = v___x_1765_;
                        v_upper_1753_ = v___x_1767_;
                        state = 1;
                        continue;
                    } else {
                        v_lower_1752_ = v___x_1766_;
                        v_upper_1753_ = v___x_1767_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1769_ = leanh::lean_ctor_get(v___x_1744_, 0);
                    v_isSharedCheck_1776_ = (!leanh::lean_is_exclusive(v___x_1744_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1771_ = v___x_1744_;
                        v_isShared_1772_ = v_isSharedCheck_1776_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1769_);
                        leanh::lean_dec(v___x_1744_);
                        v___x_1771_ = leanh::lean_box(0);
                        v_isShared_1772_ = v_isSharedCheck_1776_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1754_ =
                    l_Array_toSubarray___redArg(v_result_1750_, v_lower_1752_, v_upper_1753_);
                v___x_1755_ = leanh::lean_box(0);
                v___x_1756_ =
                    l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(
                        v___x_1754_,
                        v___x_1755_,
                        v_a_1738_,
                        v_a_1739_,
                        v_a_1740_,
                        v_a_1741_,
                        v_a_1742_,
                    );
                if leanh::lean_obj_tag(v___x_1756_) == 0 {
                    v_isSharedCheck_1763_ = (!leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1763_ == 0 {
                        v_unused_1764_ = leanh::lean_ctor_get(v___x_1756_, 0);
                        leanh::lean_dec(v_unused_1764_);
                        v___x_1758_ = v___x_1756_;
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1756_);
                        v___x_1758_ = leanh::lean_box(0);
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_1756_;
                }
            }
            2 => {
                if v_isShared_1759_ == 0 {
                    leanh::lean_ctor_set(v___x_1758_, 0, v___x_1755_);
                    v___x_1761_ = v___x_1758_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1755_);
                    v___x_1761_ = v_reuseFailAlloc_1762_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1761_;
            }
            4 => {
                if v_isShared_1772_ == 0 {
                    v___x_1774_ = v___x_1771_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(
    mut v_a_1777_: *mut leanh::LeanObject,
    mut v_b_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1785_ = leanh::lean_ctor_get(v_a_1777_, 0);
                v_start_1786_ = leanh::lean_ctor_get(v_a_1777_, 1);
                v_stop_1787_ = leanh::lean_ctor_get(v_a_1777_, 2);
                v_isSharedCheck_1816_ = (!leanh::lean_is_exclusive(v_a_1777_)) as u8;
                if v_isSharedCheck_1816_ == 0 {
                    v___x_1789_ = v_a_1777_;
                    v_isShared_1790_ = v_isSharedCheck_1816_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_1787_);
                    leanh::lean_inc(v_start_1786_);
                    leanh::lean_inc(v_array_1785_);
                    leanh::lean_dec(v_a_1777_);
                    v___x_1789_ = leanh::lean_box(0);
                    v_isShared_1790_ = v_isSharedCheck_1816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1791_ = lean_nat_dec_lt(v_start_1786_, v_stop_1787_);
                if v___x_1791_ == 0 {
                    leanh::lean_del_object(v___x_1789_);
                    leanh::lean_dec(v_stop_1787_);
                    leanh::lean_dec(v_start_1786_);
                    leanh::lean_dec_ref(v_array_1785_);
                    v___x_1792_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1792_, 0, v_b_1778_);
                    return v___x_1792_;
                } else {
                    v___x_1793_ = lean_array_fget_borrowed(v_array_1785_, v_start_1786_);
                    v___x_1794_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_1793_, v___y_1781_);
                    if leanh::lean_obj_tag(v___x_1794_) == 0 {
                        v_a_1795_ = leanh::lean_ctor_get(v___x_1794_, 0);
                        leanh::lean_inc(v_a_1795_);
                        leanh::lean_dec_ref_known(v___x_1794_, 1);
                        v___x_1796_ = leanh::lean_box(0);
                        v___x_1797_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1798_ = lean_nat_add(v_start_1786_, v___x_1797_);
                        leanh::lean_dec(v_start_1786_);
                        if v_isShared_1790_ == 0 {
                            leanh::lean_ctor_set(v___x_1789_, 1, v___x_1798_);
                            v___x_1800_ = v___x_1789_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1807_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_array_1785_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1798_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_stop_1787_);
                            v___x_1800_ = v_reuseFailAlloc_1807_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1789_);
                        leanh::lean_dec(v_stop_1787_);
                        leanh::lean_dec(v_start_1786_);
                        leanh::lean_dec_ref(v_array_1785_);
                        v_a_1808_ = leanh::lean_ctor_get(v___x_1794_, 0);
                        v_isSharedCheck_1815_ =
                            (!leanh::lean_is_exclusive(v___x_1794_)) as u8;
                        if v_isSharedCheck_1815_ == 0 {
                            v___x_1810_ = v___x_1794_;
                            v_isShared_1811_ = v_isSharedCheck_1815_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1808_);
                            leanh::lean_dec(v___x_1794_);
                            v___x_1810_ = leanh::lean_box(0);
                            v_isShared_1811_ = v_isSharedCheck_1815_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_1795_) == 0 {
                    v_a_1777_ = v___x_1800_;
                    v_b_1778_ = v___x_1796_;
                    state = 0;
                    continue;
                } else {
                    v_val_1802_ = leanh::lean_ctor_get(v_a_1795_, 0);
                    leanh::lean_inc(v_val_1802_);
                    leanh::lean_dec_ref_known(v_a_1795_, 1);
                    v_mvarIdPending_1803_ = leanh::lean_ctor_get(v_val_1802_, 1);
                    leanh::lean_inc(v_mvarIdPending_1803_);
                    leanh::lean_dec(v_val_1802_);
                    v___x_1804_ = l_Lean_mkMVar(v_mvarIdPending_1803_);
                    v___x_1805_ = l_Lean_Meta_collectMVars(
                        v___x_1804_,
                        v___y_1779_,
                        v___y_1780_,
                        v___y_1781_,
                        v___y_1782_,
                        v___y_1783_,
                    );
                    if leanh::lean_obj_tag(v___x_1805_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1805_, 1);
                        v_a_1777_ = v___x_1800_;
                        v_b_1778_ = v___x_1796_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_1800_);
                        return v___x_1805_;
                    }
                }
            }
            3 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg___boxed(
    mut v_a_1817_: *mut leanh::LeanObject,
    mut v_b_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
    mut v___y_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(
        v_a_1817_,
        v_b_1818_,
        v___y_1819_,
        v___y_1820_,
        v___y_1821_,
        v___y_1822_,
        v___y_1823_,
    );
    leanh::lean_dec(v___y_1823_);
    leanh::lean_dec_ref(v___y_1822_);
    leanh::lean_dec(v___y_1821_);
    leanh::lean_dec_ref(v___y_1820_);
    leanh::lean_dec(v___y_1819_);
    return v_res_1825_;
}
pub unsafe fn l_Lean_Meta_collectMVars___boxed(
    mut v_e_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
    mut v_a_1828_: *mut leanh::LeanObject,
    mut v_a_1829_: *mut leanh::LeanObject,
    mut v_a_1830_: *mut leanh::LeanObject,
    mut v_a_1831_: *mut leanh::LeanObject,
    mut v_a_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_Meta_collectMVars(
        v_e_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_,
    );
    leanh::lean_dec(v_a_1831_);
    leanh::lean_dec_ref(v_a_1830_);
    leanh::lean_dec(v_a_1829_);
    leanh::lean_dec_ref(v_a_1828_);
    leanh::lean_dec(v_a_1827_);
    return v_res_1833_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(
    mut v_inst_1834_: *mut leanh::LeanObject,
    mut v_R_1835_: *mut leanh::LeanObject,
    mut v_a_1836_: *mut leanh::LeanObject,
    mut v_b_1837_: *mut leanh::LeanObject,
    mut v_c_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(
        v_a_1836_,
        v_b_1837_,
        v___y_1839_,
        v___y_1840_,
        v___y_1841_,
        v___y_1842_,
        v___y_1843_,
    );
    return v___x_1845_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___boxed(
    mut v_inst_1846_: *mut leanh::LeanObject,
    mut v_R_1847_: *mut leanh::LeanObject,
    mut v_a_1848_: *mut leanh::LeanObject,
    mut v_b_1849_: *mut leanh::LeanObject,
    mut v_c_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(
        v_inst_1846_,
        v_R_1847_,
        v_a_1848_,
        v_b_1849_,
        v_c_1850_,
        v___y_1851_,
        v___y_1852_,
        v___y_1853_,
        v___y_1854_,
        v___y_1855_,
    );
    leanh::lean_dec(v___y_1855_);
    leanh::lean_dec_ref(v___y_1854_);
    leanh::lean_dec(v___y_1853_);
    leanh::lean_dec_ref(v___y_1852_);
    leanh::lean_dec(v___y_1851_);
    return v_res_1857_;
}
pub unsafe fn _init_l_Lean_Meta_getMVars___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = leanh::lean_box(0);
    v___x_1859_ = leanh::lean_unsigned_to_nat(16);
    v___x_1860_ = lean_mk_array(v___x_1859_, v___x_1858_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Meta_getMVars___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__0_once),
        _init_l_Lean_Meta_getMVars___closed__0,
    );
    v___x_1862_ = leanh::lean_unsigned_to_nat(0);
    v___x_1863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Lean_Meta_getMVars___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lean_Meta_getMVars___closed__2;
    v___x_1867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__1_once),
        _init_l_Lean_Meta_getMVars___closed__1,
    );
    v___x_1868_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    leanh::lean_ctor_set(v___x_1868_, 1, v___x_1866_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_Meta_getMVars(
    mut v_e_1869_: *mut leanh::LeanObject,
    mut v_a_1870_: *mut leanh::LeanObject,
    mut v_a_1871_: *mut leanh::LeanObject,
    mut v_a_1872_: *mut leanh::LeanObject,
    mut v_a_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_unused_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1875_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__3_once),
                    _init_l_Lean_Meta_getMVars___closed__3,
                );
                v___x_1876_ = lean_st_mk_ref(v___x_1875_);
                v___x_1877_ = l_Lean_Meta_collectMVars(
                    v_e_1869_,
                    v___x_1876_,
                    v_a_1870_,
                    v_a_1871_,
                    v_a_1872_,
                    v_a_1873_,
                );
                if leanh::lean_obj_tag(v___x_1877_) == 0 {
                    v_isSharedCheck_1886_ = (!leanh::lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v_unused_1887_ = leanh::lean_ctor_get(v___x_1877_, 0);
                        leanh::lean_dec(v_unused_1887_);
                        v___x_1879_ = v___x_1877_;
                        v_isShared_1880_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1877_);
                        v___x_1879_ = leanh::lean_box(0);
                        v_isShared_1880_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1876_);
                    v_a_1888_ = leanh::lean_ctor_get(v___x_1877_, 0);
                    v_isSharedCheck_1895_ = (!leanh::lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1895_ == 0 {
                        v___x_1890_ = v___x_1877_;
                        v_isShared_1891_ = v_isSharedCheck_1895_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1888_);
                        leanh::lean_dec(v___x_1877_);
                        v___x_1890_ = leanh::lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1895_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1881_ = lean_st_ref_get(v___x_1876_);
                leanh::lean_dec(v___x_1876_);
                v_result_1882_ = leanh::lean_ctor_get(v___x_1881_, 1);
                leanh::lean_inc_ref(v_result_1882_);
                leanh::lean_dec(v___x_1881_);
                if v_isShared_1880_ == 0 {
                    leanh::lean_ctor_set(v___x_1879_, 0, v_result_1882_);
                    v___x_1884_ = v___x_1879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_result_1882_);
                    v___x_1884_ = v_reuseFailAlloc_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1884_;
            }
            3 => {
                if v_isShared_1891_ == 0 {
                    v___x_1893_ = v___x_1890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
                    v___x_1893_ = v_reuseFailAlloc_1894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getMVars___boxed(
    mut v_e_1896_: *mut leanh::LeanObject,
    mut v_a_1897_: *mut leanh::LeanObject,
    mut v_a_1898_: *mut leanh::LeanObject,
    mut v_a_1899_: *mut leanh::LeanObject,
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_Meta_getMVars(v_e_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
    leanh::lean_dec(v_a_1900_);
    leanh::lean_dec_ref(v_a_1899_);
    leanh::lean_dec(v_a_1898_);
    leanh::lean_dec_ref(v_a_1897_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_1903_: *mut leanh::LeanObject,
    mut v_i_1904_: *mut leanh::LeanObject,
    mut v_k_1905_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v_k_x27_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1906_ = lean_array_get_size(v_keys_1903_);
                v___x_1907_ = lean_nat_dec_lt(v_i_1904_, v___x_1906_);
                if v___x_1907_ == 0 {
                    leanh::lean_dec(v_i_1904_);
                    return v___x_1907_;
                } else {
                    v_k_x27_1908_ = lean_array_fget_borrowed(v_keys_1903_, v_i_1904_);
                    v___x_1909_ = l_Lean_instBEqMVarId_beq(v_k_1905_, v_k_x27_1908_);
                    if v___x_1909_ == 0 {
                        v___x_1910_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1911_ = lean_nat_add(v_i_1904_, v___x_1910_);
                        leanh::lean_dec(v_i_1904_);
                        v_i_1904_ = v___x_1911_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1904_);
                        return v___x_1909_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_1913_: *mut leanh::LeanObject,
    mut v_i_1914_: *mut leanh::LeanObject,
    mut v_k_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1916_: u8 = 0;
    let mut v_r_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1913_, v_i_1914_, v_k_1915_);
    leanh::lean_dec(v_k_1915_);
    leanh::lean_dec_ref(v_keys_1913_);
    v_r_1917_ = leanh::lean_box((v_res_1916_) as usize);
    return v_r_1917_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1918_: usize = 0;
    let mut v___x_1919_: usize = 0;
    let mut v___x_1920_: usize = 0;
    v___x_1918_ = 5usize;
    v___x_1919_ = 1usize;
    v___x_1920_ = lean_usize_shift_left(v___x_1919_, v___x_1918_);
    return v___x_1920_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: usize = 0;
    let mut v___x_1923_: usize = 0;
    v___x_1921_ = 1usize;
    v___x_1922_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1923_ = lean_usize_sub(v___x_1922_, v___x_1921_);
    return v___x_1923_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(
    mut v_x_1924_: *mut leanh::LeanObject,
    mut v_x_1925_: usize,
    mut v_x_1926_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: usize = 0;
    let mut v___x_1931_: usize = 0;
    let mut v_j_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v_node_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: usize = 0;
    let mut v___x_1939_: u8 = 0;
    let mut v_ks_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1924_) == 0 {
                    v_es_1927_ = leanh::lean_ctor_get(v_x_1924_, 0);
                    v___x_1928_ = leanh::lean_box(2);
                    v___x_1929_ = 5usize;
                    v___x_1930_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1931_ = lean_usize_land(v_x_1925_, v___x_1930_);
                    v_j_1932_ = lean_usize_to_nat(v___x_1931_);
                    v___x_1933_ = lean_array_get_borrowed(v___x_1928_, v_es_1927_, v_j_1932_);
                    leanh::lean_dec(v_j_1932_);
                    match leanh::lean_obj_tag(v___x_1933_) {
                        0 => {
                            v_key_1934_ = leanh::lean_ctor_get(v___x_1933_, 0);
                            v___x_1935_ = l_Lean_instBEqMVarId_beq(v_x_1926_, v_key_1934_);
                            return v___x_1935_;
                        }
                        1 => {
                            v_node_1936_ = leanh::lean_ctor_get(v___x_1933_, 0);
                            v___x_1937_ = lean_usize_shift_right(v_x_1925_, v___x_1929_);
                            v_x_1924_ = v_node_1936_;
                            v_x_1925_ = v___x_1937_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1939_ = 0;
                            return v___x_1939_;
                        }
                    }
                } else {
                    v_ks_1940_ = leanh::lean_ctor_get(v_x_1924_, 0);
                    v___x_1941_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1942_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1940_, v___x_1941_, v_x_1926_);
                    return v___x_1942_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1943_: *mut leanh::LeanObject,
    mut v_x_1944_: *mut leanh::LeanObject,
    mut v_x_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1309__boxed_1946_: usize = 0;
    let mut v_res_1947_: u8 = 0;
    let mut v_r_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1309__boxed_1946_ = leanh::lean_unbox_usize(v_x_1944_);
    leanh::lean_dec(v_x_1944_);
    v_res_1947_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_1943_, v_x_1309__boxed_1946_, v_x_1945_);
    leanh::lean_dec(v_x_1945_);
    leanh::lean_dec_ref(v_x_1943_);
    v_r_1948_ = leanh::lean_box((v_res_1947_) as usize);
    return v_r_1948_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(
    mut v_x_1949_: *mut leanh::LeanObject,
    mut v_x_1950_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1951_: u64 = 0;
    let mut v___x_1952_: usize = 0;
    let mut v___x_1953_: u8 = 0;
    v___x_1951_ = l_Lean_instHashableMVarId_hash(v_x_1950_);
    v___x_1952_ = lean_uint64_to_usize(v___x_1951_);
    v___x_1953_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_1949_, v___x_1952_, v_x_1950_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg___boxed(
    mut v_x_1954_: *mut leanh::LeanObject,
    mut v_x_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1956_: u8 = 0;
    let mut v_r_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1956_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_1954_, v_x_1955_);
    leanh::lean_dec(v_x_1955_);
    leanh::lean_dec_ref(v_x_1954_);
    v_r_1957_ = leanh::lean_box((v_res_1956_) as usize);
    return v_r_1957_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(
    mut v_mvarId_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = lean_st_ref_get(v___y_1959_);
    v_mctx_1962_ = leanh::lean_ctor_get(v___x_1961_, 0);
    leanh::lean_inc_ref(v_mctx_1962_);
    leanh::lean_dec(v___x_1961_);
    v_dAssignment_1963_ = leanh::lean_ctor_get(v_mctx_1962_, 9);
    leanh::lean_inc_ref(v_dAssignment_1963_);
    leanh::lean_dec_ref(v_mctx_1962_);
    v___x_1964_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_1963_, v_mvarId_1958_);
    leanh::lean_dec_ref(v_dAssignment_1963_);
    v___x_1965_ = leanh::lean_box((v___x_1964_) as usize);
    v___x_1966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1966_, 0, v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(
    mut v_mvarId_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ =
        l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(
            v_mvarId_1967_,
            v___y_1968_,
        );
    leanh::lean_dec(v___y_1968_);
    leanh::lean_dec(v_mvarId_1967_);
    return v_res_1970_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(
    mut v_as_1971_: *mut leanh::LeanObject,
    mut v_i_1972_: usize,
    mut v_stop_1973_: usize,
    mut v_b_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: usize = 0;
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v_a_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v_a_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1985_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
                if v___x_1985_ == 0 {
                    v___x_1986_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
                    v___x_1989_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_1986_, v___y_1976_);
                    if leanh::lean_obj_tag(v___x_1989_) == 0 {
                        v_a_1990_ = leanh::lean_ctor_get(v___x_1989_, 0);
                        leanh::lean_inc(v_a_1990_);
                        leanh::lean_dec_ref_known(v___x_1989_, 1);
                        v___x_1991_ = (leanh::lean_unbox(v_a_1990_) as u8);
                        leanh::lean_dec(v_a_1990_);
                        if v___x_1991_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1981_ = v_b_1974_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1989_) == 0 {
                            v_a_1992_ = leanh::lean_ctor_get(v___x_1989_, 0);
                            leanh::lean_inc(v_a_1992_);
                            leanh::lean_dec_ref_known(v___x_1989_, 1);
                            v___x_1993_ = (leanh::lean_unbox(v_a_1992_) as u8);
                            leanh::lean_dec(v_a_1992_);
                            if v___x_1993_ == 0 {
                                v_a_1981_ = v_b_1974_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_1974_);
                            v_a_1994_ = leanh::lean_ctor_get(v___x_1989_, 0);
                            v_isSharedCheck_2001_ =
                                (!leanh::lean_is_exclusive(v___x_1989_)) as u8;
                            if v_isSharedCheck_2001_ == 0 {
                                v___x_1996_ = v___x_1989_;
                                v_isShared_1997_ = v_isSharedCheck_2001_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1994_);
                                leanh::lean_dec(v___x_1989_);
                                v___x_1996_ = leanh::lean_box(0);
                                v_isShared_1997_ = v_isSharedCheck_2001_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2002_, 0, v_b_1974_);
                    return v___x_2002_;
                }
            }
            1 => {
                v___x_1982_ = 1usize;
                v___x_1983_ = lean_usize_add(v_i_1972_, v___x_1982_);
                v_i_1972_ = v___x_1983_;
                v_b_1974_ = v_a_1981_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v___x_1986_);
                v___x_1988_ = lean_array_push(v_b_1974_, v___x_1986_);
                v_a_1981_ = v___x_1988_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_1997_ == 0 {
                    v___x_1999_ = v___x_1996_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
                    v___x_1999_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1___boxed(
    mut v_as_2003_: *mut leanh::LeanObject,
    mut v_i_2004_: *mut leanh::LeanObject,
    mut v_stop_2005_: *mut leanh::LeanObject,
    mut v_b_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
    mut v___y_2010_: *mut leanh::LeanObject,
    mut v___y_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2012_: usize = 0;
    let mut v_stop_boxed_2013_: usize = 0;
    let mut v_res_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2012_ = leanh::lean_unbox_usize(v_i_2004_);
    leanh::lean_dec(v_i_2004_);
    v_stop_boxed_2013_ = leanh::lean_unbox_usize(v_stop_2005_);
    leanh::lean_dec(v_stop_2005_);
    v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_2003_, v_i_boxed_2012_, v_stop_boxed_2013_, v_b_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
    leanh::lean_dec(v___y_2010_);
    leanh::lean_dec_ref(v___y_2009_);
    leanh::lean_dec(v___y_2008_);
    leanh::lean_dec_ref(v___y_2007_);
    leanh::lean_dec_ref(v_as_2003_);
    return v_res_2014_;
}
pub unsafe fn l_Lean_Meta_getMVarsNoDelayed(
    mut v_e_2015_: *mut leanh::LeanObject,
    mut v_a_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: usize = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: usize = 0;
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2021_ =
                    l_Lean_Meta_getMVars(v_e_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                if leanh::lean_obj_tag(v___x_2021_) == 0 {
                    v_a_2022_ = leanh::lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2043_ = (!leanh::lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2043_ == 0 {
                        v___x_2024_ = v___x_2021_;
                        v_isShared_2025_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2022_);
                        leanh::lean_dec(v___x_2021_);
                        v___x_2024_ = leanh::lean_box(0);
                        v_isShared_2025_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2021_;
                }
            }
            1 => {
                v___x_2026_ = leanh::lean_unsigned_to_nat(0);
                v___x_2027_ = lean_array_get_size(v_a_2022_);
                v___x_2028_ = l_Lean_Meta_getMVars___closed__2;
                v___x_2029_ = lean_nat_dec_lt(v___x_2026_, v___x_2027_);
                if v___x_2029_ == 0 {
                    leanh::lean_dec(v_a_2022_);
                    if v_isShared_2025_ == 0 {
                        leanh::lean_ctor_set(v___x_2024_, 0, v___x_2028_);
                        v___x_2031_ = v___x_2024_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2028_);
                        v___x_2031_ = v_reuseFailAlloc_2032_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2033_ = lean_nat_dec_le(v___x_2027_, v___x_2027_);
                    if v___x_2033_ == 0 {
                        if v___x_2029_ == 0 {
                            leanh::lean_dec(v_a_2022_);
                            if v_isShared_2025_ == 0 {
                                leanh::lean_ctor_set(v___x_2024_, 0, v___x_2028_);
                                v___x_2035_ = v___x_2024_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2036_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2028_);
                                v___x_2035_ = v_reuseFailAlloc_2036_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2024_);
                            v___x_2037_ = 0usize;
                            v___x_2038_ = lean_usize_of_nat(v___x_2027_);
                            v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_2022_, v___x_2037_, v___x_2038_, v___x_2028_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                            leanh::lean_dec(v_a_2022_);
                            return v___x_2039_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2024_);
                        v___x_2040_ = 0usize;
                        v___x_2041_ = lean_usize_of_nat(v___x_2027_);
                        v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_2022_, v___x_2040_, v___x_2041_, v___x_2028_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                        leanh::lean_dec(v_a_2022_);
                        return v___x_2042_;
                    }
                }
            }
            2 => {
                return v___x_2031_;
            }
            3 => {
                return v___x_2035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getMVarsNoDelayed___boxed(
    mut v_e_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
    mut v_a_2047_: *mut leanh::LeanObject,
    mut v_a_2048_: *mut leanh::LeanObject,
    mut v_a_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2050_ =
        l_Lean_Meta_getMVarsNoDelayed(v_e_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
    leanh::lean_dec(v_a_2048_);
    leanh::lean_dec_ref(v_a_2047_);
    leanh::lean_dec(v_a_2046_);
    leanh::lean_dec_ref(v_a_2045_);
    return v_res_2050_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(
    mut v_mvarId_2051_: *mut leanh::LeanObject,
    mut v___y_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ =
        l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(
            v_mvarId_2051_,
            v___y_2053_,
        );
    return v___x_2057_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(
    mut v_mvarId_2058_: *mut leanh::LeanObject,
    mut v___y_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(
        v_mvarId_2058_,
        v___y_2059_,
        v___y_2060_,
        v___y_2061_,
        v___y_2062_,
    );
    leanh::lean_dec(v___y_2062_);
    leanh::lean_dec_ref(v___y_2061_);
    leanh::lean_dec(v___y_2060_);
    leanh::lean_dec_ref(v___y_2059_);
    leanh::lean_dec(v_mvarId_2058_);
    return v_res_2064_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(
    mut v_00_u03b2_2065_: *mut leanh::LeanObject,
    mut v_x_2066_: *mut leanh::LeanObject,
    mut v_x_2067_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2068_: u8 = 0;
    v___x_2068_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_2066_, v_x_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(
    mut v_00_u03b2_2069_: *mut leanh::LeanObject,
    mut v_x_2070_: *mut leanh::LeanObject,
    mut v_x_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2072_: u8 = 0;
    let mut v_r_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_2069_, v_x_2070_, v_x_2071_);
    leanh::lean_dec(v_x_2071_);
    leanh::lean_dec_ref(v_x_2070_);
    v_r_2073_ = leanh::lean_box((v_res_2072_) as usize);
    return v_r_2073_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2074_: *mut leanh::LeanObject,
    mut v_x_2075_: *mut leanh::LeanObject,
    mut v_x_2076_: usize,
    mut v_x_2077_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2078_: u8 = 0;
    v___x_2078_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_2075_, v_x_2076_, v_x_2077_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2079_: *mut leanh::LeanObject,
    mut v_x_2080_: *mut leanh::LeanObject,
    mut v_x_2081_: *mut leanh::LeanObject,
    mut v_x_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1520__boxed_2083_: usize = 0;
    let mut v_res_2084_: u8 = 0;
    let mut v_r_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1520__boxed_2083_ = leanh::lean_unbox_usize(v_x_2081_);
    leanh::lean_dec(v_x_2081_);
    v_res_2084_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_2079_, v_x_2080_, v_x_1520__boxed_2083_, v_x_2082_);
    leanh::lean_dec(v_x_2082_);
    leanh::lean_dec_ref(v_x_2080_);
    v_r_2085_ = leanh::lean_box((v_res_2084_) as usize);
    return v_r_2085_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2086_: *mut leanh::LeanObject,
    mut v_keys_2087_: *mut leanh::LeanObject,
    mut v_vals_2088_: *mut leanh::LeanObject,
    mut v_heq_2089_: *mut leanh::LeanObject,
    mut v_i_2090_: *mut leanh::LeanObject,
    mut v_k_2091_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2092_: u8 = 0;
    v___x_2092_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2087_, v_i_2090_, v_k_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2093_: *mut leanh::LeanObject,
    mut v_keys_2094_: *mut leanh::LeanObject,
    mut v_vals_2095_: *mut leanh::LeanObject,
    mut v_heq_2096_: *mut leanh::LeanObject,
    mut v_i_2097_: *mut leanh::LeanObject,
    mut v_k_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2099_: u8 = 0;
    let mut v_r_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2093_, v_keys_2094_, v_vals_2095_, v_heq_2096_, v_i_2097_, v_k_2098_);
    leanh::lean_dec(v_k_2098_);
    leanh::lean_dec_ref(v_vals_2095_);
    leanh::lean_dec_ref(v_keys_2094_);
    v_r_2100_ = leanh::lean_box((v_res_2099_) as usize);
    return v_r_2100_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(
    mut v_x_2101_: *mut leanh::LeanObject,
    mut v_x_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2102_) == 0 {
                    v___x_2109_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2109_, 0, v_x_2101_);
                    return v___x_2109_;
                } else {
                    v_head_2110_ = leanh::lean_ctor_get(v_x_2102_, 0);
                    leanh::lean_inc(v_head_2110_);
                    v_tail_2111_ = leanh::lean_ctor_get(v_x_2102_, 1);
                    leanh::lean_inc(v_tail_2111_);
                    leanh::lean_dec_ref_known(v_x_2102_, 2);
                    v_type_2112_ = leanh::lean_ctor_get(v_head_2110_, 1);
                    leanh::lean_inc_ref(v_type_2112_);
                    leanh::lean_dec(v_head_2110_);
                    v___x_2113_ = l_Lean_Meta_collectMVars(
                        v_type_2112_,
                        v___y_2103_,
                        v___y_2104_,
                        v___y_2105_,
                        v___y_2106_,
                        v___y_2107_,
                    );
                    if leanh::lean_obj_tag(v___x_2113_) == 0 {
                        v_a_2114_ = leanh::lean_ctor_get(v___x_2113_, 0);
                        leanh::lean_inc(v_a_2114_);
                        leanh::lean_dec_ref_known(v___x_2113_, 1);
                        v_x_2101_ = v_a_2114_;
                        v_x_2102_ = v_tail_2111_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_2111_);
                        return v___x_2113_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(
    mut v_x_2116_: *mut leanh::LeanObject,
    mut v_x_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_2116_, v_x_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    leanh::lean_dec(v___y_2122_);
    leanh::lean_dec_ref(v___y_2121_);
    leanh::lean_dec(v___y_2120_);
    leanh::lean_dec_ref(v___y_2119_);
    leanh::lean_dec(v___y_2118_);
    return v_res_2124_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(
    mut v_x_2125_: *mut leanh::LeanObject,
    mut v_x_2126_: *mut leanh::LeanObject,
    mut v___y_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
    mut v___y_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2126_) == 0 {
                    v___x_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2133_, 0, v_x_2125_);
                    return v___x_2133_;
                } else {
                    v_head_2134_ = leanh::lean_ctor_get(v_x_2126_, 0);
                    leanh::lean_inc(v_head_2134_);
                    v_tail_2135_ = leanh::lean_ctor_get(v_x_2126_, 1);
                    leanh::lean_inc(v_tail_2135_);
                    leanh::lean_dec_ref_known(v_x_2126_, 2);
                    v_type_2140_ = leanh::lean_ctor_get(v_head_2134_, 1);
                    leanh::lean_inc_ref(v_type_2140_);
                    v_ctors_2141_ = leanh::lean_ctor_get(v_head_2134_, 2);
                    leanh::lean_inc(v_ctors_2141_);
                    leanh::lean_dec(v_head_2134_);
                    v___x_2142_ = l_Lean_Meta_collectMVars(
                        v_type_2140_,
                        v___y_2127_,
                        v___y_2128_,
                        v___y_2129_,
                        v___y_2130_,
                        v___y_2131_,
                    );
                    if leanh::lean_obj_tag(v___x_2142_) == 0 {
                        v_a_2143_ = leanh::lean_ctor_get(v___x_2142_, 0);
                        leanh::lean_inc(v_a_2143_);
                        leanh::lean_dec_ref_known(v___x_2142_, 1);
                        v___x_2144_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_2143_, v_ctors_2141_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
                        v___y_2137_ = v___x_2144_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_ctors_2141_);
                        v___y_2137_ = v___x_2142_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2137_) == 0 {
                    v_a_2138_ = leanh::lean_ctor_get(v___y_2137_, 0);
                    leanh::lean_inc(v_a_2138_);
                    leanh::lean_dec_ref_known(v___y_2137_, 1);
                    v_x_2125_ = v_a_2138_;
                    v_x_2126_ = v_tail_2135_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_2135_);
                    return v___y_2137_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(
    mut v_x_2145_: *mut leanh::LeanObject,
    mut v_x_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_2145_, v_x_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
    leanh::lean_dec(v___y_2151_);
    leanh::lean_dec_ref(v___y_2150_);
    leanh::lean_dec(v___y_2149_);
    leanh::lean_dec_ref(v___y_2148_);
    leanh::lean_dec(v___y_2147_);
    return v_res_2153_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(
    mut v_x_2154_: *mut leanh::LeanObject,
    mut v_x_2155_: *mut leanh::LeanObject,
    mut v___y_2156_: *mut leanh::LeanObject,
    mut v___y_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
    mut v___y_2159_: *mut leanh::LeanObject,
    mut v___y_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2155_) == 0 {
                    v___x_2162_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2162_, 0, v_x_2154_);
                    return v___x_2162_;
                } else {
                    v_head_2163_ = leanh::lean_ctor_get(v_x_2155_, 0);
                    leanh::lean_inc(v_head_2163_);
                    v_tail_2164_ = leanh::lean_ctor_get(v_x_2155_, 1);
                    leanh::lean_inc(v_tail_2164_);
                    leanh::lean_dec_ref_known(v_x_2155_, 2);
                    v_toConstantVal_2169_ = leanh::lean_ctor_get(v_head_2163_, 0);
                    leanh::lean_inc_ref(v_toConstantVal_2169_);
                    v_value_2170_ = leanh::lean_ctor_get(v_head_2163_, 1);
                    leanh::lean_inc_ref(v_value_2170_);
                    leanh::lean_dec(v_head_2163_);
                    v_type_2171_ = leanh::lean_ctor_get(v_toConstantVal_2169_, 2);
                    leanh::lean_inc_ref(v_type_2171_);
                    leanh::lean_dec_ref(v_toConstantVal_2169_);
                    v___x_2172_ = l_Lean_Meta_collectMVars(
                        v_type_2171_,
                        v___y_2156_,
                        v___y_2157_,
                        v___y_2158_,
                        v___y_2159_,
                        v___y_2160_,
                    );
                    if leanh::lean_obj_tag(v___x_2172_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2172_, 1);
                        v___x_2173_ = l_Lean_Meta_collectMVars(
                            v_value_2170_,
                            v___y_2156_,
                            v___y_2157_,
                            v___y_2158_,
                            v___y_2159_,
                            v___y_2160_,
                        );
                        v___y_2166_ = v___x_2173_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_value_2170_);
                        v___y_2166_ = v___x_2172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2166_) == 0 {
                    v_a_2167_ = leanh::lean_ctor_get(v___y_2166_, 0);
                    leanh::lean_inc(v_a_2167_);
                    leanh::lean_dec_ref_known(v___y_2166_, 1);
                    v_x_2154_ = v_a_2167_;
                    v_x_2155_ = v_tail_2164_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_2164_);
                    return v___y_2166_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(
    mut v_x_2174_: *mut leanh::LeanObject,
    mut v_x_2175_: *mut leanh::LeanObject,
    mut v___y_2176_: *mut leanh::LeanObject,
    mut v___y_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2182_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_2174_, v_x_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
    leanh::lean_dec(v___y_2180_);
    leanh::lean_dec_ref(v___y_2179_);
    leanh::lean_dec(v___y_2178_);
    leanh::lean_dec_ref(v___y_2177_);
    leanh::lean_dec(v___y_2176_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(
    mut v_d_2183_: *mut leanh::LeanObject,
    mut v_a_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v___y_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_d_2183_) {
        0 => {
            let mut v_val_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2191_ = leanh::lean_ctor_get(v_d_2183_, 0);
            leanh::lean_inc_ref(v_val_2191_);
            leanh::lean_dec_ref_known(v_d_2183_, 1);
            v_toConstantVal_2192_ = leanh::lean_ctor_get(v_val_2191_, 0);
            leanh::lean_inc_ref(v_toConstantVal_2192_);
            leanh::lean_dec_ref(v_val_2191_);
            v_type_2193_ = leanh::lean_ctor_get(v_toConstantVal_2192_, 2);
            leanh::lean_inc_ref(v_type_2193_);
            leanh::lean_dec_ref(v_toConstantVal_2192_);
            v___x_2194_ = l_Lean_Meta_collectMVars(
                v_type_2193_,
                v___y_2185_,
                v___y_2186_,
                v___y_2187_,
                v___y_2188_,
                v___y_2189_,
            );
            return v___x_2194_;
        }
        4 => {
            let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2195_, 0, v_a_2184_);
            return v___x_2195_;
        }
        5 => {
            let mut v_defns_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_defns_2196_ = leanh::lean_ctor_get(v_d_2183_, 0);
            leanh::lean_inc(v_defns_2196_);
            leanh::lean_dec_ref_known(v_d_2183_, 1);
            v___x_2197_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_2184_, v_defns_2196_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
            return v___x_2197_;
        }
        6 => {
            let mut v_types_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_types_2198_ = leanh::lean_ctor_get(v_d_2183_, 2);
            leanh::lean_inc(v_types_2198_);
            leanh::lean_dec_ref_known(v_d_2183_, 3);
            v___x_2199_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_2184_, v_types_2198_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
            return v___x_2199_;
        }
        _ => {
            let mut v_val_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2200_ = leanh::lean_ctor_get(v_d_2183_, 0);
            leanh::lean_inc_ref(v_val_2200_);
            leanh::lean_dec(v_d_2183_);
            v_toConstantVal_2201_ = leanh::lean_ctor_get(v_val_2200_, 0);
            leanh::lean_inc_ref(v_toConstantVal_2201_);
            v_value_2202_ = leanh::lean_ctor_get(v_val_2200_, 1);
            leanh::lean_inc_ref(v_value_2202_);
            leanh::lean_dec_ref(v_val_2200_);
            v_type_2203_ = leanh::lean_ctor_get(v_toConstantVal_2201_, 2);
            leanh::lean_inc_ref(v_type_2203_);
            leanh::lean_dec_ref(v_toConstantVal_2201_);
            v___x_2204_ = l_Lean_Meta_collectMVars(
                v_type_2203_,
                v___y_2185_,
                v___y_2186_,
                v___y_2187_,
                v___y_2188_,
                v___y_2189_,
            );
            if leanh::lean_obj_tag(v___x_2204_) == 0 {
                let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_2204_, 1);
                v___x_2205_ = l_Lean_Meta_collectMVars(
                    v_value_2202_,
                    v___y_2185_,
                    v___y_2186_,
                    v___y_2187_,
                    v___y_2188_,
                    v___y_2189_,
                );
                return v___x_2205_;
            } else {
                leanh::lean_dec_ref(v_value_2202_);
                return v___x_2204_;
            }
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(
    mut v_d_2206_: *mut leanh::LeanObject,
    mut v_a_2207_: *mut leanh::LeanObject,
    mut v___y_2208_: *mut leanh::LeanObject,
    mut v___y_2209_: *mut leanh::LeanObject,
    mut v___y_2210_: *mut leanh::LeanObject,
    mut v___y_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
    mut v___y_2213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(
        v_d_2206_,
        v_a_2207_,
        v___y_2208_,
        v___y_2209_,
        v___y_2210_,
        v___y_2211_,
        v___y_2212_,
    );
    leanh::lean_dec(v___y_2212_);
    leanh::lean_dec_ref(v___y_2211_);
    leanh::lean_dec(v___y_2210_);
    leanh::lean_dec_ref(v___y_2209_);
    leanh::lean_dec(v___y_2208_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_Meta_collectMVarsAtDecl(
    mut v_d_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_a_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
    mut v_a_2219_: *mut leanh::LeanObject,
    mut v_a_2220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2222_ = leanh::lean_box(0);
    v___x_2223_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(
        v_d_2215_,
        v___x_2222_,
        v_a_2216_,
        v_a_2217_,
        v_a_2218_,
        v_a_2219_,
        v_a_2220_,
    );
    return v___x_2223_;
}
pub unsafe fn l_Lean_Meta_collectMVarsAtDecl___boxed(
    mut v_d_2224_: *mut leanh::LeanObject,
    mut v_a_2225_: *mut leanh::LeanObject,
    mut v_a_2226_: *mut leanh::LeanObject,
    mut v_a_2227_: *mut leanh::LeanObject,
    mut v_a_2228_: *mut leanh::LeanObject,
    mut v_a_2229_: *mut leanh::LeanObject,
    mut v_a_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_Meta_collectMVarsAtDecl(
        v_d_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_,
    );
    leanh::lean_dec(v_a_2229_);
    leanh::lean_dec_ref(v_a_2228_);
    leanh::lean_dec(v_a_2227_);
    leanh::lean_dec_ref(v_a_2226_);
    leanh::lean_dec(v_a_2225_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_Meta_getMVarsAtDecl(
    mut v_d_2232_: *mut leanh::LeanObject,
    mut v_a_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2243_: u8 = 0;
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_unused_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2254_: u8 = 0;
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2238_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__3_once),
                    _init_l_Lean_Meta_getMVars___closed__3,
                );
                v___x_2239_ = lean_st_mk_ref(v___x_2238_);
                v___x_2240_ = l_Lean_Meta_collectMVarsAtDecl(
                    v_d_2232_,
                    v___x_2239_,
                    v_a_2233_,
                    v_a_2234_,
                    v_a_2235_,
                    v_a_2236_,
                );
                if leanh::lean_obj_tag(v___x_2240_) == 0 {
                    v_isSharedCheck_2249_ = (!leanh::lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v_unused_2250_ = leanh::lean_ctor_get(v___x_2240_, 0);
                        leanh::lean_dec(v_unused_2250_);
                        v___x_2242_ = v___x_2240_;
                        v_isShared_2243_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2240_);
                        v___x_2242_ = leanh::lean_box(0);
                        v_isShared_2243_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2239_);
                    v_a_2251_ = leanh::lean_ctor_get(v___x_2240_, 0);
                    v_isSharedCheck_2258_ = (!leanh::lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2258_ == 0 {
                        v___x_2253_ = v___x_2240_;
                        v_isShared_2254_ = v_isSharedCheck_2258_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2251_);
                        leanh::lean_dec(v___x_2240_);
                        v___x_2253_ = leanh::lean_box(0);
                        v_isShared_2254_ = v_isSharedCheck_2258_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2244_ = lean_st_ref_get(v___x_2239_);
                leanh::lean_dec(v___x_2239_);
                v_result_2245_ = leanh::lean_ctor_get(v___x_2244_, 1);
                leanh::lean_inc_ref(v_result_2245_);
                leanh::lean_dec(v___x_2244_);
                if v_isShared_2243_ == 0 {
                    leanh::lean_ctor_set(v___x_2242_, 0, v_result_2245_);
                    v___x_2247_ = v___x_2242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_result_2245_);
                    v___x_2247_ = v_reuseFailAlloc_2248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2247_;
            }
            3 => {
                if v_isShared_2254_ == 0 {
                    v___x_2256_ = v___x_2253_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2257_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
                    v___x_2256_ = v_reuseFailAlloc_2257_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getMVarsAtDecl___boxed(
    mut v_d_2259_: *mut leanh::LeanObject,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
    mut v_a_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
    mut v_a_2264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2265_ = l_Lean_Meta_getMVarsAtDecl(v_d_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
    leanh::lean_dec(v_a_2263_);
    leanh::lean_dec_ref(v_a_2262_);
    leanh::lean_dec(v_a_2261_);
    leanh::lean_dec_ref(v_a_2260_);
    return v_res_2265_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(
    mut v_mvarId_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: u8 = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2269_ = lean_st_ref_get(v___y_2267_);
    v_mctx_2270_ = leanh::lean_ctor_get(v___x_2269_, 0);
    leanh::lean_inc_ref(v_mctx_2270_);
    leanh::lean_dec(v___x_2269_);
    v_dAssignment_2271_ = leanh::lean_ctor_get(v_mctx_2270_, 9);
    leanh::lean_inc_ref(v_dAssignment_2271_);
    leanh::lean_dec_ref(v_mctx_2270_);
    v___x_2272_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_2271_, v_mvarId_2266_);
    leanh::lean_dec_ref(v_dAssignment_2271_);
    v___x_2273_ = leanh::lean_box((v___x_2272_) as usize);
    v___x_2274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2274_, 0, v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(
    mut v_mvarId_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_2275_, v___y_2276_);
    leanh::lean_dec(v___y_2276_);
    leanh::lean_dec(v_mvarId_2275_);
    return v_res_2278_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_x_2280_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2281_: u8 = 0;
    let mut v_key_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2280_) == 0 {
                    v___x_2281_ = 0;
                    return v___x_2281_;
                } else {
                    v_key_2282_ = leanh::lean_ctor_get(v_x_2280_, 0);
                    v_tail_2283_ = leanh::lean_ctor_get(v_x_2280_, 2);
                    v___x_2284_ = l_Lean_instBEqMVarId_beq(v_key_2282_, v_a_2279_);
                    if v___x_2284_ == 0 {
                        v_x_2280_ = v_tail_2283_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2284_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg___boxed(
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_x_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2288_: u8 = 0;
    let mut v_r_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_2286_, v_x_2287_);
    leanh::lean_dec(v_x_2287_);
    leanh::lean_dec(v_a_2286_);
    v_r_2289_ = leanh::lean_box((v_res_2288_) as usize);
    return v_r_2289_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(
    mut v_x_2290_: *mut leanh::LeanObject,
    mut v_x_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u64 = 0;
    let mut v___x_2300_: u64 = 0;
    let mut v___x_2301_: u64 = 0;
    let mut v_fold_2302_: u64 = 0;
    let mut v___x_2303_: u64 = 0;
    let mut v___x_2304_: u64 = 0;
    let mut v___x_2305_: u64 = 0;
    let mut v___x_2306_: usize = 0;
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut v___x_2309_: usize = 0;
    let mut v___x_2310_: usize = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2291_) == 0 {
                    return v_x_2290_;
                } else {
                    v_key_2292_ = leanh::lean_ctor_get(v_x_2291_, 0);
                    v_value_2293_ = leanh::lean_ctor_get(v_x_2291_, 1);
                    v_tail_2294_ = leanh::lean_ctor_get(v_x_2291_, 2);
                    v_isSharedCheck_2317_ = (!leanh::lean_is_exclusive(v_x_2291_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2296_ = v_x_2291_;
                        v_isShared_2297_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2294_);
                        leanh::lean_inc(v_value_2293_);
                        leanh::lean_inc(v_key_2292_);
                        leanh::lean_dec(v_x_2291_);
                        v___x_2296_ = leanh::lean_box(0);
                        v_isShared_2297_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2298_ = lean_array_get_size(v_x_2290_);
                v___x_2299_ = l_Lean_instHashableMVarId_hash(v_key_2292_);
                v___x_2300_ = 32u64;
                v___x_2301_ = lean_uint64_shift_right(v___x_2299_, v___x_2300_);
                v_fold_2302_ = lean_uint64_xor(v___x_2299_, v___x_2301_);
                v___x_2303_ = 16u64;
                v___x_2304_ = lean_uint64_shift_right(v_fold_2302_, v___x_2303_);
                v___x_2305_ = lean_uint64_xor(v_fold_2302_, v___x_2304_);
                v___x_2306_ = lean_uint64_to_usize(v___x_2305_);
                v___x_2307_ = lean_usize_of_nat(v___x_2298_);
                v___x_2308_ = 1usize;
                v___x_2309_ = lean_usize_sub(v___x_2307_, v___x_2308_);
                v___x_2310_ = lean_usize_land(v___x_2306_, v___x_2309_);
                v___x_2311_ = lean_array_uget_borrowed(v_x_2290_, v___x_2310_);
                leanh::lean_inc(v___x_2311_);
                if v_isShared_2297_ == 0 {
                    leanh::lean_ctor_set(v___x_2296_, 2, v___x_2311_);
                    v___x_2313_ = v___x_2296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2316_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_key_2292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_value_2293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 2, v___x_2311_);
                    v___x_2313_ = v_reuseFailAlloc_2316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2314_ = lean_array_uset(v_x_2290_, v___x_2310_, v___x_2313_);
                v_x_2290_ = v___x_2314_;
                v_x_2291_ = v_tail_2294_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(
    mut v_i_2318_: *mut leanh::LeanObject,
    mut v_source_2319_: *mut leanh::LeanObject,
    mut v_target_2320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v_es_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2321_ = lean_array_get_size(v_source_2319_);
                v___x_2322_ = lean_nat_dec_lt(v_i_2318_, v___x_2321_);
                if v___x_2322_ == 0 {
                    leanh::lean_dec_ref(v_source_2319_);
                    leanh::lean_dec(v_i_2318_);
                    return v_target_2320_;
                } else {
                    v_es_2323_ = lean_array_fget(v_source_2319_, v_i_2318_);
                    v___x_2324_ = leanh::lean_box(0);
                    v_source_2325_ = lean_array_fset(v_source_2319_, v_i_2318_, v___x_2324_);
                    v_target_2326_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_2320_, v_es_2323_);
                    v___x_2327_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2328_ = lean_nat_add(v_i_2318_, v___x_2327_);
                    leanh::lean_dec(v_i_2318_);
                    v_i_2318_ = v___x_2328_;
                    v_source_2319_ = v_source_2325_;
                    v_target_2320_ = v_target_2326_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(
    mut v_data_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ = lean_array_get_size(v_data_2330_);
    v___x_2332_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2333_ = lean_nat_mul(v___x_2331_, v___x_2332_);
    v___x_2334_ = leanh::lean_unsigned_to_nat(0);
    v___x_2335_ = leanh::lean_box(0);
    v___x_2336_ = lean_mk_array(v_nbuckets_2333_, v___x_2335_);
    v___x_2337_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_2334_, v_data_2330_, v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(
    mut v_m_2338_: *mut leanh::LeanObject,
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_b_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u64 = 0;
    let mut v___x_2345_: u64 = 0;
    let mut v___x_2346_: u64 = 0;
    let mut v_fold_2347_: u64 = 0;
    let mut v___x_2348_: u64 = 0;
    let mut v___x_2349_: u64 = 0;
    let mut v___x_2350_: u64 = 0;
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    let mut v___x_2355_: usize = 0;
    let mut v_bkt_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: u8 = 0;
    let mut v_val_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_unused_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2341_ = leanh::lean_ctor_get(v_m_2338_, 0);
                v_buckets_2342_ = leanh::lean_ctor_get(v_m_2338_, 1);
                v___x_2343_ = lean_array_get_size(v_buckets_2342_);
                v___x_2344_ = l_Lean_instHashableMVarId_hash(v_a_2339_);
                v___x_2345_ = 32u64;
                v___x_2346_ = lean_uint64_shift_right(v___x_2344_, v___x_2345_);
                v_fold_2347_ = lean_uint64_xor(v___x_2344_, v___x_2346_);
                v___x_2348_ = 16u64;
                v___x_2349_ = lean_uint64_shift_right(v_fold_2347_, v___x_2348_);
                v___x_2350_ = lean_uint64_xor(v_fold_2347_, v___x_2349_);
                v___x_2351_ = lean_uint64_to_usize(v___x_2350_);
                v___x_2352_ = lean_usize_of_nat(v___x_2343_);
                v___x_2353_ = 1usize;
                v___x_2354_ = lean_usize_sub(v___x_2352_, v___x_2353_);
                v___x_2355_ = lean_usize_land(v___x_2351_, v___x_2354_);
                v_bkt_2356_ = lean_array_uget_borrowed(v_buckets_2342_, v___x_2355_);
                v___x_2357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_2339_, v_bkt_2356_);
                if v___x_2357_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2342_);
                    leanh::lean_inc(v_size_2341_);
                    v_isSharedCheck_2378_ = (!leanh::lean_is_exclusive(v_m_2338_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v_unused_2379_ = leanh::lean_ctor_get(v_m_2338_, 1);
                        leanh::lean_dec(v_unused_2379_);
                        v_unused_2380_ = leanh::lean_ctor_get(v_m_2338_, 0);
                        leanh::lean_dec(v_unused_2380_);
                        v___x_2359_ = v_m_2338_;
                        v_isShared_2360_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2338_);
                        v___x_2359_ = leanh::lean_box(0);
                        v_isShared_2360_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2340_);
                    leanh::lean_dec(v_a_2339_);
                    return v_m_2338_;
                }
            }
            1 => {
                v___x_2361_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2362_ = lean_nat_add(v_size_2341_, v___x_2361_);
                leanh::lean_dec(v_size_2341_);
                leanh::lean_inc(v_bkt_2356_);
                v___x_2363_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2363_, 0, v_a_2339_);
                leanh::lean_ctor_set(v___x_2363_, 1, v_b_2340_);
                leanh::lean_ctor_set(v___x_2363_, 2, v_bkt_2356_);
                v_buckets_x27_2364_ = lean_array_uset(v_buckets_2342_, v___x_2355_, v___x_2363_);
                v___x_2365_ = leanh::lean_unsigned_to_nat(4);
                v___x_2366_ = lean_nat_mul(v_size_x27_2362_, v___x_2365_);
                v___x_2367_ = leanh::lean_unsigned_to_nat(3);
                v___x_2368_ = lean_nat_div(v___x_2366_, v___x_2367_);
                leanh::lean_dec(v___x_2366_);
                v___x_2369_ = lean_array_get_size(v_buckets_x27_2364_);
                v___x_2370_ = lean_nat_dec_le(v___x_2368_, v___x_2369_);
                leanh::lean_dec(v___x_2368_);
                if v___x_2370_ == 0 {
                    v_val_2371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_2364_);
                    if v_isShared_2360_ == 0 {
                        leanh::lean_ctor_set(v___x_2359_, 1, v_val_2371_);
                        leanh::lean_ctor_set(v___x_2359_, 0, v_size_x27_2362_);
                        v___x_2373_ = v___x_2359_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2374_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_size_x27_2362_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_val_2371_);
                        v___x_2373_ = v_reuseFailAlloc_2374_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2360_ == 0 {
                        leanh::lean_ctor_set(v___x_2359_, 1, v_buckets_x27_2364_);
                        leanh::lean_ctor_set(v___x_2359_, 0, v_size_x27_2362_);
                        v___x_2376_ = v___x_2359_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_size_x27_2362_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_buckets_x27_2364_);
                        v___x_2376_ = v_reuseFailAlloc_2377_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2373_;
            }
            3 => {
                return v___x_2376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(
    mut v_includeDelayed_2381_: u8,
    mut v_as_2382_: *mut leanh::LeanObject,
    mut v_sz_2383_: usize,
    mut v_i_2384_: usize,
    mut v_b_2385_: *mut leanh::LeanObject,
    mut v___y_2386_: *mut leanh::LeanObject,
    mut v___y_2387_: *mut leanh::LeanObject,
    mut v___y_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: usize = 0;
    let mut v___x_2395_: usize = 0;
    let mut v___x_2397_: u8 = 0;
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: u8 = 0;
    let mut v_a_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v_a_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2397_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
                if v___x_2397_ == 0 {
                    v___x_2398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2398_, 0, v_b_2385_);
                    return v___x_2398_;
                } else {
                    v_a_2399_ = lean_array_uget_borrowed(v_as_2382_, v_i_2384_);
                    if v_includeDelayed_2381_ == 0 {
                        v___x_2403_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_2399_, v___y_2388_);
                        if leanh::lean_obj_tag(v___x_2403_) == 0 {
                            v_a_2404_ = leanh::lean_ctor_get(v___x_2403_, 0);
                            leanh::lean_inc(v_a_2404_);
                            leanh::lean_dec_ref_known(v___x_2403_, 1);
                            v___x_2405_ = (leanh::lean_unbox(v_a_2404_) as u8);
                            leanh::lean_dec(v_a_2404_);
                            if v___x_2405_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v_a_2393_ = v_b_2385_;
                                state = 1;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_2403_) == 0 {
                                v_a_2406_ = leanh::lean_ctor_get(v___x_2403_, 0);
                                leanh::lean_inc(v_a_2406_);
                                leanh::lean_dec_ref_known(v___x_2403_, 1);
                                v___x_2407_ = (leanh::lean_unbox(v_a_2406_) as u8);
                                leanh::lean_dec(v_a_2406_);
                                if v___x_2407_ == 0 {
                                    v_a_2393_ = v_b_2385_;
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_2385_);
                                v_a_2408_ = leanh::lean_ctor_get(v___x_2403_, 0);
                                v_isSharedCheck_2415_ =
                                    (!leanh::lean_is_exclusive(v___x_2403_)) as u8;
                                if v_isSharedCheck_2415_ == 0 {
                                    v___x_2410_ = v___x_2403_;
                                    v_isShared_2411_ = v_isSharedCheck_2415_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2408_);
                                    leanh::lean_dec(v___x_2403_);
                                    v___x_2410_ = leanh::lean_box(0);
                                    v_isShared_2411_ = v_isSharedCheck_2415_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2394_ = 1usize;
                v___x_2395_ = lean_usize_add(v_i_2384_, v___x_2394_);
                v_i_2384_ = v___x_2395_;
                v_b_2385_ = v_a_2393_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2401_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_2399_);
                v___x_2402_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_b_2385_, v_a_2399_, v___x_2401_);
                v_a_2393_ = v___x_2402_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2411_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2___boxed(
    mut v_includeDelayed_2416_: *mut leanh::LeanObject,
    mut v_as_2417_: *mut leanh::LeanObject,
    mut v_sz_2418_: *mut leanh::LeanObject,
    mut v_i_2419_: *mut leanh::LeanObject,
    mut v_b_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
    mut v___y_2425_: *mut leanh::LeanObject,
    mut v___y_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_2427_: u8 = 0;
    let mut v_sz_boxed_2428_: usize = 0;
    let mut v_i_boxed_2429_: usize = 0;
    let mut v_res_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_2427_ = (leanh::lean_unbox(v_includeDelayed_2416_) as u8);
    v_sz_boxed_2428_ = leanh::lean_unbox_usize(v_sz_2418_);
    leanh::lean_dec(v_sz_2418_);
    v_i_boxed_2429_ = leanh::lean_unbox_usize(v_i_2419_);
    leanh::lean_dec(v_i_2419_);
    v_res_2430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_boxed_2427_, v_as_2417_, v_sz_boxed_2428_, v_i_boxed_2429_, v_b_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
    leanh::lean_dec(v___y_2425_);
    leanh::lean_dec_ref(v___y_2424_);
    leanh::lean_dec(v___y_2423_);
    leanh::lean_dec_ref(v___y_2422_);
    leanh::lean_dec(v___y_2421_);
    leanh::lean_dec_ref(v_as_2417_);
    return v_res_2430_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ = l_Lean_maxRecDepthErrorMessage;
    v___x_2437_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2437_, 0, v___x_2436_);
    return v___x_2437_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3);
    v___x_2439_ = l_Lean_MessageData_ofFormat(v___x_2438_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2440_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4);
    v___x_2441_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2;
    v___x_2442_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2442_, 0, v___x_2441_);
    leanh::lean_ctor_set(v___x_2442_, 1, v___x_2440_);
    return v___x_2442_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(
    mut v_ref_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5);
    v___x_2446_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2446_, 0, v_ref_2443_);
    leanh::lean_ctor_set(v___x_2446_, 1, v___x_2445_);
    v___x_2447_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2447_, 0, v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(
    mut v_ref_2448_: *mut leanh::LeanObject,
    mut v___y_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ =
        l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(
            v_ref_2448_,
        );
    return v_res_2450_;
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(
    mut v_mvarId_2451_: *mut leanh::LeanObject,
    mut v___y_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    v___x_2454_ = lean_st_ref_get(v___y_2452_);
    v_mctx_2455_ = leanh::lean_ctor_get(v___x_2454_, 0);
    leanh::lean_inc_ref(v_mctx_2455_);
    leanh::lean_dec(v___x_2454_);
    v_eAssignment_2456_ = leanh::lean_ctor_get(v_mctx_2455_, 8);
    leanh::lean_inc_ref(v_eAssignment_2456_);
    v_dAssignment_2457_ = leanh::lean_ctor_get(v_mctx_2455_, 9);
    leanh::lean_inc_ref(v_dAssignment_2457_);
    leanh::lean_dec_ref(v_mctx_2455_);
    v___x_2458_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_2456_, v_mvarId_2451_);
    leanh::lean_dec_ref(v_eAssignment_2456_);
    if v___x_2458_ == 0 {
        let mut v___x_2459_: u8 = 0;
        let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2459_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_2457_, v_mvarId_2451_);
        leanh::lean_dec_ref(v_dAssignment_2457_);
        v___x_2460_ = leanh::lean_box((v___x_2459_) as usize);
        v___x_2461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2461_, 0, v___x_2460_);
        return v___x_2461_;
    } else {
        let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_dAssignment_2457_);
        v___x_2462_ = leanh::lean_box((v___x_2458_) as usize);
        v___x_2463_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2463_, 0, v___x_2462_);
        return v___x_2463_;
    }
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(
    mut v_mvarId_2464_: *mut leanh::LeanObject,
    mut v___y_2465_: *mut leanh::LeanObject,
    mut v___y_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2467_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_2464_, v___y_2465_);
    leanh::lean_dec(v___y_2465_);
    leanh::lean_dec(v_mvarId_2464_);
    return v_res_2467_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(
    mut v_mvarId_2468_: *mut leanh::LeanObject,
    mut v___y_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = lean_st_ref_get(v___y_2469_);
    v_mctx_2472_ = leanh::lean_ctor_get(v___x_2471_, 0);
    leanh::lean_inc_ref(v_mctx_2472_);
    leanh::lean_dec(v___x_2471_);
    v___x_2473_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_2472_, v_mvarId_2468_);
    leanh::lean_dec_ref(v_mctx_2472_);
    v___x_2474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    return v___x_2474_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(
    mut v_mvarId_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_2475_, v___y_2476_);
    leanh::lean_dec(v___y_2476_);
    leanh::lean_dec(v_mvarId_2475_);
    return v_res_2478_;
}
pub unsafe fn _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = leanh::lean_box(0);
    v___x_2480_ = leanh::lean_unsigned_to_nat(16);
    v___x_2481_ = lean_mk_array(v___x_2480_, v___x_2479_);
    return v___x_2481_;
}
pub unsafe fn _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0),
        core::ptr::addr_of_mut!(l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once),
        _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0,
    );
    v___x_2483_ = leanh::lean_unsigned_to_nat(0);
    v___x_2484_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    leanh::lean_ctor_set(v___x_2484_, 1, v___x_2482_);
    return v___x_2484_;
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__addMVars(
    mut v_e_2485_: *mut leanh::LeanObject,
    mut v_includeDelayed_2486_: u8,
    mut v_a_2487_: *mut leanh::LeanObject,
    mut v_a_2488_: *mut leanh::LeanObject,
    mut v_a_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
    mut v_a_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2499_: usize = 0;
    let mut v___x_2500_: usize = 0;
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_a_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_a_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2493_ =
                    l_Lean_Meta_getMVars(v_e_2485_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                if leanh::lean_obj_tag(v___x_2493_) == 0 {
                    v_a_2494_ = leanh::lean_ctor_get(v___x_2493_, 0);
                    leanh::lean_inc(v_a_2494_);
                    leanh::lean_dec_ref_known(v___x_2493_, 1);
                    v___x_2495_ = lean_st_ref_get(v_a_2487_);
                    v___x_2496_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2497_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once
                        ),
                        _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1,
                    );
                    v___x_2498_ = lean_st_ref_set(v_a_2487_, v___x_2497_);
                    v_sz_2499_ = lean_array_size(v_a_2494_);
                    v___x_2500_ = 0usize;
                    v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_2486_, v_a_2494_, v_sz_2499_, v___x_2500_, v___x_2495_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                    if leanh::lean_obj_tag(v___x_2501_) == 0 {
                        v_a_2502_ = leanh::lean_ctor_get(v___x_2501_, 0);
                        v_isSharedCheck_2521_ =
                            (!leanh::lean_is_exclusive(v___x_2501_)) as u8;
                        if v_isSharedCheck_2521_ == 0 {
                            v___x_2504_ = v___x_2501_;
                            v_isShared_2505_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2502_);
                            leanh::lean_dec(v___x_2501_);
                            v___x_2504_ = leanh::lean_box(0);
                            v_isShared_2505_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2494_);
                        v_a_2522_ = leanh::lean_ctor_get(v___x_2501_, 0);
                        v_isSharedCheck_2529_ =
                            (!leanh::lean_is_exclusive(v___x_2501_)) as u8;
                        if v_isSharedCheck_2529_ == 0 {
                            v___x_2524_ = v___x_2501_;
                            v_isShared_2525_ = v_isSharedCheck_2529_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2522_);
                            leanh::lean_dec(v___x_2501_);
                            v___x_2524_ = leanh::lean_box(0);
                            v_isShared_2525_ = v_isSharedCheck_2529_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_2530_ = leanh::lean_ctor_get(v___x_2493_, 0);
                    v_isSharedCheck_2537_ = (!leanh::lean_is_exclusive(v___x_2493_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v___x_2532_ = v___x_2493_;
                        v_isShared_2533_ = v_isSharedCheck_2537_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2530_);
                        leanh::lean_dec(v___x_2493_);
                        v___x_2532_ = leanh::lean_box(0);
                        v_isShared_2533_ = v_isSharedCheck_2537_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2506_ = lean_st_ref_set(v_a_2487_, v_a_2502_);
                v___x_2507_ = lean_array_get_size(v_a_2494_);
                v___x_2508_ = leanh::lean_box(0);
                v___x_2509_ = lean_nat_dec_lt(v___x_2496_, v___x_2507_);
                if v___x_2509_ == 0 {
                    leanh::lean_dec(v_a_2494_);
                    if v_isShared_2505_ == 0 {
                        leanh::lean_ctor_set(v___x_2504_, 0, v___x_2508_);
                        v___x_2511_ = v___x_2504_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2508_);
                        v___x_2511_ = v_reuseFailAlloc_2512_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2513_ = lean_nat_dec_le(v___x_2507_, v___x_2507_);
                    if v___x_2513_ == 0 {
                        if v___x_2509_ == 0 {
                            leanh::lean_dec(v_a_2494_);
                            if v_isShared_2505_ == 0 {
                                leanh::lean_ctor_set(v___x_2504_, 0, v___x_2508_);
                                v___x_2515_ = v___x_2504_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2516_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2508_);
                                v___x_2515_ = v_reuseFailAlloc_2516_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2504_);
                            v___x_2517_ = lean_usize_of_nat(v___x_2507_);
                            v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_2494_, v___x_2500_, v___x_2517_, v___x_2508_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                            leanh::lean_dec(v_a_2494_);
                            return v___x_2518_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2504_);
                        v___x_2519_ = lean_usize_of_nat(v___x_2507_);
                        v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_2494_, v___x_2500_, v___x_2519_, v___x_2508_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                        leanh::lean_dec(v_a_2494_);
                        return v___x_2520_;
                    }
                }
            }
            2 => {
                return v___x_2511_;
            }
            3 => {
                return v___x_2515_;
            }
            4 => {
                if v_isShared_2525_ == 0 {
                    v___x_2527_ = v___x_2524_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2527_;
            }
            6 => {
                if v_isShared_2533_ == 0 {
                    v___x_2535_ = v___x_2532_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
                    v___x_2535_ = v_reuseFailAlloc_2536_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(
    mut v_init_2538_: *mut leanh::LeanObject,
    mut v_includeDelayed_2539_: u8,
    mut v_as_2540_: *mut leanh::LeanObject,
    mut v_sz_2541_: usize,
    mut v_i_2542_: usize,
    mut v_b_2543_: *mut leanh::LeanObject,
    mut v___y_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
    mut v___y_2546_: *mut leanh::LeanObject,
    mut v___y_2547_: *mut leanh::LeanObject,
    mut v___y_2548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v_a_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: usize = 0;
    let mut v___x_2574_: usize = 0;
    let mut v_reuseFailAlloc_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_a_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_unused_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_usize_dec_lt(v_i_2542_, v_sz_2541_);
                if v___x_2550_ == 0 {
                    v___x_2551_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2551_, 0, v_b_2543_);
                    return v___x_2551_;
                } else {
                    v_snd_2552_ = leanh::lean_ctor_get(v_b_2543_, 1);
                    v_isSharedCheck_2586_ = (!leanh::lean_is_exclusive(v_b_2543_)) as u8;
                    if v_isSharedCheck_2586_ == 0 {
                        v_unused_2587_ = leanh::lean_ctor_get(v_b_2543_, 0);
                        leanh::lean_dec(v_unused_2587_);
                        v___x_2554_ = v_b_2543_;
                        v_isShared_2555_ = v_isSharedCheck_2586_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2552_);
                        leanh::lean_dec(v_b_2543_);
                        v___x_2554_ = leanh::lean_box(0);
                        v_isShared_2555_ = v_isSharedCheck_2586_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2556_ = lean_array_uget_borrowed(v_as_2540_, v_i_2542_);
                leanh::lean_inc(v_snd_2552_);
                v___x_2557_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_2538_, v_includeDelayed_2539_, v_a_2556_, v_snd_2552_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
                if leanh::lean_obj_tag(v___x_2557_) == 0 {
                    v_a_2558_ = leanh::lean_ctor_get(v___x_2557_, 0);
                    v_isSharedCheck_2577_ = (!leanh::lean_is_exclusive(v___x_2557_)) as u8;
                    if v_isSharedCheck_2577_ == 0 {
                        v___x_2560_ = v___x_2557_;
                        v_isShared_2561_ = v_isSharedCheck_2577_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2558_);
                        leanh::lean_dec(v___x_2557_);
                        v___x_2560_ = leanh::lean_box(0);
                        v_isShared_2561_ = v_isSharedCheck_2577_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2554_);
                    leanh::lean_dec(v_snd_2552_);
                    v_a_2578_ = leanh::lean_ctor_get(v___x_2557_, 0);
                    v_isSharedCheck_2585_ = (!leanh::lean_is_exclusive(v___x_2557_)) as u8;
                    if v_isSharedCheck_2585_ == 0 {
                        v___x_2580_ = v___x_2557_;
                        v_isShared_2581_ = v_isSharedCheck_2585_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2578_);
                        leanh::lean_dec(v___x_2557_);
                        v___x_2580_ = leanh::lean_box(0);
                        v_isShared_2581_ = v_isSharedCheck_2585_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2558_) == 0 {
                    v___x_2562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2562_, 0, v_a_2558_);
                    if v_isShared_2555_ == 0 {
                        leanh::lean_ctor_set(v___x_2554_, 0, v___x_2562_);
                        v___x_2564_ = v___x_2554_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2568_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2562_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_snd_2552_);
                        v___x_2564_ = v_reuseFailAlloc_2568_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2560_);
                    leanh::lean_dec(v_snd_2552_);
                    v_a_2569_ = leanh::lean_ctor_get(v_a_2558_, 0);
                    leanh::lean_inc(v_a_2569_);
                    leanh::lean_dec_ref_known(v_a_2558_, 1);
                    v___x_2570_ = leanh::lean_box(0);
                    if v_isShared_2555_ == 0 {
                        leanh::lean_ctor_set(v___x_2554_, 1, v_a_2569_);
                        leanh::lean_ctor_set(v___x_2554_, 0, v___x_2570_);
                        v___x_2572_ = v___x_2554_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2576_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2570_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_a_2569_);
                        v___x_2572_ = v_reuseFailAlloc_2576_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2561_ == 0 {
                    leanh::lean_ctor_set(v___x_2560_, 0, v___x_2564_);
                    v___x_2566_ = v___x_2560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2566_;
            }
            5 => {
                v___x_2573_ = 1usize;
                v___x_2574_ = lean_usize_add(v_i_2542_, v___x_2573_);
                v_i_2542_ = v___x_2574_;
                v_b_2543_ = v___x_2572_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2581_ == 0 {
                    v___x_2583_ = v___x_2580_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(
    mut v_includeDelayed_2588_: u8,
    mut v_as_2589_: *mut leanh::LeanObject,
    mut v_sz_2590_: usize,
    mut v_i_2591_: usize,
    mut v_b_2592_: *mut leanh::LeanObject,
    mut v___y_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
    mut v___y_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v_reuseFailAlloc_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2626_: u8 = 0;
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_a_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v_unused_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2599_ = lean_usize_dec_lt(v_i_2591_, v_sz_2590_);
                if v___x_2599_ == 0 {
                    v___x_2600_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2600_, 0, v_b_2592_);
                    return v___x_2600_;
                } else {
                    v_snd_2601_ = leanh::lean_ctor_get(v_b_2592_, 1);
                    v_isSharedCheck_2639_ = (!leanh::lean_is_exclusive(v_b_2592_)) as u8;
                    if v_isSharedCheck_2639_ == 0 {
                        v_unused_2640_ = leanh::lean_ctor_get(v_b_2592_, 0);
                        leanh::lean_dec(v_unused_2640_);
                        v___x_2603_ = v_b_2592_;
                        v_isShared_2604_ = v_isSharedCheck_2639_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2601_);
                        leanh::lean_dec(v_b_2592_);
                        v___x_2603_ = leanh::lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2605_ = leanh::lean_box(0);
                v_a_2614_ = lean_array_uget_borrowed(v_as_2589_, v_i_2591_);
                if leanh::lean_obj_tag(v_a_2614_) == 0 {
                    v_a_2607_ = v_snd_2601_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2601_);
                    v_val_2615_ = leanh::lean_ctor_get(v_a_2614_, 0);
                    v___x_2616_ = l_Lean_LocalDecl_type(v_val_2615_);
                    v___x_2617_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                        v___x_2616_,
                        v_includeDelayed_2588_,
                        v___y_2593_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if leanh::lean_obj_tag(v___x_2617_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2617_, 1);
                        v___x_2618_ = leanh::lean_box(0);
                        v___x_2619_ = 0;
                        v___x_2620_ = l_Lean_LocalDecl_value_x3f(v_val_2615_, v___x_2619_);
                        if leanh::lean_obj_tag(v___x_2620_) == 1 {
                            v_val_2621_ = leanh::lean_ctor_get(v___x_2620_, 0);
                            leanh::lean_inc(v_val_2621_);
                            leanh::lean_dec_ref_known(v___x_2620_, 1);
                            v___x_2622_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2621_,
                                v_includeDelayed_2588_,
                                v___y_2593_,
                                v___y_2594_,
                                v___y_2595_,
                                v___y_2596_,
                                v___y_2597_,
                            );
                            if leanh::lean_obj_tag(v___x_2622_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2622_, 1);
                                v_a_2607_ = v___x_2618_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2603_);
                                v_a_2623_ = leanh::lean_ctor_get(v___x_2622_, 0);
                                v_isSharedCheck_2630_ =
                                    (!leanh::lean_is_exclusive(v___x_2622_)) as u8;
                                if v_isSharedCheck_2630_ == 0 {
                                    v___x_2625_ = v___x_2622_;
                                    v_isShared_2626_ = v_isSharedCheck_2630_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2623_);
                                    leanh::lean_dec(v___x_2622_);
                                    v___x_2625_ = leanh::lean_box(0);
                                    v_isShared_2626_ = v_isSharedCheck_2630_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2620_);
                            v_a_2607_ = v___x_2618_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2603_);
                        v_a_2631_ = leanh::lean_ctor_get(v___x_2617_, 0);
                        v_isSharedCheck_2638_ =
                            (!leanh::lean_is_exclusive(v___x_2617_)) as u8;
                        if v_isSharedCheck_2638_ == 0 {
                            v___x_2633_ = v___x_2617_;
                            v_isShared_2634_ = v_isSharedCheck_2638_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2631_);
                            leanh::lean_dec(v___x_2617_);
                            v___x_2633_ = leanh::lean_box(0);
                            v_isShared_2634_ = v_isSharedCheck_2638_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2604_ == 0 {
                    leanh::lean_ctor_set(v___x_2603_, 1, v_a_2607_);
                    leanh::lean_ctor_set(v___x_2603_, 0, v___x_2605_);
                    v___x_2609_ = v___x_2603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_a_2607_);
                    v___x_2609_ = v_reuseFailAlloc_2613_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2610_ = 1usize;
                v___x_2611_ = lean_usize_add(v_i_2591_, v___x_2610_);
                v_i_2591_ = v___x_2611_;
                v_b_2592_ = v___x_2609_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2626_ == 0 {
                    v___x_2628_ = v___x_2625_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
                    v___x_2628_ = v_reuseFailAlloc_2629_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2628_;
            }
            6 => {
                if v_isShared_2634_ == 0 {
                    v___x_2636_ = v___x_2633_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2637_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
                    v___x_2636_ = v_reuseFailAlloc_2637_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(
    mut v_includeDelayed_2641_: u8,
    mut v_as_2642_: *mut leanh::LeanObject,
    mut v_sz_2643_: usize,
    mut v_i_2644_: usize,
    mut v_b_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2652_: u8 = 0;
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: usize = 0;
    let mut v___x_2664_: usize = 0;
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2691_: u8 = 0;
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_unused_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_usize_dec_lt(v_i_2644_, v_sz_2643_);
                if v___x_2652_ == 0 {
                    v___x_2653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2653_, 0, v_b_2645_);
                    return v___x_2653_;
                } else {
                    v_snd_2654_ = leanh::lean_ctor_get(v_b_2645_, 1);
                    v_isSharedCheck_2692_ = (!leanh::lean_is_exclusive(v_b_2645_)) as u8;
                    if v_isSharedCheck_2692_ == 0 {
                        v_unused_2693_ = leanh::lean_ctor_get(v_b_2645_, 0);
                        leanh::lean_dec(v_unused_2693_);
                        v___x_2656_ = v_b_2645_;
                        v_isShared_2657_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2654_);
                        leanh::lean_dec(v_b_2645_);
                        v___x_2656_ = leanh::lean_box(0);
                        v_isShared_2657_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2658_ = leanh::lean_box(0);
                v_a_2667_ = lean_array_uget_borrowed(v_as_2642_, v_i_2644_);
                if leanh::lean_obj_tag(v_a_2667_) == 0 {
                    v_a_2660_ = v_snd_2654_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2654_);
                    v_val_2668_ = leanh::lean_ctor_get(v_a_2667_, 0);
                    v___x_2669_ = l_Lean_LocalDecl_type(v_val_2668_);
                    v___x_2670_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                        v___x_2669_,
                        v_includeDelayed_2641_,
                        v___y_2646_,
                        v___y_2647_,
                        v___y_2648_,
                        v___y_2649_,
                        v___y_2650_,
                    );
                    if leanh::lean_obj_tag(v___x_2670_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2670_, 1);
                        v___x_2671_ = leanh::lean_box(0);
                        v___x_2672_ = 0;
                        v___x_2673_ = l_Lean_LocalDecl_value_x3f(v_val_2668_, v___x_2672_);
                        if leanh::lean_obj_tag(v___x_2673_) == 1 {
                            v_val_2674_ = leanh::lean_ctor_get(v___x_2673_, 0);
                            leanh::lean_inc(v_val_2674_);
                            leanh::lean_dec_ref_known(v___x_2673_, 1);
                            v___x_2675_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2674_,
                                v_includeDelayed_2641_,
                                v___y_2646_,
                                v___y_2647_,
                                v___y_2648_,
                                v___y_2649_,
                                v___y_2650_,
                            );
                            if leanh::lean_obj_tag(v___x_2675_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2675_, 1);
                                v_a_2660_ = v___x_2671_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2656_);
                                v_a_2676_ = leanh::lean_ctor_get(v___x_2675_, 0);
                                v_isSharedCheck_2683_ =
                                    (!leanh::lean_is_exclusive(v___x_2675_)) as u8;
                                if v_isSharedCheck_2683_ == 0 {
                                    v___x_2678_ = v___x_2675_;
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2676_);
                                    leanh::lean_dec(v___x_2675_);
                                    v___x_2678_ = leanh::lean_box(0);
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2673_);
                            v_a_2660_ = v___x_2671_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2656_);
                        v_a_2684_ = leanh::lean_ctor_get(v___x_2670_, 0);
                        v_isSharedCheck_2691_ =
                            (!leanh::lean_is_exclusive(v___x_2670_)) as u8;
                        if v_isSharedCheck_2691_ == 0 {
                            v___x_2686_ = v___x_2670_;
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2684_);
                            leanh::lean_dec(v___x_2670_);
                            v___x_2686_ = leanh::lean_box(0);
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2657_ == 0 {
                    leanh::lean_ctor_set(v___x_2656_, 1, v_a_2660_);
                    leanh::lean_ctor_set(v___x_2656_, 0, v___x_2658_);
                    v___x_2662_ = v___x_2656_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_a_2660_);
                    v___x_2662_ = v_reuseFailAlloc_2666_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2663_ = 1usize;
                v___x_2664_ = lean_usize_add(v_i_2644_, v___x_2663_);
                v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_2641_, v_as_2642_, v_sz_2643_, v___x_2664_, v___x_2662_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
                return v___x_2665_;
            }
            4 => {
                if v_isShared_2679_ == 0 {
                    v___x_2681_ = v___x_2678_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
                    v___x_2681_ = v_reuseFailAlloc_2682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2681_;
            }
            6 => {
                if v_isShared_2687_ == 0 {
                    v___x_2689_ = v___x_2686_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
                    v___x_2689_ = v_reuseFailAlloc_2690_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(
    mut v_init_2694_: *mut leanh::LeanObject,
    mut v_includeDelayed_2695_: u8,
    mut v_n_2696_: *mut leanh::LeanObject,
    mut v_b_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
    mut v___y_2700_: *mut leanh::LeanObject,
    mut v___y_2701_: *mut leanh::LeanObject,
    mut v___y_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2707_: usize = 0;
    let mut v___x_2708_: usize = 0;
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v_fst_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_a_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2732_: u8 = 0;
    let mut v_vs_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2736_: usize = 0;
    let mut v___x_2737_: usize = 0;
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v_fst_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2753_: u8 = 0;
    let mut v_a_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2757_: u8 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_2696_) == 0 {
                    v_cs_2704_ = leanh::lean_ctor_get(v_n_2696_, 0);
                    v___x_2705_ = leanh::lean_box(0);
                    v___x_2706_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2706_, 0, v___x_2705_);
                    leanh::lean_ctor_set(v___x_2706_, 1, v_b_2697_);
                    v_sz_2707_ = lean_array_size(v_cs_2704_);
                    v___x_2708_ = 0usize;
                    v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_2694_, v_includeDelayed_2695_, v_cs_2704_, v_sz_2707_, v___x_2708_, v___x_2706_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
                    if leanh::lean_obj_tag(v___x_2709_) == 0 {
                        v_a_2710_ = leanh::lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_2724_ =
                            (!leanh::lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_2724_ == 0 {
                            v___x_2712_ = v___x_2709_;
                            v_isShared_2713_ = v_isSharedCheck_2724_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2710_);
                            leanh::lean_dec(v___x_2709_);
                            v___x_2712_ = leanh::lean_box(0);
                            v_isShared_2713_ = v_isSharedCheck_2724_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2725_ = leanh::lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_2732_ =
                            (!leanh::lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_2732_ == 0 {
                            v___x_2727_ = v___x_2709_;
                            v_isShared_2728_ = v_isSharedCheck_2732_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2725_);
                            leanh::lean_dec(v___x_2709_);
                            v___x_2727_ = leanh::lean_box(0);
                            v_isShared_2728_ = v_isSharedCheck_2732_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2733_ = leanh::lean_ctor_get(v_n_2696_, 0);
                    v___x_2734_ = leanh::lean_box(0);
                    v___x_2735_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2735_, 0, v___x_2734_);
                    leanh::lean_ctor_set(v___x_2735_, 1, v_b_2697_);
                    v_sz_2736_ = lean_array_size(v_vs_2733_);
                    v___x_2737_ = 0usize;
                    v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_2695_, v_vs_2733_, v_sz_2736_, v___x_2737_, v___x_2735_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
                    if leanh::lean_obj_tag(v___x_2738_) == 0 {
                        v_a_2739_ = leanh::lean_ctor_get(v___x_2738_, 0);
                        v_isSharedCheck_2753_ =
                            (!leanh::lean_is_exclusive(v___x_2738_)) as u8;
                        if v_isSharedCheck_2753_ == 0 {
                            v___x_2741_ = v___x_2738_;
                            v_isShared_2742_ = v_isSharedCheck_2753_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2739_);
                            leanh::lean_dec(v___x_2738_);
                            v___x_2741_ = leanh::lean_box(0);
                            v_isShared_2742_ = v_isSharedCheck_2753_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2754_ = leanh::lean_ctor_get(v___x_2738_, 0);
                        v_isSharedCheck_2761_ =
                            (!leanh::lean_is_exclusive(v___x_2738_)) as u8;
                        if v_isSharedCheck_2761_ == 0 {
                            v___x_2756_ = v___x_2738_;
                            v_isShared_2757_ = v_isSharedCheck_2761_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2754_);
                            leanh::lean_dec(v___x_2738_);
                            v___x_2756_ = leanh::lean_box(0);
                            v_isShared_2757_ = v_isSharedCheck_2761_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2714_ = leanh::lean_ctor_get(v_a_2710_, 0);
                if leanh::lean_obj_tag(v_fst_2714_) == 0 {
                    v_snd_2715_ = leanh::lean_ctor_get(v_a_2710_, 1);
                    leanh::lean_inc(v_snd_2715_);
                    leanh::lean_dec(v_a_2710_);
                    v___x_2716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2716_, 0, v_snd_2715_);
                    if v_isShared_2713_ == 0 {
                        leanh::lean_ctor_set(v___x_2712_, 0, v___x_2716_);
                        v___x_2718_ = v___x_2712_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2719_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                        v___x_2718_ = v_reuseFailAlloc_2719_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2714_);
                    leanh::lean_dec(v_a_2710_);
                    v_val_2720_ = leanh::lean_ctor_get(v_fst_2714_, 0);
                    leanh::lean_inc(v_val_2720_);
                    leanh::lean_dec_ref_known(v_fst_2714_, 1);
                    if v_isShared_2713_ == 0 {
                        leanh::lean_ctor_set(v___x_2712_, 0, v_val_2720_);
                        v___x_2722_ = v___x_2712_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2723_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_val_2720_);
                        v___x_2722_ = v_reuseFailAlloc_2723_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2718_;
            }
            3 => {
                return v___x_2722_;
            }
            4 => {
                if v_isShared_2728_ == 0 {
                    v___x_2730_ = v___x_2727_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
                    v___x_2730_ = v_reuseFailAlloc_2731_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2730_;
            }
            6 => {
                v_fst_2743_ = leanh::lean_ctor_get(v_a_2739_, 0);
                if leanh::lean_obj_tag(v_fst_2743_) == 0 {
                    v_snd_2744_ = leanh::lean_ctor_get(v_a_2739_, 1);
                    leanh::lean_inc(v_snd_2744_);
                    leanh::lean_dec(v_a_2739_);
                    v___x_2745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2745_, 0, v_snd_2744_);
                    if v_isShared_2742_ == 0 {
                        leanh::lean_ctor_set(v___x_2741_, 0, v___x_2745_);
                        v___x_2747_ = v___x_2741_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
                        v___x_2747_ = v_reuseFailAlloc_2748_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2743_);
                    leanh::lean_dec(v_a_2739_);
                    v_val_2749_ = leanh::lean_ctor_get(v_fst_2743_, 0);
                    leanh::lean_inc(v_val_2749_);
                    leanh::lean_dec_ref_known(v_fst_2743_, 1);
                    if v_isShared_2742_ == 0 {
                        leanh::lean_ctor_set(v___x_2741_, 0, v_val_2749_);
                        v___x_2751_ = v___x_2741_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2752_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_val_2749_);
                        v___x_2751_ = v_reuseFailAlloc_2752_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2747_;
            }
            8 => {
                return v___x_2751_;
            }
            9 => {
                if v_isShared_2757_ == 0 {
                    v___x_2759_ = v___x_2756_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(
    mut v_includeDelayed_2762_: u8,
    mut v_as_2763_: *mut leanh::LeanObject,
    mut v_sz_2764_: usize,
    mut v_i_2765_: usize,
    mut v_b_2766_: *mut leanh::LeanObject,
    mut v___y_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: usize = 0;
    let mut v___x_2785_: usize = 0;
    let mut v_reuseFailAlloc_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_a_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut v_isSharedCheck_2813_: u8 = 0;
    let mut v_unused_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2773_ = lean_usize_dec_lt(v_i_2765_, v_sz_2764_);
                if v___x_2773_ == 0 {
                    v___x_2774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2774_, 0, v_b_2766_);
                    return v___x_2774_;
                } else {
                    v_snd_2775_ = leanh::lean_ctor_get(v_b_2766_, 1);
                    v_isSharedCheck_2813_ = (!leanh::lean_is_exclusive(v_b_2766_)) as u8;
                    if v_isSharedCheck_2813_ == 0 {
                        v_unused_2814_ = leanh::lean_ctor_get(v_b_2766_, 0);
                        leanh::lean_dec(v_unused_2814_);
                        v___x_2777_ = v_b_2766_;
                        v_isShared_2778_ = v_isSharedCheck_2813_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2775_);
                        leanh::lean_dec(v_b_2766_);
                        v___x_2777_ = leanh::lean_box(0);
                        v_isShared_2778_ = v_isSharedCheck_2813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2779_ = leanh::lean_box(0);
                v_a_2788_ = lean_array_uget_borrowed(v_as_2763_, v_i_2765_);
                if leanh::lean_obj_tag(v_a_2788_) == 0 {
                    v_a_2781_ = v_snd_2775_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2775_);
                    v_val_2789_ = leanh::lean_ctor_get(v_a_2788_, 0);
                    v___x_2790_ = l_Lean_LocalDecl_type(v_val_2789_);
                    v___x_2791_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                        v___x_2790_,
                        v_includeDelayed_2762_,
                        v___y_2767_,
                        v___y_2768_,
                        v___y_2769_,
                        v___y_2770_,
                        v___y_2771_,
                    );
                    if leanh::lean_obj_tag(v___x_2791_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2791_, 1);
                        v___x_2792_ = leanh::lean_box(0);
                        v___x_2793_ = 0;
                        v___x_2794_ = l_Lean_LocalDecl_value_x3f(v_val_2789_, v___x_2793_);
                        if leanh::lean_obj_tag(v___x_2794_) == 1 {
                            v_val_2795_ = leanh::lean_ctor_get(v___x_2794_, 0);
                            leanh::lean_inc(v_val_2795_);
                            leanh::lean_dec_ref_known(v___x_2794_, 1);
                            v___x_2796_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2795_,
                                v_includeDelayed_2762_,
                                v___y_2767_,
                                v___y_2768_,
                                v___y_2769_,
                                v___y_2770_,
                                v___y_2771_,
                            );
                            if leanh::lean_obj_tag(v___x_2796_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2796_, 1);
                                v_a_2781_ = v___x_2792_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2777_);
                                v_a_2797_ = leanh::lean_ctor_get(v___x_2796_, 0);
                                v_isSharedCheck_2804_ =
                                    (!leanh::lean_is_exclusive(v___x_2796_)) as u8;
                                if v_isSharedCheck_2804_ == 0 {
                                    v___x_2799_ = v___x_2796_;
                                    v_isShared_2800_ = v_isSharedCheck_2804_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2797_);
                                    leanh::lean_dec(v___x_2796_);
                                    v___x_2799_ = leanh::lean_box(0);
                                    v_isShared_2800_ = v_isSharedCheck_2804_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2794_);
                            v_a_2781_ = v___x_2792_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2777_);
                        v_a_2805_ = leanh::lean_ctor_get(v___x_2791_, 0);
                        v_isSharedCheck_2812_ =
                            (!leanh::lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_2812_ == 0 {
                            v___x_2807_ = v___x_2791_;
                            v_isShared_2808_ = v_isSharedCheck_2812_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2805_);
                            leanh::lean_dec(v___x_2791_);
                            v___x_2807_ = leanh::lean_box(0);
                            v_isShared_2808_ = v_isSharedCheck_2812_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2778_ == 0 {
                    leanh::lean_ctor_set(v___x_2777_, 1, v_a_2781_);
                    leanh::lean_ctor_set(v___x_2777_, 0, v___x_2779_);
                    v___x_2783_ = v___x_2777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_a_2781_);
                    v___x_2783_ = v_reuseFailAlloc_2787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2784_ = 1usize;
                v___x_2785_ = lean_usize_add(v_i_2765_, v___x_2784_);
                v_i_2765_ = v___x_2785_;
                v_b_2766_ = v___x_2783_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2800_ == 0 {
                    v___x_2802_ = v___x_2799_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
                    v___x_2802_ = v_reuseFailAlloc_2803_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2802_;
            }
            6 => {
                if v_isShared_2808_ == 0 {
                    v___x_2810_ = v___x_2807_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
                    v___x_2810_ = v_reuseFailAlloc_2811_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(
    mut v_includeDelayed_2815_: u8,
    mut v_as_2816_: *mut leanh::LeanObject,
    mut v_sz_2817_: usize,
    mut v_i_2818_: usize,
    mut v_b_2819_: *mut leanh::LeanObject,
    mut v___y_2820_: *mut leanh::LeanObject,
    mut v___y_2821_: *mut leanh::LeanObject,
    mut v___y_2822_: *mut leanh::LeanObject,
    mut v___y_2823_: *mut leanh::LeanObject,
    mut v___y_2824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: usize = 0;
    let mut v___x_2838_: usize = 0;
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_a_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v_isSharedCheck_2866_: u8 = 0;
    let mut v_unused_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2826_ = lean_usize_dec_lt(v_i_2818_, v_sz_2817_);
                if v___x_2826_ == 0 {
                    v___x_2827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2827_, 0, v_b_2819_);
                    return v___x_2827_;
                } else {
                    v_snd_2828_ = leanh::lean_ctor_get(v_b_2819_, 1);
                    v_isSharedCheck_2866_ = (!leanh::lean_is_exclusive(v_b_2819_)) as u8;
                    if v_isSharedCheck_2866_ == 0 {
                        v_unused_2867_ = leanh::lean_ctor_get(v_b_2819_, 0);
                        leanh::lean_dec(v_unused_2867_);
                        v___x_2830_ = v_b_2819_;
                        v_isShared_2831_ = v_isSharedCheck_2866_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2828_);
                        leanh::lean_dec(v_b_2819_);
                        v___x_2830_ = leanh::lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2866_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2832_ = leanh::lean_box(0);
                v_a_2841_ = lean_array_uget_borrowed(v_as_2816_, v_i_2818_);
                if leanh::lean_obj_tag(v_a_2841_) == 0 {
                    v_a_2834_ = v_snd_2828_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2828_);
                    v_val_2842_ = leanh::lean_ctor_get(v_a_2841_, 0);
                    v___x_2843_ = l_Lean_LocalDecl_type(v_val_2842_);
                    v___x_2844_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                        v___x_2843_,
                        v_includeDelayed_2815_,
                        v___y_2820_,
                        v___y_2821_,
                        v___y_2822_,
                        v___y_2823_,
                        v___y_2824_,
                    );
                    if leanh::lean_obj_tag(v___x_2844_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2844_, 1);
                        v___x_2845_ = leanh::lean_box(0);
                        v___x_2846_ = 0;
                        v___x_2847_ = l_Lean_LocalDecl_value_x3f(v_val_2842_, v___x_2846_);
                        if leanh::lean_obj_tag(v___x_2847_) == 1 {
                            v_val_2848_ = leanh::lean_ctor_get(v___x_2847_, 0);
                            leanh::lean_inc(v_val_2848_);
                            leanh::lean_dec_ref_known(v___x_2847_, 1);
                            v___x_2849_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2848_,
                                v_includeDelayed_2815_,
                                v___y_2820_,
                                v___y_2821_,
                                v___y_2822_,
                                v___y_2823_,
                                v___y_2824_,
                            );
                            if leanh::lean_obj_tag(v___x_2849_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2849_, 1);
                                v_a_2834_ = v___x_2845_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2830_);
                                v_a_2850_ = leanh::lean_ctor_get(v___x_2849_, 0);
                                v_isSharedCheck_2857_ =
                                    (!leanh::lean_is_exclusive(v___x_2849_)) as u8;
                                if v_isSharedCheck_2857_ == 0 {
                                    v___x_2852_ = v___x_2849_;
                                    v_isShared_2853_ = v_isSharedCheck_2857_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2850_);
                                    leanh::lean_dec(v___x_2849_);
                                    v___x_2852_ = leanh::lean_box(0);
                                    v_isShared_2853_ = v_isSharedCheck_2857_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2847_);
                            v_a_2834_ = v___x_2845_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2830_);
                        v_a_2858_ = leanh::lean_ctor_get(v___x_2844_, 0);
                        v_isSharedCheck_2865_ =
                            (!leanh::lean_is_exclusive(v___x_2844_)) as u8;
                        if v_isSharedCheck_2865_ == 0 {
                            v___x_2860_ = v___x_2844_;
                            v_isShared_2861_ = v_isSharedCheck_2865_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2858_);
                            leanh::lean_dec(v___x_2844_);
                            v___x_2860_ = leanh::lean_box(0);
                            v_isShared_2861_ = v_isSharedCheck_2865_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2831_ == 0 {
                    leanh::lean_ctor_set(v___x_2830_, 1, v_a_2834_);
                    leanh::lean_ctor_set(v___x_2830_, 0, v___x_2832_);
                    v___x_2836_ = v___x_2830_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_a_2834_);
                    v___x_2836_ = v_reuseFailAlloc_2840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2837_ = 1usize;
                v___x_2838_ = lean_usize_add(v_i_2818_, v___x_2837_);
                v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_2815_, v_as_2816_, v_sz_2817_, v___x_2838_, v___x_2836_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
                return v___x_2839_;
            }
            4 => {
                if v_isShared_2853_ == 0 {
                    v___x_2855_ = v___x_2852_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2855_;
            }
            6 => {
                if v_isShared_2861_ == 0 {
                    v___x_2863_ = v___x_2860_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(
    mut v_includeDelayed_2868_: u8,
    mut v_t_2869_: *mut leanh::LeanObject,
    mut v_init_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v_a_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2891_: usize = 0;
    let mut v___x_2892_: usize = 0;
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v_fst_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v_a_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2877_ = leanh::lean_ctor_get(v_t_2869_, 0);
                v_tail_2878_ = leanh::lean_ctor_get(v_t_2869_, 1);
                v___x_2879_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_2870_, v_includeDelayed_2868_, v_root_2877_, v_init_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
                if leanh::lean_obj_tag(v___x_2879_) == 0 {
                    v_a_2880_ = leanh::lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2916_ = (!leanh::lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2882_ = v___x_2879_;
                        v_isShared_2883_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2880_);
                        leanh::lean_dec(v___x_2879_);
                        v___x_2882_ = leanh::lean_box(0);
                        v_isShared_2883_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2917_ = leanh::lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2924_ = (!leanh::lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2924_ == 0 {
                        v___x_2919_ = v___x_2879_;
                        v_isShared_2920_ = v_isSharedCheck_2924_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2917_);
                        leanh::lean_dec(v___x_2879_);
                        v___x_2919_ = leanh::lean_box(0);
                        v_isShared_2920_ = v_isSharedCheck_2924_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2880_) == 0 {
                    v_a_2884_ = leanh::lean_ctor_get(v_a_2880_, 0);
                    leanh::lean_inc(v_a_2884_);
                    leanh::lean_dec_ref_known(v_a_2880_, 1);
                    if v_isShared_2883_ == 0 {
                        leanh::lean_ctor_set(v___x_2882_, 0, v_a_2884_);
                        v___x_2886_ = v___x_2882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2884_);
                        v___x_2886_ = v_reuseFailAlloc_2887_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2882_);
                    v_a_2888_ = leanh::lean_ctor_get(v_a_2880_, 0);
                    leanh::lean_inc(v_a_2888_);
                    leanh::lean_dec_ref_known(v_a_2880_, 1);
                    v___x_2889_ = leanh::lean_box(0);
                    v___x_2890_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2890_, 0, v___x_2889_);
                    leanh::lean_ctor_set(v___x_2890_, 1, v_a_2888_);
                    v_sz_2891_ = lean_array_size(v_tail_2878_);
                    v___x_2892_ = 0usize;
                    v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_2868_, v_tail_2878_, v_sz_2891_, v___x_2892_, v___x_2890_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
                    if leanh::lean_obj_tag(v___x_2893_) == 0 {
                        v_a_2894_ = leanh::lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2907_ =
                            (!leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2907_ == 0 {
                            v___x_2896_ = v___x_2893_;
                            v_isShared_2897_ = v_isSharedCheck_2907_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2894_);
                            leanh::lean_dec(v___x_2893_);
                            v___x_2896_ = leanh::lean_box(0);
                            v_isShared_2897_ = v_isSharedCheck_2907_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2908_ = leanh::lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2915_ =
                            (!leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2915_ == 0 {
                            v___x_2910_ = v___x_2893_;
                            v_isShared_2911_ = v_isSharedCheck_2915_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2908_);
                            leanh::lean_dec(v___x_2893_);
                            v___x_2910_ = leanh::lean_box(0);
                            v_isShared_2911_ = v_isSharedCheck_2915_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2886_;
            }
            3 => {
                v_fst_2898_ = leanh::lean_ctor_get(v_a_2894_, 0);
                if leanh::lean_obj_tag(v_fst_2898_) == 0 {
                    v_snd_2899_ = leanh::lean_ctor_get(v_a_2894_, 1);
                    leanh::lean_inc(v_snd_2899_);
                    leanh::lean_dec(v_a_2894_);
                    if v_isShared_2897_ == 0 {
                        leanh::lean_ctor_set(v___x_2896_, 0, v_snd_2899_);
                        v___x_2901_ = v___x_2896_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_snd_2899_);
                        v___x_2901_ = v_reuseFailAlloc_2902_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2898_);
                    leanh::lean_dec(v_a_2894_);
                    v_val_2903_ = leanh::lean_ctor_get(v_fst_2898_, 0);
                    leanh::lean_inc(v_val_2903_);
                    leanh::lean_dec_ref_known(v_fst_2898_, 1);
                    if v_isShared_2897_ == 0 {
                        leanh::lean_ctor_set(v___x_2896_, 0, v_val_2903_);
                        v___x_2905_ = v___x_2896_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2906_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_val_2903_);
                        v___x_2905_ = v_reuseFailAlloc_2906_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2901_;
            }
            5 => {
                return v___x_2905_;
            }
            6 => {
                if v_isShared_2911_ == 0 {
                    v___x_2913_ = v___x_2910_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2914_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
                    v___x_2913_ = v_reuseFailAlloc_2914_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2913_;
            }
            8 => {
                if v_isShared_2920_ == 0 {
                    v___x_2922_ = v___x_2919_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2923_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__go(
    mut v_mvarId_2925_: *mut leanh::LeanObject,
    mut v_includeDelayed_2926_: u8,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
    mut v_a_2929_: *mut leanh::LeanObject,
    mut v_a_2930_: *mut leanh::LeanObject,
    mut v_a_2931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2953_: u8 = 0;
    let mut v_cancelTk_x3f_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2955_: u8 = 0;
    let mut v_inheritedTraceOptions_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v_val_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v_a_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v_a_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_a_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_a_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2941_ = leanh::lean_ctor_get(v_a_2930_, 0);
                leanh::lean_inc_ref(v_fileName_2941_);
                v_fileMap_2942_ = leanh::lean_ctor_get(v_a_2930_, 1);
                leanh::lean_inc_ref(v_fileMap_2942_);
                v_options_2943_ = leanh::lean_ctor_get(v_a_2930_, 2);
                leanh::lean_inc_ref(v_options_2943_);
                v_currRecDepth_2944_ = leanh::lean_ctor_get(v_a_2930_, 3);
                leanh::lean_inc(v_currRecDepth_2944_);
                v_maxRecDepth_2945_ = leanh::lean_ctor_get(v_a_2930_, 4);
                leanh::lean_inc(v_maxRecDepth_2945_);
                v_ref_2946_ = leanh::lean_ctor_get(v_a_2930_, 5);
                leanh::lean_inc(v_ref_2946_);
                v_currNamespace_2947_ = leanh::lean_ctor_get(v_a_2930_, 6);
                leanh::lean_inc(v_currNamespace_2947_);
                v_openDecls_2948_ = leanh::lean_ctor_get(v_a_2930_, 7);
                leanh::lean_inc(v_openDecls_2948_);
                v_initHeartbeats_2949_ = leanh::lean_ctor_get(v_a_2930_, 8);
                leanh::lean_inc(v_initHeartbeats_2949_);
                v_maxHeartbeats_2950_ = leanh::lean_ctor_get(v_a_2930_, 9);
                leanh::lean_inc(v_maxHeartbeats_2950_);
                v_quotContext_2951_ = leanh::lean_ctor_get(v_a_2930_, 10);
                leanh::lean_inc(v_quotContext_2951_);
                v_currMacroScope_2952_ = leanh::lean_ctor_get(v_a_2930_, 11);
                leanh::lean_inc(v_currMacroScope_2952_);
                v_diag_2953_ = leanh::lean_ctor_get_uint8(
                    v_a_2930_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2954_ = leanh::lean_ctor_get(v_a_2930_, 12);
                leanh::lean_inc(v_cancelTk_x3f_2954_);
                v_suppressElabErrors_2955_ = leanh::lean_ctor_get_uint8(
                    v_a_2930_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2956_ = leanh::lean_ctor_get(v_a_2930_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2956_);
                leanh::lean_dec_ref(v_a_2930_);
                v___x_3011_ = leanh::lean_unsigned_to_nat(0);
                v___x_3012_ = lean_nat_dec_eq(v_maxRecDepth_2945_, v___x_3011_);
                if v___x_3012_ == 0 {
                    v___x_3013_ = lean_nat_dec_eq(v_currRecDepth_2944_, v_maxRecDepth_2945_);
                    if v___x_3013_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_inheritedTraceOptions_2956_);
                        leanh::lean_dec(v_cancelTk_x3f_2954_);
                        leanh::lean_dec(v_currMacroScope_2952_);
                        leanh::lean_dec(v_quotContext_2951_);
                        leanh::lean_dec(v_maxHeartbeats_2950_);
                        leanh::lean_dec(v_initHeartbeats_2949_);
                        leanh::lean_dec(v_openDecls_2948_);
                        leanh::lean_dec(v_currNamespace_2947_);
                        leanh::lean_dec(v_maxRecDepth_2945_);
                        leanh::lean_dec(v_currRecDepth_2944_);
                        leanh::lean_dec_ref(v_options_2943_);
                        leanh::lean_dec_ref(v_fileMap_2942_);
                        leanh::lean_dec_ref(v_fileName_2941_);
                        leanh::lean_dec(v_mvarId_2925_);
                        v___x_3014_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(v_ref_2946_);
                        return v___x_3014_;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2937_ = lean_st_ref_take(v_a_2927_);
                leanh::lean_inc(v___y_2934_);
                v___x_2938_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_2937_, v___y_2934_, v___y_2935_);
                v___x_2939_ = lean_st_ref_set(v_a_2927_, v___x_2938_);
                v_mvarId_2925_ = v___y_2934_;
                v_a_2930_ = v___y_2936_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2958_ = leanh::lean_unsigned_to_nat(1);
                v___x_2959_ = lean_nat_add(v_currRecDepth_2944_, v___x_2958_);
                leanh::lean_dec(v_currRecDepth_2944_);
                v___x_2960_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2960_, 0, v_fileName_2941_);
                leanh::lean_ctor_set(v___x_2960_, 1, v_fileMap_2942_);
                leanh::lean_ctor_set(v___x_2960_, 2, v_options_2943_);
                leanh::lean_ctor_set(v___x_2960_, 3, v___x_2959_);
                leanh::lean_ctor_set(v___x_2960_, 4, v_maxRecDepth_2945_);
                leanh::lean_ctor_set(v___x_2960_, 5, v_ref_2946_);
                leanh::lean_ctor_set(v___x_2960_, 6, v_currNamespace_2947_);
                leanh::lean_ctor_set(v___x_2960_, 7, v_openDecls_2948_);
                leanh::lean_ctor_set(v___x_2960_, 8, v_initHeartbeats_2949_);
                leanh::lean_ctor_set(v___x_2960_, 9, v_maxHeartbeats_2950_);
                leanh::lean_ctor_set(v___x_2960_, 10, v_quotContext_2951_);
                leanh::lean_ctor_set(v___x_2960_, 11, v_currMacroScope_2952_);
                leanh::lean_ctor_set(v___x_2960_, 12, v_cancelTk_x3f_2954_);
                leanh::lean_ctor_set(v___x_2960_, 13, v_inheritedTraceOptions_2956_);
                leanh::lean_ctor_set_uint8(
                    v___x_2960_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2953_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2960_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2955_,
                );
                leanh::lean_inc(v_mvarId_2925_);
                v___x_2961_ = l_Lean_MVarId_getDecl(
                    v_mvarId_2925_,
                    v_a_2928_,
                    v_a_2929_,
                    v___x_2960_,
                    v_a_2931_,
                );
                if leanh::lean_obj_tag(v___x_2961_) == 0 {
                    v_a_2962_ = leanh::lean_ctor_get(v___x_2961_, 0);
                    leanh::lean_inc(v_a_2962_);
                    leanh::lean_dec_ref_known(v___x_2961_, 1);
                    v_lctx_2963_ = leanh::lean_ctor_get(v_a_2962_, 1);
                    leanh::lean_inc_ref(v_lctx_2963_);
                    v_type_2964_ = leanh::lean_ctor_get(v_a_2962_, 2);
                    leanh::lean_inc_ref(v_type_2964_);
                    leanh::lean_dec(v_a_2962_);
                    v___x_2965_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                        v_type_2964_,
                        v_includeDelayed_2926_,
                        v_a_2927_,
                        v_a_2928_,
                        v_a_2929_,
                        v___x_2960_,
                        v_a_2931_,
                    );
                    if leanh::lean_obj_tag(v___x_2965_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2965_, 1);
                        v_decls_2966_ = leanh::lean_ctor_get(v_lctx_2963_, 1);
                        leanh::lean_inc_ref(v_decls_2966_);
                        leanh::lean_dec_ref(v_lctx_2963_);
                        v___x_2967_ = leanh::lean_box(0);
                        v___x_2968_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_2926_, v_decls_2966_, v___x_2967_, v_a_2927_, v_a_2928_, v_a_2929_, v___x_2960_, v_a_2931_);
                        leanh::lean_dec_ref(v_decls_2966_);
                        if leanh::lean_obj_tag(v___x_2968_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2968_, 1);
                            v___x_2969_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_2925_, v_a_2929_);
                            leanh::lean_dec(v_mvarId_2925_);
                            if leanh::lean_obj_tag(v___x_2969_) == 0 {
                                v_a_2970_ = leanh::lean_ctor_get(v___x_2969_, 0);
                                v_isSharedCheck_2994_ =
                                    (!leanh::lean_is_exclusive(v___x_2969_)) as u8;
                                if v_isSharedCheck_2994_ == 0 {
                                    v___x_2972_ = v___x_2969_;
                                    v_isShared_2973_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2970_);
                                    leanh::lean_dec(v___x_2969_);
                                    v___x_2972_ = leanh::lean_box(0);
                                    v_isShared_2973_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v___x_2960_, 14);
                                v_a_2995_ = leanh::lean_ctor_get(v___x_2969_, 0);
                                v_isSharedCheck_3002_ =
                                    (!leanh::lean_is_exclusive(v___x_2969_)) as u8;
                                if v_isSharedCheck_3002_ == 0 {
                                    v___x_2997_ = v___x_2969_;
                                    v_isShared_2998_ = v_isSharedCheck_3002_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2995_);
                                    leanh::lean_dec(v___x_2969_);
                                    v___x_2997_ = leanh::lean_box(0);
                                    v_isShared_2998_ = v_isSharedCheck_3002_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_2960_, 14);
                            leanh::lean_dec(v_mvarId_2925_);
                            return v___x_2968_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_lctx_2963_);
                        leanh::lean_dec_ref_known(v___x_2960_, 14);
                        leanh::lean_dec(v_mvarId_2925_);
                        return v___x_2965_;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2960_, 14);
                    leanh::lean_dec(v_mvarId_2925_);
                    v_a_3003_ = leanh::lean_ctor_get(v___x_2961_, 0);
                    v_isSharedCheck_3010_ = (!leanh::lean_is_exclusive(v___x_2961_)) as u8;
                    if v_isSharedCheck_3010_ == 0 {
                        v___x_3005_ = v___x_2961_;
                        v_isShared_3006_ = v_isSharedCheck_3010_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3003_);
                        leanh::lean_dec(v___x_2961_);
                        v___x_3005_ = leanh::lean_box(0);
                        v_isShared_3006_ = v_isSharedCheck_3010_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2970_) == 1 {
                    leanh::lean_del_object(v___x_2972_);
                    v_val_2974_ = leanh::lean_ctor_get(v_a_2970_, 0);
                    leanh::lean_inc(v_val_2974_);
                    leanh::lean_dec_ref_known(v_a_2970_, 1);
                    v_mvarIdPending_2975_ = leanh::lean_ctor_get(v_val_2974_, 1);
                    leanh::lean_inc(v_mvarIdPending_2975_);
                    leanh::lean_dec(v_val_2974_);
                    v___x_2976_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_2975_, v_a_2929_);
                    if leanh::lean_obj_tag(v___x_2976_) == 0 {
                        v_a_2977_ = leanh::lean_ctor_get(v___x_2976_, 0);
                        leanh::lean_inc(v_a_2977_);
                        leanh::lean_dec_ref_known(v___x_2976_, 1);
                        v___x_2978_ = (leanh::lean_unbox(v_a_2977_) as u8);
                        leanh::lean_dec(v_a_2977_);
                        if v___x_2978_ == 0 {
                            v___y_2934_ = v_mvarIdPending_2975_;
                            v___y_2935_ = v___x_2967_;
                            v___y_2936_ = v___x_2960_;
                            state = 1;
                            continue;
                        } else {
                            v_mvarId_2925_ = v_mvarIdPending_2975_;
                            v_a_2930_ = v___x_2960_;
                            state = 0;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_2976_) == 0 {
                            v_a_2980_ = leanh::lean_ctor_get(v___x_2976_, 0);
                            leanh::lean_inc(v_a_2980_);
                            leanh::lean_dec_ref_known(v___x_2976_, 1);
                            v___x_2981_ = (leanh::lean_unbox(v_a_2980_) as u8);
                            leanh::lean_dec(v_a_2980_);
                            if v___x_2981_ == 0 {
                                v_mvarId_2925_ = v_mvarIdPending_2975_;
                                v_a_2930_ = v___x_2960_;
                                state = 0;
                                continue;
                            } else {
                                v___y_2934_ = v_mvarIdPending_2975_;
                                v___y_2935_ = v___x_2967_;
                                v___y_2936_ = v___x_2960_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_mvarIdPending_2975_);
                            leanh::lean_dec_ref_known(v___x_2960_, 14);
                            v_a_2983_ = leanh::lean_ctor_get(v___x_2976_, 0);
                            v_isSharedCheck_2990_ =
                                (!leanh::lean_is_exclusive(v___x_2976_)) as u8;
                            if v_isSharedCheck_2990_ == 0 {
                                v___x_2985_ = v___x_2976_;
                                v_isShared_2986_ = v_isSharedCheck_2990_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2983_);
                                leanh::lean_dec(v___x_2976_);
                                v___x_2985_ = leanh::lean_box(0);
                                v_isShared_2986_ = v_isSharedCheck_2990_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2970_);
                    leanh::lean_dec_ref_known(v___x_2960_, 14);
                    if v_isShared_2973_ == 0 {
                        leanh::lean_ctor_set(v___x_2972_, 0, v___x_2967_);
                        v___x_2992_ = v___x_2972_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2967_);
                        v___x_2992_ = v_reuseFailAlloc_2993_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2986_ == 0 {
                    v___x_2988_ = v___x_2985_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
                    v___x_2988_ = v_reuseFailAlloc_2989_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2988_;
            }
            6 => {
                return v___x_2992_;
            }
            7 => {
                if v_isShared_2998_ == 0 {
                    v___x_3000_ = v___x_2997_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
                    v___x_3000_ = v_reuseFailAlloc_3001_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3000_;
            }
            9 => {
                if v_isShared_3006_ == 0 {
                    v___x_3008_ = v___x_3005_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
                    v___x_3008_ = v_reuseFailAlloc_3009_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(
    mut v_as_3015_: *mut leanh::LeanObject,
    mut v_i_3016_: usize,
    mut v_stop_3017_: usize,
    mut v_b_3018_: *mut leanh::LeanObject,
    mut v___y_3019_: *mut leanh::LeanObject,
    mut v___y_3020_: *mut leanh::LeanObject,
    mut v___y_3021_: *mut leanh::LeanObject,
    mut v___y_3022_: *mut leanh::LeanObject,
    mut v___y_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3025_ = lean_usize_dec_eq(v_i_3016_, v_stop_3017_);
                if v___x_3025_ == 0 {
                    v___x_3026_ = lean_array_uget_borrowed(v_as_3015_, v_i_3016_);
                    leanh::lean_inc_ref(v___y_3022_);
                    leanh::lean_inc(v___x_3026_);
                    v___x_3027_ = l___private_Lean_Meta_CollectMVars_0__go(
                        v___x_3026_,
                        v___x_3025_,
                        v___y_3019_,
                        v___y_3020_,
                        v___y_3021_,
                        v___y_3022_,
                        v___y_3023_,
                    );
                    if leanh::lean_obj_tag(v___x_3027_) == 0 {
                        v_a_3028_ = leanh::lean_ctor_get(v___x_3027_, 0);
                        leanh::lean_inc(v_a_3028_);
                        leanh::lean_dec_ref_known(v___x_3027_, 1);
                        v___x_3029_ = 1usize;
                        v___x_3030_ = lean_usize_add(v_i_3016_, v___x_3029_);
                        v_i_3016_ = v___x_3030_;
                        v_b_3018_ = v_a_3028_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3027_;
                    }
                } else {
                    v___x_3032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3032_, 0, v_b_3018_);
                    return v___x_3032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(
    mut v_as_3033_: *mut leanh::LeanObject,
    mut v_i_3034_: *mut leanh::LeanObject,
    mut v_stop_3035_: *mut leanh::LeanObject,
    mut v_b_3036_: *mut leanh::LeanObject,
    mut v___y_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
    mut v___y_3039_: *mut leanh::LeanObject,
    mut v___y_3040_: *mut leanh::LeanObject,
    mut v___y_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3043_: usize = 0;
    let mut v_stop_boxed_3044_: usize = 0;
    let mut v_res_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3043_ = leanh::lean_unbox_usize(v_i_3034_);
    leanh::lean_dec(v_i_3034_);
    v_stop_boxed_3044_ = leanh::lean_unbox_usize(v_stop_3035_);
    leanh::lean_dec(v_stop_3035_);
    v_res_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_3033_, v_i_boxed_3043_, v_stop_boxed_3044_, v_b_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
    leanh::lean_dec(v___y_3041_);
    leanh::lean_dec_ref(v___y_3040_);
    leanh::lean_dec(v___y_3039_);
    leanh::lean_dec_ref(v___y_3038_);
    leanh::lean_dec(v___y_3037_);
    leanh::lean_dec_ref(v_as_3033_);
    return v_res_3045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(
    mut v_init_3046_: *mut leanh::LeanObject,
    mut v_includeDelayed_3047_: *mut leanh::LeanObject,
    mut v_as_3048_: *mut leanh::LeanObject,
    mut v_sz_3049_: *mut leanh::LeanObject,
    mut v_i_3050_: *mut leanh::LeanObject,
    mut v_b_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
    mut v___y_3053_: *mut leanh::LeanObject,
    mut v___y_3054_: *mut leanh::LeanObject,
    mut v___y_3055_: *mut leanh::LeanObject,
    mut v___y_3056_: *mut leanh::LeanObject,
    mut v___y_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3058_: u8 = 0;
    let mut v_sz_boxed_3059_: usize = 0;
    let mut v_i_boxed_3060_: usize = 0;
    let mut v_res_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3058_ = (leanh::lean_unbox(v_includeDelayed_3047_) as u8);
    v_sz_boxed_3059_ = leanh::lean_unbox_usize(v_sz_3049_);
    leanh::lean_dec(v_sz_3049_);
    v_i_boxed_3060_ = leanh::lean_unbox_usize(v_i_3050_);
    leanh::lean_dec(v_i_3050_);
    v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_3046_, v_includeDelayed_boxed_3058_, v_as_3048_, v_sz_boxed_3059_, v_i_boxed_3060_, v_b_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
    leanh::lean_dec(v___y_3056_);
    leanh::lean_dec_ref(v___y_3055_);
    leanh::lean_dec(v___y_3054_);
    leanh::lean_dec_ref(v___y_3053_);
    leanh::lean_dec(v___y_3052_);
    leanh::lean_dec_ref(v_as_3048_);
    return v_res_3061_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(
    mut v_includeDelayed_3062_: *mut leanh::LeanObject,
    mut v_t_3063_: *mut leanh::LeanObject,
    mut v_init_3064_: *mut leanh::LeanObject,
    mut v___y_3065_: *mut leanh::LeanObject,
    mut v___y_3066_: *mut leanh::LeanObject,
    mut v___y_3067_: *mut leanh::LeanObject,
    mut v___y_3068_: *mut leanh::LeanObject,
    mut v___y_3069_: *mut leanh::LeanObject,
    mut v___y_3070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3071_: u8 = 0;
    let mut v_res_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3071_ = (leanh::lean_unbox(v_includeDelayed_3062_) as u8);
    v_res_3072_ =
        l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(
            v_includeDelayed_boxed_3071_,
            v_t_3063_,
            v_init_3064_,
            v___y_3065_,
            v___y_3066_,
            v___y_3067_,
            v___y_3068_,
            v___y_3069_,
        );
    leanh::lean_dec(v___y_3069_);
    leanh::lean_dec_ref(v___y_3068_);
    leanh::lean_dec(v___y_3067_);
    leanh::lean_dec_ref(v___y_3066_);
    leanh::lean_dec(v___y_3065_);
    leanh::lean_dec_ref(v_t_3063_);
    return v_res_3072_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(
    mut v_includeDelayed_3073_: *mut leanh::LeanObject,
    mut v_as_3074_: *mut leanh::LeanObject,
    mut v_sz_3075_: *mut leanh::LeanObject,
    mut v_i_3076_: *mut leanh::LeanObject,
    mut v_b_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
    mut v___y_3079_: *mut leanh::LeanObject,
    mut v___y_3080_: *mut leanh::LeanObject,
    mut v___y_3081_: *mut leanh::LeanObject,
    mut v___y_3082_: *mut leanh::LeanObject,
    mut v___y_3083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3084_: u8 = 0;
    let mut v_sz_boxed_3085_: usize = 0;
    let mut v_i_boxed_3086_: usize = 0;
    let mut v_res_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3084_ = (leanh::lean_unbox(v_includeDelayed_3073_) as u8);
    v_sz_boxed_3085_ = leanh::lean_unbox_usize(v_sz_3075_);
    leanh::lean_dec(v_sz_3075_);
    v_i_boxed_3086_ = leanh::lean_unbox_usize(v_i_3076_);
    leanh::lean_dec(v_i_3076_);
    v_res_3087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_3084_, v_as_3074_, v_sz_boxed_3085_, v_i_boxed_3086_, v_b_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
    leanh::lean_dec(v___y_3082_);
    leanh::lean_dec_ref(v___y_3081_);
    leanh::lean_dec(v___y_3080_);
    leanh::lean_dec_ref(v___y_3079_);
    leanh::lean_dec(v___y_3078_);
    leanh::lean_dec_ref(v_as_3074_);
    return v_res_3087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(
    mut v_includeDelayed_3088_: *mut leanh::LeanObject,
    mut v_as_3089_: *mut leanh::LeanObject,
    mut v_sz_3090_: *mut leanh::LeanObject,
    mut v_i_3091_: *mut leanh::LeanObject,
    mut v_b_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
    mut v___y_3095_: *mut leanh::LeanObject,
    mut v___y_3096_: *mut leanh::LeanObject,
    mut v___y_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3099_: u8 = 0;
    let mut v_sz_boxed_3100_: usize = 0;
    let mut v_i_boxed_3101_: usize = 0;
    let mut v_res_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3099_ = (leanh::lean_unbox(v_includeDelayed_3088_) as u8);
    v_sz_boxed_3100_ = leanh::lean_unbox_usize(v_sz_3090_);
    leanh::lean_dec(v_sz_3090_);
    v_i_boxed_3101_ = leanh::lean_unbox_usize(v_i_3091_);
    leanh::lean_dec(v_i_3091_);
    v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_3099_, v_as_3089_, v_sz_boxed_3100_, v_i_boxed_3101_, v_b_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
    leanh::lean_dec(v___y_3097_);
    leanh::lean_dec_ref(v___y_3096_);
    leanh::lean_dec(v___y_3095_);
    leanh::lean_dec_ref(v___y_3094_);
    leanh::lean_dec(v___y_3093_);
    leanh::lean_dec_ref(v_as_3089_);
    return v_res_3102_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(
    mut v_includeDelayed_3103_: *mut leanh::LeanObject,
    mut v_as_3104_: *mut leanh::LeanObject,
    mut v_sz_3105_: *mut leanh::LeanObject,
    mut v_i_3106_: *mut leanh::LeanObject,
    mut v_b_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
    mut v___y_3109_: *mut leanh::LeanObject,
    mut v___y_3110_: *mut leanh::LeanObject,
    mut v___y_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3114_: u8 = 0;
    let mut v_sz_boxed_3115_: usize = 0;
    let mut v_i_boxed_3116_: usize = 0;
    let mut v_res_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3114_ = (leanh::lean_unbox(v_includeDelayed_3103_) as u8);
    v_sz_boxed_3115_ = leanh::lean_unbox_usize(v_sz_3105_);
    leanh::lean_dec(v_sz_3105_);
    v_i_boxed_3116_ = leanh::lean_unbox_usize(v_i_3106_);
    leanh::lean_dec(v_i_3106_);
    v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_3114_, v_as_3104_, v_sz_boxed_3115_, v_i_boxed_3116_, v_b_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
    leanh::lean_dec(v___y_3112_);
    leanh::lean_dec_ref(v___y_3111_);
    leanh::lean_dec(v___y_3110_);
    leanh::lean_dec_ref(v___y_3109_);
    leanh::lean_dec(v___y_3108_);
    leanh::lean_dec_ref(v_as_3104_);
    return v_res_3117_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(
    mut v_includeDelayed_3118_: *mut leanh::LeanObject,
    mut v_as_3119_: *mut leanh::LeanObject,
    mut v_sz_3120_: *mut leanh::LeanObject,
    mut v_i_3121_: *mut leanh::LeanObject,
    mut v_b_3122_: *mut leanh::LeanObject,
    mut v___y_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3129_: u8 = 0;
    let mut v_sz_boxed_3130_: usize = 0;
    let mut v_i_boxed_3131_: usize = 0;
    let mut v_res_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3129_ = (leanh::lean_unbox(v_includeDelayed_3118_) as u8);
    v_sz_boxed_3130_ = leanh::lean_unbox_usize(v_sz_3120_);
    leanh::lean_dec(v_sz_3120_);
    v_i_boxed_3131_ = leanh::lean_unbox_usize(v_i_3121_);
    leanh::lean_dec(v_i_3121_);
    v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_3129_, v_as_3119_, v_sz_boxed_3130_, v_i_boxed_3131_, v_b_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
    leanh::lean_dec(v___y_3127_);
    leanh::lean_dec_ref(v___y_3126_);
    leanh::lean_dec(v___y_3125_);
    leanh::lean_dec_ref(v___y_3124_);
    leanh::lean_dec(v___y_3123_);
    leanh::lean_dec_ref(v_as_3119_);
    return v_res_3132_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(
    mut v_init_3133_: *mut leanh::LeanObject,
    mut v_includeDelayed_3134_: *mut leanh::LeanObject,
    mut v_n_3135_: *mut leanh::LeanObject,
    mut v_b_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
    mut v___y_3139_: *mut leanh::LeanObject,
    mut v___y_3140_: *mut leanh::LeanObject,
    mut v___y_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3143_: u8 = 0;
    let mut v_res_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3143_ = (leanh::lean_unbox(v_includeDelayed_3134_) as u8);
    v_res_3144_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_3133_, v_includeDelayed_boxed_3143_, v_n_3135_, v_b_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
    leanh::lean_dec(v___y_3141_);
    leanh::lean_dec_ref(v___y_3140_);
    leanh::lean_dec(v___y_3139_);
    leanh::lean_dec_ref(v___y_3138_);
    leanh::lean_dec(v___y_3137_);
    leanh::lean_dec_ref(v_n_3135_);
    return v_res_3144_;
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(
    mut v_e_3145_: *mut leanh::LeanObject,
    mut v_includeDelayed_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
    mut v_a_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3153_: u8 = 0;
    let mut v_res_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3153_ = (leanh::lean_unbox(v_includeDelayed_3146_) as u8);
    v_res_3154_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
        v_e_3145_,
        v_includeDelayed_boxed_3153_,
        v_a_3147_,
        v_a_3148_,
        v_a_3149_,
        v_a_3150_,
        v_a_3151_,
    );
    leanh::lean_dec(v_a_3151_);
    leanh::lean_dec_ref(v_a_3150_);
    leanh::lean_dec(v_a_3149_);
    leanh::lean_dec_ref(v_a_3148_);
    leanh::lean_dec(v_a_3147_);
    return v_res_3154_;
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__go___boxed(
    mut v_mvarId_3155_: *mut leanh::LeanObject,
    mut v_includeDelayed_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
    mut v_a_3159_: *mut leanh::LeanObject,
    mut v_a_3160_: *mut leanh::LeanObject,
    mut v_a_3161_: *mut leanh::LeanObject,
    mut v_a_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3163_: u8 = 0;
    let mut v_res_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3163_ = (leanh::lean_unbox(v_includeDelayed_3156_) as u8);
    v_res_3164_ = l___private_Lean_Meta_CollectMVars_0__go(
        v_mvarId_3155_,
        v_includeDelayed_boxed_3163_,
        v_a_3157_,
        v_a_3158_,
        v_a_3159_,
        v_a_3160_,
        v_a_3161_,
    );
    leanh::lean_dec(v_a_3161_);
    leanh::lean_dec(v_a_3159_);
    leanh::lean_dec_ref(v_a_3158_);
    leanh::lean_dec(v_a_3157_);
    return v_res_3164_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(
    mut v_mvarId_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
    mut v___y_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3172_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_3165_, v___y_3168_);
    return v___x_3172_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(
    mut v_mvarId_3173_: *mut leanh::LeanObject,
    mut v___y_3174_: *mut leanh::LeanObject,
    mut v___y_3175_: *mut leanh::LeanObject,
    mut v___y_3176_: *mut leanh::LeanObject,
    mut v___y_3177_: *mut leanh::LeanObject,
    mut v___y_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3180_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(
            v_mvarId_3173_,
            v___y_3174_,
            v___y_3175_,
            v___y_3176_,
            v___y_3177_,
            v___y_3178_,
        );
    leanh::lean_dec(v___y_3178_);
    leanh::lean_dec_ref(v___y_3177_);
    leanh::lean_dec(v___y_3176_);
    leanh::lean_dec_ref(v___y_3175_);
    leanh::lean_dec(v___y_3174_);
    leanh::lean_dec(v_mvarId_3173_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(
    mut v_00_u03b1_3181_: *mut leanh::LeanObject,
    mut v_ref_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ =
        l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(
            v_ref_3182_,
        );
    return v___x_3189_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(
    mut v_00_u03b1_3190_: *mut leanh::LeanObject,
    mut v_ref_3191_: *mut leanh::LeanObject,
    mut v___y_3192_: *mut leanh::LeanObject,
    mut v___y_3193_: *mut leanh::LeanObject,
    mut v___y_3194_: *mut leanh::LeanObject,
    mut v___y_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(
        v_00_u03b1_3190_,
        v_ref_3191_,
        v___y_3192_,
        v___y_3193_,
        v___y_3194_,
        v___y_3195_,
        v___y_3196_,
    );
    leanh::lean_dec(v___y_3196_);
    leanh::lean_dec_ref(v___y_3195_);
    leanh::lean_dec(v___y_3194_);
    leanh::lean_dec_ref(v___y_3193_);
    leanh::lean_dec(v___y_3192_);
    return v_res_3198_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(
    mut v_00_u03b2_3199_: *mut leanh::LeanObject,
    mut v_m_3200_: *mut leanh::LeanObject,
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_b_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3203_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_3200_, v_a_3201_, v_b_3202_);
    return v___x_3203_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(
    mut v_mvarId_3204_: *mut leanh::LeanObject,
    mut v___y_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
    mut v___y_3209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3211_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_3204_, v___y_3207_);
    return v___x_3211_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(
    mut v_mvarId_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: *mut leanh::LeanObject,
    mut v___y_3215_: *mut leanh::LeanObject,
    mut v___y_3216_: *mut leanh::LeanObject,
    mut v___y_3217_: *mut leanh::LeanObject,
    mut v___y_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
    leanh::lean_dec(v___y_3217_);
    leanh::lean_dec_ref(v___y_3216_);
    leanh::lean_dec(v___y_3215_);
    leanh::lean_dec_ref(v___y_3214_);
    leanh::lean_dec(v___y_3213_);
    leanh::lean_dec(v_mvarId_3212_);
    return v_res_3219_;
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(
    mut v_mvarId_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
    mut v___y_3222_: *mut leanh::LeanObject,
    mut v___y_3223_: *mut leanh::LeanObject,
    mut v___y_3224_: *mut leanh::LeanObject,
    mut v___y_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_3220_, v___y_3223_);
    return v___x_3227_;
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(
    mut v_mvarId_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
    mut v___y_3230_: *mut leanh::LeanObject,
    mut v___y_3231_: *mut leanh::LeanObject,
    mut v___y_3232_: *mut leanh::LeanObject,
    mut v___y_3233_: *mut leanh::LeanObject,
    mut v___y_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
    leanh::lean_dec(v___y_3233_);
    leanh::lean_dec_ref(v___y_3232_);
    leanh::lean_dec(v___y_3231_);
    leanh::lean_dec_ref(v___y_3230_);
    leanh::lean_dec(v___y_3229_);
    leanh::lean_dec(v_mvarId_3228_);
    return v_res_3235_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(
    mut v_00_u03b2_3236_: *mut leanh::LeanObject,
    mut v_a_3237_: *mut leanh::LeanObject,
    mut v_x_3238_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3239_: u8 = 0;
    v___x_3239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_3237_, v_x_3238_);
    return v___x_3239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_3240_: *mut leanh::LeanObject,
    mut v_a_3241_: *mut leanh::LeanObject,
    mut v_x_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3243_: u8 = 0;
    let mut v_r_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_3240_, v_a_3241_, v_x_3242_);
    leanh::lean_dec(v_x_3242_);
    leanh::lean_dec(v_a_3241_);
    v_r_3244_ = leanh::lean_box((v_res_3243_) as usize);
    return v_r_3244_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(
    mut v_00_u03b2_3245_: *mut leanh::LeanObject,
    mut v_data_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_3246_);
    return v___x_3247_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(
    mut v_00_u03b2_3248_: *mut leanh::LeanObject,
    mut v_i_3249_: *mut leanh::LeanObject,
    mut v_source_3250_: *mut leanh::LeanObject,
    mut v_target_3251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_3249_, v_source_3250_, v_target_3251_);
    return v___x_3252_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(
    mut v_00_u03b2_3253_: *mut leanh::LeanObject,
    mut v_x_3254_: *mut leanh::LeanObject,
    mut v_x_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_3254_, v_x_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_MVarId_getMVarDependencies(
    mut v_mvarId_3257_: *mut leanh::LeanObject,
    mut v_includeDelayed_3258_: u8,
    mut v_a_3259_: *mut leanh::LeanObject,
    mut v_a_3260_: *mut leanh::LeanObject,
    mut v_a_3261_: *mut leanh::LeanObject,
    mut v_a_3262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut v_unused_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3264_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once
                    ),
                    _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1,
                );
                v___x_3265_ = lean_st_mk_ref(v___x_3264_);
                leanh::lean_inc_ref(v_a_3261_);
                v___x_3266_ = l___private_Lean_Meta_CollectMVars_0__go(
                    v_mvarId_3257_,
                    v_includeDelayed_3258_,
                    v___x_3265_,
                    v_a_3259_,
                    v_a_3260_,
                    v_a_3261_,
                    v_a_3262_,
                );
                if leanh::lean_obj_tag(v___x_3266_) == 0 {
                    v_isSharedCheck_3274_ = (!leanh::lean_is_exclusive(v___x_3266_)) as u8;
                    if v_isSharedCheck_3274_ == 0 {
                        v_unused_3275_ = leanh::lean_ctor_get(v___x_3266_, 0);
                        leanh::lean_dec(v_unused_3275_);
                        v___x_3268_ = v___x_3266_;
                        v_isShared_3269_ = v_isSharedCheck_3274_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3266_);
                        v___x_3268_ = leanh::lean_box(0);
                        v_isShared_3269_ = v_isSharedCheck_3274_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3265_);
                    v_a_3276_ = leanh::lean_ctor_get(v___x_3266_, 0);
                    v_isSharedCheck_3283_ = (!leanh::lean_is_exclusive(v___x_3266_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v___x_3278_ = v___x_3266_;
                        v_isShared_3279_ = v_isSharedCheck_3283_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3276_);
                        leanh::lean_dec(v___x_3266_);
                        v___x_3278_ = leanh::lean_box(0);
                        v_isShared_3279_ = v_isSharedCheck_3283_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3270_ = lean_st_ref_get(v___x_3265_);
                leanh::lean_dec(v___x_3265_);
                if v_isShared_3269_ == 0 {
                    leanh::lean_ctor_set(v___x_3268_, 0, v___x_3270_);
                    v___x_3272_ = v___x_3268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
                    v___x_3272_ = v_reuseFailAlloc_3273_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3272_;
            }
            3 => {
                if v_isShared_3279_ == 0 {
                    v___x_3281_ = v___x_3278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
                    v___x_3281_ = v_reuseFailAlloc_3282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_getMVarDependencies___boxed(
    mut v_mvarId_3284_: *mut leanh::LeanObject,
    mut v_includeDelayed_3285_: *mut leanh::LeanObject,
    mut v_a_3286_: *mut leanh::LeanObject,
    mut v_a_3287_: *mut leanh::LeanObject,
    mut v_a_3288_: *mut leanh::LeanObject,
    mut v_a_3289_: *mut leanh::LeanObject,
    mut v_a_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3291_: u8 = 0;
    let mut v_res_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3291_ = (leanh::lean_unbox(v_includeDelayed_3285_) as u8);
    v_res_3292_ = l_Lean_MVarId_getMVarDependencies(
        v_mvarId_3284_,
        v_includeDelayed_boxed_3291_,
        v_a_3286_,
        v_a_3287_,
        v_a_3288_,
        v_a_3289_,
    );
    leanh::lean_dec(v_a_3289_);
    leanh::lean_dec_ref(v_a_3288_);
    leanh::lean_dec(v_a_3287_);
    leanh::lean_dec_ref(v_a_3286_);
    return v_res_3292_;
}
pub unsafe fn l_Lean_Expr_getMVarDependencies(
    mut v_e_3293_: *mut leanh::LeanObject,
    mut v_includeDelayed_3294_: u8,
    mut v_a_3295_: *mut leanh::LeanObject,
    mut v_a_3296_: *mut leanh::LeanObject,
    mut v_a_3297_: *mut leanh::LeanObject,
    mut v_a_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut v_unused_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3300_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once
                    ),
                    _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1,
                );
                v___x_3301_ = lean_st_mk_ref(v___x_3300_);
                v___x_3302_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                    v_e_3293_,
                    v_includeDelayed_3294_,
                    v___x_3301_,
                    v_a_3295_,
                    v_a_3296_,
                    v_a_3297_,
                    v_a_3298_,
                );
                if leanh::lean_obj_tag(v___x_3302_) == 0 {
                    v_isSharedCheck_3310_ = (!leanh::lean_is_exclusive(v___x_3302_)) as u8;
                    if v_isSharedCheck_3310_ == 0 {
                        v_unused_3311_ = leanh::lean_ctor_get(v___x_3302_, 0);
                        leanh::lean_dec(v_unused_3311_);
                        v___x_3304_ = v___x_3302_;
                        v_isShared_3305_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3302_);
                        v___x_3304_ = leanh::lean_box(0);
                        v_isShared_3305_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3301_);
                    v_a_3312_ = leanh::lean_ctor_get(v___x_3302_, 0);
                    v_isSharedCheck_3319_ = (!leanh::lean_is_exclusive(v___x_3302_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3314_ = v___x_3302_;
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3312_);
                        leanh::lean_dec(v___x_3302_);
                        v___x_3314_ = leanh::lean_box(0);
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3306_ = lean_st_ref_get(v___x_3301_);
                leanh::lean_dec(v___x_3301_);
                if v_isShared_3305_ == 0 {
                    leanh::lean_ctor_set(v___x_3304_, 0, v___x_3306_);
                    v___x_3308_ = v___x_3304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
                    v___x_3308_ = v_reuseFailAlloc_3309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3308_;
            }
            3 => {
                if v_isShared_3315_ == 0 {
                    v___x_3317_ = v___x_3314_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
                    v___x_3317_ = v_reuseFailAlloc_3318_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_getMVarDependencies___boxed(
    mut v_e_3320_: *mut leanh::LeanObject,
    mut v_includeDelayed_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
    mut v_a_3323_: *mut leanh::LeanObject,
    mut v_a_3324_: *mut leanh::LeanObject,
    mut v_a_3325_: *mut leanh::LeanObject,
    mut v_a_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeDelayed_boxed_3327_: u8 = 0;
    let mut v_res_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3327_ = (leanh::lean_unbox(v_includeDelayed_3321_) as u8);
    v_res_3328_ = l_Lean_Expr_getMVarDependencies(
        v_e_3320_,
        v_includeDelayed_boxed_3327_,
        v_a_3322_,
        v_a_3323_,
        v_a_3324_,
        v_a_3325_,
    );
    leanh::lean_dec(v_a_3325_);
    leanh::lean_dec_ref(v_a_3324_);
    leanh::lean_dec(v_a_3323_);
    leanh::lean_dec_ref(v_a_3322_);
    return v_res_3328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CollectMVars(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CollectMVars(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CollectMVars(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CollectMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CollectMVars(builtin);
}