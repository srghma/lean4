// Lean compiler output
// Module: Lean.Meta.CollectMVars
// Imports: Lean.Util.CollectMVars Lean.Meta.Basic
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Meta_getMVars___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getMVars___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_getMVars___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getMVars___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getMVars___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_getMVars___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getMVars___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_getMVars___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getMVars___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
    mut v_e_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_unused_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = l_Lean_Expr_hasMVar(v_e_1665_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1669_, 0, v_e_1665_);
                    return v___x_1669_;
                } else {
                    v___x_1670_ = lean_st_ref_get(v___y_1666_);
                    v_mctx_1671_ = lean_ctor_get(v___x_1670_, 0);
                    lean_inc_ref(v_mctx_1671_);
                    lean_dec(v___x_1670_);
                    v___x_1672_ = l_Lean_instantiateMVarsCore(v_mctx_1671_, v_e_1665_);
                    v_fst_1673_ = lean_ctor_get(v___x_1672_, 0);
                    lean_inc(v_fst_1673_);
                    v_snd_1674_ = lean_ctor_get(v___x_1672_, 1);
                    lean_inc(v_snd_1674_);
                    lean_dec_ref(v___x_1672_);
                    v___x_1675_ = lean_st_ref_take(v___y_1666_);
                    v_cache_1676_ = lean_ctor_get(v___x_1675_, 1);
                    v_zetaDeltaFVarIds_1677_ = lean_ctor_get(v___x_1675_, 2);
                    v_postponed_1678_ = lean_ctor_get(v___x_1675_, 3);
                    v_diag_1679_ = lean_ctor_get(v___x_1675_, 4);
                    v_isSharedCheck_1688_ = (!lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v_unused_1689_ = lean_ctor_get(v___x_1675_, 0);
                        lean_dec(v_unused_1689_);
                        v___x_1681_ = v___x_1675_;
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1679_);
                        lean_inc(v_postponed_1678_);
                        lean_inc(v_zetaDeltaFVarIds_1677_);
                        lean_inc(v_cache_1676_);
                        lean_dec(v___x_1675_);
                        v___x_1681_ = lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1682_ == 0 {
                    lean_ctor_set(v___x_1681_, 0, v_snd_1674_);
                    v___x_1684_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_snd_1674_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_cache_1676_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_zetaDeltaFVarIds_1677_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_postponed_1678_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_diag_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1685_ = lean_st_ref_set(v___y_1666_, v___x_1684_);
                v___x_1686_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1686_, 0, v_fst_1673_);
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg___boxed(
    mut v_e_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
        v_e_1690_,
        v___y_1691_,
    );
    lean_dec(v___y_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(
    mut v_e_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
        v_e_1694_,
        v___y_1697_,
    );
    return v___x_1701_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___boxed(
    mut v_e_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1709_: *mut LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0(
        v_e_1702_,
        v___y_1703_,
        v___y_1704_,
        v___y_1705_,
        v___y_1706_,
        v___y_1707_,
    );
    lean_dec(v___y_1707_);
    lean_dec_ref(v___y_1706_);
    lean_dec(v___y_1705_);
    lean_dec_ref(v___y_1704_);
    lean_dec(v___y_1703_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(
    mut v_mvarId_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = lean_st_ref_get(v___y_1711_);
    v_mctx_1714_ = lean_ctor_get(v___x_1713_, 0);
    lean_inc_ref(v_mctx_1714_);
    lean_dec(v___x_1713_);
    v___x_1715_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1714_, v_mvarId_1710_);
    lean_dec_ref(v_mctx_1714_);
    v___x_1716_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg___boxed(
    mut v_mvarId_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_res_1720_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(
            v_mvarId_1717_,
            v___y_1718_,
        );
    lean_dec(v___y_1718_);
    lean_dec(v_mvarId_1717_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(
    mut v_mvarId_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1728_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(
            v_mvarId_1721_,
            v___y_1724_,
        );
    return v___x_1728_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___boxed(
    mut v_mvarId_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
    mut v___y_1733_: *mut LeanObject,
    mut v___y_1734_: *mut LeanObject,
    mut v___y_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1736_: *mut LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1(
        v_mvarId_1729_,
        v___y_1730_,
        v___y_1731_,
        v___y_1732_,
        v___y_1733_,
        v___y_1734_,
    );
    lean_dec(v___y_1734_);
    lean_dec_ref(v___y_1733_);
    lean_dec(v___y_1732_);
    lean_dec_ref(v___y_1731_);
    lean_dec(v___y_1730_);
    lean_dec(v_mvarId_1729_);
    return v_res_1736_;
}
pub unsafe fn l_Lean_Meta_collectMVars(
    mut v_e_1737_: *mut LeanObject,
    mut v_a_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v_a_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_collectMVars_spec__0___redArg(
                        v_e_1737_, v_a_1740_,
                    );
                if lean_obj_tag(v___x_1744_) == 0 {
                    v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
                    lean_inc(v_a_1745_);
                    lean_dec_ref_known(v___x_1744_, 1);
                    v___x_1746_ = lean_st_ref_get(v_a_1738_);
                    v_result_1747_ = lean_ctor_get(v___x_1746_, 1);
                    lean_inc_ref(v_result_1747_);
                    v___x_1748_ = l_Lean_Expr_collectMVars(v___x_1746_, v_a_1745_);
                    lean_inc_ref(v___x_1748_);
                    v___x_1749_ = lean_st_ref_set(v_a_1738_, v___x_1748_);
                    v_result_1750_ = lean_ctor_get(v___x_1748_, 1);
                    lean_inc_ref(v_result_1750_);
                    lean_dec_ref(v___x_1748_);
                    v___x_1765_ = lean_array_get_size(v_result_1747_);
                    lean_dec_ref(v_result_1747_);
                    v___x_1766_ = lean_unsigned_to_nat(0);
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
                    v_a_1769_ = lean_ctor_get(v___x_1744_, 0);
                    v_isSharedCheck_1776_ = (!lean_is_exclusive(v___x_1744_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1771_ = v___x_1744_;
                        v_isShared_1772_ = v_isSharedCheck_1776_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1769_);
                        lean_dec(v___x_1744_);
                        v___x_1771_ = lean_box(0);
                        v_isShared_1772_ = v_isSharedCheck_1776_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1754_ =
                    l_Array_toSubarray___redArg(v_result_1750_, v_lower_1752_, v_upper_1753_);
                v___x_1755_ = lean_box(0);
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
                if lean_obj_tag(v___x_1756_) == 0 {
                    v_isSharedCheck_1763_ = (!lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1763_ == 0 {
                        v_unused_1764_ = lean_ctor_get(v___x_1756_, 0);
                        lean_dec(v_unused_1764_);
                        v___x_1758_ = v___x_1756_;
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_1756_);
                        v___x_1758_ = lean_box(0);
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
                    lean_ctor_set(v___x_1758_, 0, v___x_1755_);
                    v___x_1761_ = v___x_1758_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1755_);
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
                    v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
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
    mut v_a_1777_: *mut LeanObject,
    mut v_b_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1785_ = lean_ctor_get(v_a_1777_, 0);
                v_start_1786_ = lean_ctor_get(v_a_1777_, 1);
                v_stop_1787_ = lean_ctor_get(v_a_1777_, 2);
                v_isSharedCheck_1816_ = (!lean_is_exclusive(v_a_1777_)) as u8;
                if v_isSharedCheck_1816_ == 0 {
                    v___x_1789_ = v_a_1777_;
                    v_isShared_1790_ = v_isSharedCheck_1816_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_1787_);
                    lean_inc(v_start_1786_);
                    lean_inc(v_array_1785_);
                    lean_dec(v_a_1777_);
                    v___x_1789_ = lean_box(0);
                    v_isShared_1790_ = v_isSharedCheck_1816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1791_ = lean_nat_dec_lt(v_start_1786_, v_stop_1787_);
                if v___x_1791_ == 0 {
                    lean_del_object(v___x_1789_);
                    lean_dec(v_stop_1787_);
                    lean_dec(v_start_1786_);
                    lean_dec_ref(v_array_1785_);
                    v___x_1792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1792_, 0, v_b_1778_);
                    return v___x_1792_;
                } else {
                    v___x_1793_ = lean_array_fget_borrowed(v_array_1785_, v_start_1786_);
                    v___x_1794_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_collectMVars_spec__1___redArg(v___x_1793_, v___y_1781_);
                    if lean_obj_tag(v___x_1794_) == 0 {
                        v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
                        lean_inc(v_a_1795_);
                        lean_dec_ref_known(v___x_1794_, 1);
                        v___x_1796_ = lean_box(0);
                        v___x_1797_ = lean_unsigned_to_nat(1);
                        v___x_1798_ = lean_nat_add(v_start_1786_, v___x_1797_);
                        lean_dec(v_start_1786_);
                        if v_isShared_1790_ == 0 {
                            lean_ctor_set(v___x_1789_, 1, v___x_1798_);
                            v___x_1800_ = v___x_1789_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_array_1785_);
                            lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1798_);
                            lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_stop_1787_);
                            v___x_1800_ = v_reuseFailAlloc_1807_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1789_);
                        lean_dec(v_stop_1787_);
                        lean_dec(v_start_1786_);
                        lean_dec_ref(v_array_1785_);
                        v_a_1808_ = lean_ctor_get(v___x_1794_, 0);
                        v_isSharedCheck_1815_ = (!lean_is_exclusive(v___x_1794_)) as u8;
                        if v_isSharedCheck_1815_ == 0 {
                            v___x_1810_ = v___x_1794_;
                            v_isShared_1811_ = v_isSharedCheck_1815_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1808_);
                            lean_dec(v___x_1794_);
                            v___x_1810_ = lean_box(0);
                            v_isShared_1811_ = v_isSharedCheck_1815_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1795_) == 0 {
                    v_a_1777_ = v___x_1800_;
                    v_b_1778_ = v___x_1796_;
                    state = 0;
                    continue;
                } else {
                    v_val_1802_ = lean_ctor_get(v_a_1795_, 0);
                    lean_inc(v_val_1802_);
                    lean_dec_ref_known(v_a_1795_, 1);
                    v_mvarIdPending_1803_ = lean_ctor_get(v_val_1802_, 1);
                    lean_inc(v_mvarIdPending_1803_);
                    lean_dec(v_val_1802_);
                    v___x_1804_ = l_Lean_mkMVar(v_mvarIdPending_1803_);
                    v___x_1805_ = l_Lean_Meta_collectMVars(
                        v___x_1804_,
                        v___y_1779_,
                        v___y_1780_,
                        v___y_1781_,
                        v___y_1782_,
                        v___y_1783_,
                    );
                    if lean_obj_tag(v___x_1805_) == 0 {
                        lean_dec_ref_known(v___x_1805_, 1);
                        v_a_1777_ = v___x_1800_;
                        v_b_1778_ = v___x_1796_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___x_1800_);
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
                    v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
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
    mut v_a_1817_: *mut LeanObject,
    mut v_b_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1825_: *mut LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2___redArg(
        v_a_1817_,
        v_b_1818_,
        v___y_1819_,
        v___y_1820_,
        v___y_1821_,
        v___y_1822_,
        v___y_1823_,
    );
    lean_dec(v___y_1823_);
    lean_dec_ref(v___y_1822_);
    lean_dec(v___y_1821_);
    lean_dec_ref(v___y_1820_);
    lean_dec(v___y_1819_);
    return v_res_1825_;
}
pub unsafe fn l_Lean_Meta_collectMVars___boxed(
    mut v_e_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
    mut v_a_1828_: *mut LeanObject,
    mut v_a_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1833_: *mut LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_Meta_collectMVars(
        v_e_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_,
    );
    lean_dec(v_a_1831_);
    lean_dec_ref(v_a_1830_);
    lean_dec(v_a_1829_);
    lean_dec_ref(v_a_1828_);
    lean_dec(v_a_1827_);
    return v_res_1833_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_collectMVars_spec__2(
    mut v_inst_1834_: *mut LeanObject,
    mut v_R_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_b_1837_: *mut LeanObject,
    mut v_c_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1846_: *mut LeanObject,
    mut v_R_1847_: *mut LeanObject,
    mut v_a_1848_: *mut LeanObject,
    mut v_b_1849_: *mut LeanObject,
    mut v_c_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1855_);
    lean_dec_ref(v___y_1854_);
    lean_dec(v___y_1853_);
    lean_dec_ref(v___y_1852_);
    lean_dec(v___y_1851_);
    return v_res_1857_;
}
pub unsafe fn _init_l_Lean_Meta_getMVars___closed__0() -> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1858_ = lean_box(0);
    v___x_1859_ = lean_unsigned_to_nat(16);
    v___x_1860_ = lean_mk_array(v___x_1859_, v___x_1858_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_Meta_getMVars___closed__1() -> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__0_once),
        _init_l_Lean_Meta_getMVars___closed__0,
    );
    v___x_1862_ = lean_unsigned_to_nat(0);
    v___x_1863_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Lean_Meta_getMVars___closed__3() -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lean_Meta_getMVars___closed__2;
    v___x_1867_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_getMVars___closed__1_once),
        _init_l_Lean_Meta_getMVars___closed__1,
    );
    v___x_1868_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    lean_ctor_set(v___x_1868_, 1, v___x_1866_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_Meta_getMVars(
    mut v_e_1869_: *mut LeanObject,
    mut v_a_1870_: *mut LeanObject,
    mut v_a_1871_: *mut LeanObject,
    mut v_a_1872_: *mut LeanObject,
    mut v_a_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_unused_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1875_ = lean_obj_once(
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
                if lean_obj_tag(v___x_1877_) == 0 {
                    v_isSharedCheck_1886_ = (!lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v_unused_1887_ = lean_ctor_get(v___x_1877_, 0);
                        lean_dec(v_unused_1887_);
                        v___x_1879_ = v___x_1877_;
                        v_isShared_1880_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1877_);
                        v___x_1879_ = lean_box(0);
                        v_isShared_1880_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1876_);
                    v_a_1888_ = lean_ctor_get(v___x_1877_, 0);
                    v_isSharedCheck_1895_ = (!lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1895_ == 0 {
                        v___x_1890_ = v___x_1877_;
                        v_isShared_1891_ = v_isSharedCheck_1895_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1888_);
                        lean_dec(v___x_1877_);
                        v___x_1890_ = lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1895_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1881_ = lean_st_ref_get(v___x_1876_);
                lean_dec(v___x_1876_);
                v_result_1882_ = lean_ctor_get(v___x_1881_, 1);
                lean_inc_ref(v_result_1882_);
                lean_dec(v___x_1881_);
                if v_isShared_1880_ == 0 {
                    lean_ctor_set(v___x_1879_, 0, v_result_1882_);
                    v___x_1884_ = v___x_1879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_result_1882_);
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
                    v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
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
    mut v_e_1896_: *mut LeanObject,
    mut v_a_1897_: *mut LeanObject,
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_Meta_getMVars(v_e_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
    lean_dec(v_a_1900_);
    lean_dec_ref(v_a_1899_);
    lean_dec(v_a_1898_);
    lean_dec_ref(v_a_1897_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_1903_: *mut LeanObject,
    mut v_i_1904_: *mut LeanObject,
    mut v_k_1905_: *mut LeanObject,
) -> u8 {
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v_k_x27_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1906_ = lean_array_get_size(v_keys_1903_);
                v___x_1907_ = lean_nat_dec_lt(v_i_1904_, v___x_1906_);
                if v___x_1907_ == 0 {
                    lean_dec(v_i_1904_);
                    return v___x_1907_;
                } else {
                    v_k_x27_1908_ = lean_array_fget_borrowed(v_keys_1903_, v_i_1904_);
                    v___x_1909_ = l_Lean_instBEqMVarId_beq(v_k_1905_, v_k_x27_1908_);
                    if v___x_1909_ == 0 {
                        v___x_1910_ = lean_unsigned_to_nat(1);
                        v___x_1911_ = lean_nat_add(v_i_1904_, v___x_1910_);
                        lean_dec(v_i_1904_);
                        v_i_1904_ = v___x_1911_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_1904_);
                        return v___x_1909_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_1913_: *mut LeanObject,
    mut v_i_1914_: *mut LeanObject,
    mut v_k_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1916_: u8 = 0;
    let mut v_r_1917_: *mut LeanObject = core::ptr::null_mut();
    v_res_1916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1913_, v_i_1914_, v_k_1915_);
    lean_dec(v_k_1915_);
    lean_dec_ref(v_keys_1913_);
    v_r_1917_ = lean_box((v_res_1916_) as usize);
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
    v___x_1922_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1923_ = lean_usize_sub(v___x_1922_, v___x_1921_);
    return v___x_1923_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(
    mut v_x_1924_: *mut LeanObject,
    mut v_x_1925_: usize,
    mut v_x_1926_: *mut LeanObject,
) -> u8 {
    let mut v_es_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: usize = 0;
    let mut v___x_1931_: usize = 0;
    let mut v_j_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v_node_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: usize = 0;
    let mut v___x_1939_: u8 = 0;
    let mut v_ks_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1924_) == 0 {
                    v_es_1927_ = lean_ctor_get(v_x_1924_, 0);
                    v___x_1928_ = lean_box(2);
                    v___x_1929_ = 5usize;
                    v___x_1930_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1931_ = lean_usize_land(v_x_1925_, v___x_1930_);
                    v_j_1932_ = lean_usize_to_nat(v___x_1931_);
                    v___x_1933_ = lean_array_get_borrowed(v___x_1928_, v_es_1927_, v_j_1932_);
                    lean_dec(v_j_1932_);
                    match lean_obj_tag(v___x_1933_) {
                        0 => {
                            v_key_1934_ = lean_ctor_get(v___x_1933_, 0);
                            v___x_1935_ = l_Lean_instBEqMVarId_beq(v_x_1926_, v_key_1934_);
                            return v___x_1935_;
                        }
                        1 => {
                            v_node_1936_ = lean_ctor_get(v___x_1933_, 0);
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
                    v_ks_1940_ = lean_ctor_get(v_x_1924_, 0);
                    v___x_1941_ = lean_unsigned_to_nat(0);
                    v___x_1942_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1940_, v___x_1941_, v_x_1926_);
                    return v___x_1942_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1943_: *mut LeanObject,
    mut v_x_1944_: *mut LeanObject,
    mut v_x_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1309__boxed_1946_: usize = 0;
    let mut v_res_1947_: u8 = 0;
    let mut v_r_1948_: *mut LeanObject = core::ptr::null_mut();
    v_x_1309__boxed_1946_ = lean_unbox_usize(v_x_1944_);
    lean_dec(v_x_1944_);
    v_res_1947_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_1943_, v_x_1309__boxed_1946_, v_x_1945_);
    lean_dec(v_x_1945_);
    lean_dec_ref(v_x_1943_);
    v_r_1948_ = lean_box((v_res_1947_) as usize);
    return v_r_1948_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(
    mut v_x_1949_: *mut LeanObject,
    mut v_x_1950_: *mut LeanObject,
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
    mut v_x_1954_: *mut LeanObject,
    mut v_x_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1956_: u8 = 0;
    let mut v_r_1957_: *mut LeanObject = core::ptr::null_mut();
    v_res_1956_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_1954_, v_x_1955_);
    lean_dec(v_x_1955_);
    lean_dec_ref(v_x_1954_);
    v_r_1957_ = lean_box((v_res_1956_) as usize);
    return v_r_1957_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(
    mut v_mvarId_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1961_ = lean_st_ref_get(v___y_1959_);
    v_mctx_1962_ = lean_ctor_get(v___x_1961_, 0);
    lean_inc_ref(v_mctx_1962_);
    lean_dec(v___x_1961_);
    v_dAssignment_1963_ = lean_ctor_get(v_mctx_1962_, 9);
    lean_inc_ref(v_dAssignment_1963_);
    lean_dec_ref(v_mctx_1962_);
    v___x_1964_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_1963_, v_mvarId_1958_);
    lean_dec_ref(v_dAssignment_1963_);
    v___x_1965_ = lean_box((v___x_1964_) as usize);
    v___x_1966_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1966_, 0, v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg___boxed(
    mut v_mvarId_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_res_1970_ =
        l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(
            v_mvarId_1967_,
            v___y_1968_,
        );
    lean_dec(v___y_1968_);
    lean_dec(v_mvarId_1967_);
    return v_res_1970_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(
    mut v_as_1971_: *mut LeanObject,
    mut v_i_1972_: usize,
    mut v_stop_1973_: usize,
    mut v_b_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: usize = 0;
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v_a_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v_a_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1985_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
                if v___x_1985_ == 0 {
                    v___x_1986_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
                    v___x_1989_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(v___x_1986_, v___y_1976_);
                    if lean_obj_tag(v___x_1989_) == 0 {
                        v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
                        lean_inc(v_a_1990_);
                        lean_dec_ref_known(v___x_1989_, 1);
                        v___x_1991_ = (lean_unbox(v_a_1990_) as u8);
                        lean_dec(v_a_1990_);
                        if v___x_1991_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1981_ = v_b_1974_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_1989_) == 0 {
                            v_a_1992_ = lean_ctor_get(v___x_1989_, 0);
                            lean_inc(v_a_1992_);
                            lean_dec_ref_known(v___x_1989_, 1);
                            v___x_1993_ = (lean_unbox(v_a_1992_) as u8);
                            lean_dec(v_a_1992_);
                            if v___x_1993_ == 0 {
                                v_a_1981_ = v_b_1974_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_1974_);
                            v_a_1994_ = lean_ctor_get(v___x_1989_, 0);
                            v_isSharedCheck_2001_ = (!lean_is_exclusive(v___x_1989_)) as u8;
                            if v_isSharedCheck_2001_ == 0 {
                                v___x_1996_ = v___x_1989_;
                                v_isShared_1997_ = v_isSharedCheck_2001_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1994_);
                                lean_dec(v___x_1989_);
                                v___x_1996_ = lean_box(0);
                                v_isShared_1997_ = v_isSharedCheck_2001_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2002_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2002_, 0, v_b_1974_);
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
                lean_inc(v___x_1986_);
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
                    v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
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
    mut v_as_2003_: *mut LeanObject,
    mut v_i_2004_: *mut LeanObject,
    mut v_stop_2005_: *mut LeanObject,
    mut v_b_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2012_: usize = 0;
    let mut v_stop_boxed_2013_: usize = 0;
    let mut v_res_2014_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2012_ = lean_unbox_usize(v_i_2004_);
    lean_dec(v_i_2004_);
    v_stop_boxed_2013_ = lean_unbox_usize(v_stop_2005_);
    lean_dec(v_stop_2005_);
    v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_as_2003_, v_i_boxed_2012_, v_stop_boxed_2013_, v_b_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
    lean_dec(v___y_2010_);
    lean_dec_ref(v___y_2009_);
    lean_dec(v___y_2008_);
    lean_dec_ref(v___y_2007_);
    lean_dec_ref(v_as_2003_);
    return v_res_2014_;
}
pub unsafe fn l_Lean_Meta_getMVarsNoDelayed(
    mut v_e_2015_: *mut LeanObject,
    mut v_a_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: usize = 0;
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: usize = 0;
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2021_ =
                    l_Lean_Meta_getMVars(v_e_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                if lean_obj_tag(v___x_2021_) == 0 {
                    v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2043_ = (!lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2043_ == 0 {
                        v___x_2024_ = v___x_2021_;
                        v_isShared_2025_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2022_);
                        lean_dec(v___x_2021_);
                        v___x_2024_ = lean_box(0);
                        v_isShared_2025_ = v_isSharedCheck_2043_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2021_;
                }
            }
            1 => {
                v___x_2026_ = lean_unsigned_to_nat(0);
                v___x_2027_ = lean_array_get_size(v_a_2022_);
                v___x_2028_ = l_Lean_Meta_getMVars___closed__2;
                v___x_2029_ = lean_nat_dec_lt(v___x_2026_, v___x_2027_);
                if v___x_2029_ == 0 {
                    lean_dec(v_a_2022_);
                    if v_isShared_2025_ == 0 {
                        lean_ctor_set(v___x_2024_, 0, v___x_2028_);
                        v___x_2031_ = v___x_2024_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2028_);
                        v___x_2031_ = v_reuseFailAlloc_2032_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2033_ = lean_nat_dec_le(v___x_2027_, v___x_2027_);
                    if v___x_2033_ == 0 {
                        if v___x_2029_ == 0 {
                            lean_dec(v_a_2022_);
                            if v_isShared_2025_ == 0 {
                                lean_ctor_set(v___x_2024_, 0, v___x_2028_);
                                v___x_2035_ = v___x_2024_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2028_);
                                v___x_2035_ = v_reuseFailAlloc_2036_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2024_);
                            v___x_2037_ = 0usize;
                            v___x_2038_ = lean_usize_of_nat(v___x_2027_);
                            v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_2022_, v___x_2037_, v___x_2038_, v___x_2028_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                            lean_dec(v_a_2022_);
                            return v___x_2039_;
                        }
                    } else {
                        lean_del_object(v___x_2024_);
                        v___x_2040_ = 0usize;
                        v___x_2041_ = lean_usize_of_nat(v___x_2027_);
                        v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getMVarsNoDelayed_spec__1(v_a_2022_, v___x_2040_, v___x_2041_, v___x_2028_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                        lean_dec(v_a_2022_);
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
    mut v_e_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
    mut v_a_2046_: *mut LeanObject,
    mut v_a_2047_: *mut LeanObject,
    mut v_a_2048_: *mut LeanObject,
    mut v_a_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2050_: *mut LeanObject = core::ptr::null_mut();
    v_res_2050_ =
        l_Lean_Meta_getMVarsNoDelayed(v_e_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
    lean_dec(v_a_2048_);
    lean_dec_ref(v_a_2047_);
    lean_dec(v_a_2046_);
    lean_dec_ref(v_a_2045_);
    return v_res_2050_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(
    mut v_mvarId_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    v___x_2057_ =
        l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___redArg(
            v_mvarId_2051_,
            v___y_2053_,
        );
    return v___x_2057_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0___boxed(
    mut v_mvarId_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2064_: *mut LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0(
        v_mvarId_2058_,
        v___y_2059_,
        v___y_2060_,
        v___y_2061_,
        v___y_2062_,
    );
    lean_dec(v___y_2062_);
    lean_dec_ref(v___y_2061_);
    lean_dec(v___y_2060_);
    lean_dec_ref(v___y_2059_);
    lean_dec(v_mvarId_2058_);
    return v_res_2064_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(
    mut v_00_u03b2_2065_: *mut LeanObject,
    mut v_x_2066_: *mut LeanObject,
    mut v_x_2067_: *mut LeanObject,
) -> u8 {
    let mut v___x_2068_: u8 = 0;
    v___x_2068_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_x_2066_, v_x_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___boxed(
    mut v_00_u03b2_2069_: *mut LeanObject,
    mut v_x_2070_: *mut LeanObject,
    mut v_x_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2072_: u8 = 0;
    let mut v_r_2073_: *mut LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0(v_00_u03b2_2069_, v_x_2070_, v_x_2071_);
    lean_dec(v_x_2071_);
    lean_dec_ref(v_x_2070_);
    v_r_2073_ = lean_box((v_res_2072_) as usize);
    return v_r_2073_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2074_: *mut LeanObject,
    mut v_x_2075_: *mut LeanObject,
    mut v_x_2076_: usize,
    mut v_x_2077_: *mut LeanObject,
) -> u8 {
    let mut v___x_2078_: u8 = 0;
    v___x_2078_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___redArg(v_x_2075_, v_x_2076_, v_x_2077_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2079_: *mut LeanObject,
    mut v_x_2080_: *mut LeanObject,
    mut v_x_2081_: *mut LeanObject,
    mut v_x_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1520__boxed_2083_: usize = 0;
    let mut v_res_2084_: u8 = 0;
    let mut v_r_2085_: *mut LeanObject = core::ptr::null_mut();
    v_x_1520__boxed_2083_ = lean_unbox_usize(v_x_2081_);
    lean_dec(v_x_2081_);
    v_res_2084_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1(v_00_u03b2_2079_, v_x_2080_, v_x_1520__boxed_2083_, v_x_2082_);
    lean_dec(v_x_2082_);
    lean_dec_ref(v_x_2080_);
    v_r_2085_ = lean_box((v_res_2084_) as usize);
    return v_r_2085_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2086_: *mut LeanObject,
    mut v_keys_2087_: *mut LeanObject,
    mut v_vals_2088_: *mut LeanObject,
    mut v_heq_2089_: *mut LeanObject,
    mut v_i_2090_: *mut LeanObject,
    mut v_k_2091_: *mut LeanObject,
) -> u8 {
    let mut v___x_2092_: u8 = 0;
    v___x_2092_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2087_, v_i_2090_, v_k_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2093_: *mut LeanObject,
    mut v_keys_2094_: *mut LeanObject,
    mut v_vals_2095_: *mut LeanObject,
    mut v_heq_2096_: *mut LeanObject,
    mut v_i_2097_: *mut LeanObject,
    mut v_k_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2099_: u8 = 0;
    let mut v_r_2100_: *mut LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2093_, v_keys_2094_, v_vals_2095_, v_heq_2096_, v_i_2097_, v_k_2098_);
    lean_dec(v_k_2098_);
    lean_dec_ref(v_vals_2095_);
    lean_dec_ref(v_keys_2094_);
    v_r_2100_ = lean_box((v_res_2099_) as usize);
    return v_r_2100_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(
    mut v_x_2101_: *mut LeanObject,
    mut v_x_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2102_) == 0 {
                    v___x_2109_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2109_, 0, v_x_2101_);
                    return v___x_2109_;
                } else {
                    v_head_2110_ = lean_ctor_get(v_x_2102_, 0);
                    lean_inc(v_head_2110_);
                    v_tail_2111_ = lean_ctor_get(v_x_2102_, 1);
                    lean_inc(v_tail_2111_);
                    lean_dec_ref_known(v_x_2102_, 2);
                    v_type_2112_ = lean_ctor_get(v_head_2110_, 1);
                    lean_inc_ref(v_type_2112_);
                    lean_dec(v_head_2110_);
                    v___x_2113_ = l_Lean_Meta_collectMVars(
                        v_type_2112_,
                        v___y_2103_,
                        v___y_2104_,
                        v___y_2105_,
                        v___y_2106_,
                        v___y_2107_,
                    );
                    if lean_obj_tag(v___x_2113_) == 0 {
                        v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
                        lean_inc(v_a_2114_);
                        lean_dec_ref_known(v___x_2113_, 1);
                        v_x_2101_ = v_a_2114_;
                        v_x_2102_ = v_tail_2111_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_2111_);
                        return v___x_2113_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0___boxed(
    mut v_x_2116_: *mut LeanObject,
    mut v_x_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
    mut v___y_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2124_: *mut LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_x_2116_, v_x_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    lean_dec(v___y_2122_);
    lean_dec_ref(v___y_2121_);
    lean_dec(v___y_2120_);
    lean_dec_ref(v___y_2119_);
    lean_dec(v___y_2118_);
    return v_res_2124_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(
    mut v_x_2125_: *mut LeanObject,
    mut v_x_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2126_) == 0 {
                    v___x_2133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2133_, 0, v_x_2125_);
                    return v___x_2133_;
                } else {
                    v_head_2134_ = lean_ctor_get(v_x_2126_, 0);
                    lean_inc(v_head_2134_);
                    v_tail_2135_ = lean_ctor_get(v_x_2126_, 1);
                    lean_inc(v_tail_2135_);
                    lean_dec_ref_known(v_x_2126_, 2);
                    v_type_2140_ = lean_ctor_get(v_head_2134_, 1);
                    lean_inc_ref(v_type_2140_);
                    v_ctors_2141_ = lean_ctor_get(v_head_2134_, 2);
                    lean_inc(v_ctors_2141_);
                    lean_dec(v_head_2134_);
                    v___x_2142_ = l_Lean_Meta_collectMVars(
                        v_type_2140_,
                        v___y_2127_,
                        v___y_2128_,
                        v___y_2129_,
                        v___y_2130_,
                        v___y_2131_,
                    );
                    if lean_obj_tag(v___x_2142_) == 0 {
                        v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
                        lean_inc(v_a_2143_);
                        lean_dec_ref_known(v___x_2142_, 1);
                        v___x_2144_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__0(v_a_2143_, v_ctors_2141_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
                        v___y_2137_ = v___x_2144_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_ctors_2141_);
                        v___y_2137_ = v___x_2142_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_2137_) == 0 {
                    v_a_2138_ = lean_ctor_get(v___y_2137_, 0);
                    lean_inc(v_a_2138_);
                    lean_dec_ref_known(v___y_2137_, 1);
                    v_x_2125_ = v_a_2138_;
                    v_x_2126_ = v_tail_2135_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_2135_);
                    return v___y_2137_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2___boxed(
    mut v_x_2145_: *mut LeanObject,
    mut v_x_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2153_: *mut LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_x_2145_, v_x_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
    lean_dec(v___y_2151_);
    lean_dec_ref(v___y_2150_);
    lean_dec(v___y_2149_);
    lean_dec_ref(v___y_2148_);
    lean_dec(v___y_2147_);
    return v_res_2153_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(
    mut v_x_2154_: *mut LeanObject,
    mut v_x_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2155_) == 0 {
                    v___x_2162_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2162_, 0, v_x_2154_);
                    return v___x_2162_;
                } else {
                    v_head_2163_ = lean_ctor_get(v_x_2155_, 0);
                    lean_inc(v_head_2163_);
                    v_tail_2164_ = lean_ctor_get(v_x_2155_, 1);
                    lean_inc(v_tail_2164_);
                    lean_dec_ref_known(v_x_2155_, 2);
                    v_toConstantVal_2169_ = lean_ctor_get(v_head_2163_, 0);
                    lean_inc_ref(v_toConstantVal_2169_);
                    v_value_2170_ = lean_ctor_get(v_head_2163_, 1);
                    lean_inc_ref(v_value_2170_);
                    lean_dec(v_head_2163_);
                    v_type_2171_ = lean_ctor_get(v_toConstantVal_2169_, 2);
                    lean_inc_ref(v_type_2171_);
                    lean_dec_ref(v_toConstantVal_2169_);
                    v___x_2172_ = l_Lean_Meta_collectMVars(
                        v_type_2171_,
                        v___y_2156_,
                        v___y_2157_,
                        v___y_2158_,
                        v___y_2159_,
                        v___y_2160_,
                    );
                    if lean_obj_tag(v___x_2172_) == 0 {
                        lean_dec_ref_known(v___x_2172_, 1);
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
                        lean_dec_ref(v_value_2170_);
                        v___y_2166_ = v___x_2172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_2166_) == 0 {
                    v_a_2167_ = lean_ctor_get(v___y_2166_, 0);
                    lean_inc(v_a_2167_);
                    lean_dec_ref_known(v___y_2166_, 1);
                    v_x_2154_ = v_a_2167_;
                    v_x_2155_ = v_tail_2164_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_2164_);
                    return v___y_2166_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1___boxed(
    mut v_x_2174_: *mut LeanObject,
    mut v_x_2175_: *mut LeanObject,
    mut v___y_2176_: *mut LeanObject,
    mut v___y_2177_: *mut LeanObject,
    mut v___y_2178_: *mut LeanObject,
    mut v___y_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2182_: *mut LeanObject = core::ptr::null_mut();
    v_res_2182_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_x_2174_, v_x_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
    lean_dec(v___y_2180_);
    lean_dec_ref(v___y_2179_);
    lean_dec(v___y_2178_);
    lean_dec_ref(v___y_2177_);
    lean_dec(v___y_2176_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(
    mut v_d_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
    mut v___y_2189_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_d_2183_) {
        0 => {
            let mut v_val_2191_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2192_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_2193_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
            v_val_2191_ = lean_ctor_get(v_d_2183_, 0);
            lean_inc_ref(v_val_2191_);
            lean_dec_ref_known(v_d_2183_, 1);
            v_toConstantVal_2192_ = lean_ctor_get(v_val_2191_, 0);
            lean_inc_ref(v_toConstantVal_2192_);
            lean_dec_ref(v_val_2191_);
            v_type_2193_ = lean_ctor_get(v_toConstantVal_2192_, 2);
            lean_inc_ref(v_type_2193_);
            lean_dec_ref(v_toConstantVal_2192_);
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
            let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
            v___x_2195_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_2195_, 0, v_a_2184_);
            return v___x_2195_;
        }
        5 => {
            let mut v_defns_2196_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
            v_defns_2196_ = lean_ctor_get(v_d_2183_, 0);
            lean_inc(v_defns_2196_);
            lean_dec_ref_known(v_d_2183_, 1);
            v___x_2197_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__1(v_a_2184_, v_defns_2196_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
            return v___x_2197_;
        }
        6 => {
            let mut v_types_2198_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
            v_types_2198_ = lean_ctor_get(v_d_2183_, 2);
            lean_inc(v_types_2198_);
            lean_dec_ref_known(v_d_2183_, 3);
            v___x_2199_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0_spec__2(v_a_2184_, v_types_2198_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
            return v___x_2199_;
        }
        _ => {
            let mut v_val_2200_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2201_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_2202_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_2203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
            v_val_2200_ = lean_ctor_get(v_d_2183_, 0);
            lean_inc_ref(v_val_2200_);
            lean_dec(v_d_2183_);
            v_toConstantVal_2201_ = lean_ctor_get(v_val_2200_, 0);
            lean_inc_ref(v_toConstantVal_2201_);
            v_value_2202_ = lean_ctor_get(v_val_2200_, 1);
            lean_inc_ref(v_value_2202_);
            lean_dec_ref(v_val_2200_);
            v_type_2203_ = lean_ctor_get(v_toConstantVal_2201_, 2);
            lean_inc_ref(v_type_2203_);
            lean_dec_ref(v_toConstantVal_2201_);
            v___x_2204_ = l_Lean_Meta_collectMVars(
                v_type_2203_,
                v___y_2185_,
                v___y_2186_,
                v___y_2187_,
                v___y_2188_,
                v___y_2189_,
            );
            if lean_obj_tag(v___x_2204_) == 0 {
                let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_2204_, 1);
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
                lean_dec_ref(v_value_2202_);
                return v___x_2204_;
            }
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0___boxed(
    mut v_d_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2214_: *mut LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_Declaration_foldExprM___at___00Lean_Meta_collectMVarsAtDecl_spec__0(
        v_d_2206_,
        v_a_2207_,
        v___y_2208_,
        v___y_2209_,
        v___y_2210_,
        v___y_2211_,
        v___y_2212_,
    );
    lean_dec(v___y_2212_);
    lean_dec_ref(v___y_2211_);
    lean_dec(v___y_2210_);
    lean_dec_ref(v___y_2209_);
    lean_dec(v___y_2208_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_Meta_collectMVarsAtDecl(
    mut v_d_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
    mut v_a_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
    mut v_a_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    v___x_2222_ = lean_box(0);
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
    mut v_d_2224_: *mut LeanObject,
    mut v_a_2225_: *mut LeanObject,
    mut v_a_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
    mut v_a_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_Meta_collectMVarsAtDecl(
        v_d_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_,
    );
    lean_dec(v_a_2229_);
    lean_dec_ref(v_a_2228_);
    lean_dec(v_a_2227_);
    lean_dec_ref(v_a_2226_);
    lean_dec(v_a_2225_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_Meta_getMVarsAtDecl(
    mut v_d_2232_: *mut LeanObject,
    mut v_a_2233_: *mut LeanObject,
    mut v_a_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2243_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_unused_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2254_: u8 = 0;
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2238_ = lean_obj_once(
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
                if lean_obj_tag(v___x_2240_) == 0 {
                    v_isSharedCheck_2249_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v_unused_2250_ = lean_ctor_get(v___x_2240_, 0);
                        lean_dec(v_unused_2250_);
                        v___x_2242_ = v___x_2240_;
                        v_isShared_2243_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2240_);
                        v___x_2242_ = lean_box(0);
                        v_isShared_2243_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2239_);
                    v_a_2251_ = lean_ctor_get(v___x_2240_, 0);
                    v_isSharedCheck_2258_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2258_ == 0 {
                        v___x_2253_ = v___x_2240_;
                        v_isShared_2254_ = v_isSharedCheck_2258_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2251_);
                        lean_dec(v___x_2240_);
                        v___x_2253_ = lean_box(0);
                        v_isShared_2254_ = v_isSharedCheck_2258_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2244_ = lean_st_ref_get(v___x_2239_);
                lean_dec(v___x_2239_);
                v_result_2245_ = lean_ctor_get(v___x_2244_, 1);
                lean_inc_ref(v_result_2245_);
                lean_dec(v___x_2244_);
                if v_isShared_2243_ == 0 {
                    lean_ctor_set(v___x_2242_, 0, v_result_2245_);
                    v___x_2247_ = v___x_2242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_result_2245_);
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
                    v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
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
    mut v_d_2259_: *mut LeanObject,
    mut v_a_2260_: *mut LeanObject,
    mut v_a_2261_: *mut LeanObject,
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2265_: *mut LeanObject = core::ptr::null_mut();
    v_res_2265_ = l_Lean_Meta_getMVarsAtDecl(v_d_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
    lean_dec(v_a_2263_);
    lean_dec_ref(v_a_2262_);
    lean_dec(v_a_2261_);
    lean_dec_ref(v_a_2260_);
    return v_res_2265_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(
    mut v_mvarId_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: u8 = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    v___x_2269_ = lean_st_ref_get(v___y_2267_);
    v_mctx_2270_ = lean_ctor_get(v___x_2269_, 0);
    lean_inc_ref(v_mctx_2270_);
    lean_dec(v___x_2269_);
    v_dAssignment_2271_ = lean_ctor_get(v_mctx_2270_, 9);
    lean_inc_ref(v_dAssignment_2271_);
    lean_dec_ref(v_mctx_2270_);
    v___x_2272_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_2271_, v_mvarId_2266_);
    lean_dec_ref(v_dAssignment_2271_);
    v___x_2273_ = lean_box((v___x_2272_) as usize);
    v___x_2274_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2274_, 0, v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg___boxed(
    mut v_mvarId_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2278_: *mut LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_2275_, v___y_2276_);
    lean_dec(v___y_2276_);
    lean_dec(v_mvarId_2275_);
    return v_res_2278_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(
    mut v_a_2279_: *mut LeanObject,
    mut v_x_2280_: *mut LeanObject,
) -> u8 {
    let mut v___x_2281_: u8 = 0;
    let mut v_key_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2280_) == 0 {
                    v___x_2281_ = 0;
                    return v___x_2281_;
                } else {
                    v_key_2282_ = lean_ctor_get(v_x_2280_, 0);
                    v_tail_2283_ = lean_ctor_get(v_x_2280_, 2);
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
    mut v_a_2286_: *mut LeanObject,
    mut v_x_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2288_: u8 = 0;
    let mut v_r_2289_: *mut LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_2286_, v_x_2287_);
    lean_dec(v_x_2287_);
    lean_dec(v_a_2286_);
    v_r_2289_ = lean_box((v_res_2288_) as usize);
    return v_r_2289_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(
    mut v_x_2290_: *mut LeanObject,
    mut v_x_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2291_) == 0 {
                    return v_x_2290_;
                } else {
                    v_key_2292_ = lean_ctor_get(v_x_2291_, 0);
                    v_value_2293_ = lean_ctor_get(v_x_2291_, 1);
                    v_tail_2294_ = lean_ctor_get(v_x_2291_, 2);
                    v_isSharedCheck_2317_ = (!lean_is_exclusive(v_x_2291_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2296_ = v_x_2291_;
                        v_isShared_2297_ = v_isSharedCheck_2317_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2294_);
                        lean_inc(v_value_2293_);
                        lean_inc(v_key_2292_);
                        lean_dec(v_x_2291_);
                        v___x_2296_ = lean_box(0);
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
                lean_inc(v___x_2311_);
                if v_isShared_2297_ == 0 {
                    lean_ctor_set(v___x_2296_, 2, v___x_2311_);
                    v___x_2313_ = v___x_2296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_key_2292_);
                    lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_value_2293_);
                    lean_ctor_set(v_reuseFailAlloc_2316_, 2, v___x_2311_);
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
    mut v_i_2318_: *mut LeanObject,
    mut v_source_2319_: *mut LeanObject,
    mut v_target_2320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v_es_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2321_ = lean_array_get_size(v_source_2319_);
                v___x_2322_ = lean_nat_dec_lt(v_i_2318_, v___x_2321_);
                if v___x_2322_ == 0 {
                    lean_dec_ref(v_source_2319_);
                    lean_dec(v_i_2318_);
                    return v_target_2320_;
                } else {
                    v_es_2323_ = lean_array_fget(v_source_2319_, v_i_2318_);
                    v___x_2324_ = lean_box(0);
                    v_source_2325_ = lean_array_fset(v_source_2319_, v_i_2318_, v___x_2324_);
                    v_target_2326_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_target_2320_, v_es_2323_);
                    v___x_2327_ = lean_unsigned_to_nat(1);
                    v___x_2328_ = lean_nat_add(v_i_2318_, v___x_2327_);
                    lean_dec(v_i_2318_);
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
    mut v_data_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v___x_2331_ = lean_array_get_size(v_data_2330_);
    v___x_2332_ = lean_unsigned_to_nat(2);
    v_nbuckets_2333_ = lean_nat_mul(v___x_2331_, v___x_2332_);
    v___x_2334_ = lean_unsigned_to_nat(0);
    v___x_2335_ = lean_box(0);
    v___x_2336_ = lean_mk_array(v_nbuckets_2333_, v___x_2335_);
    v___x_2337_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v___x_2334_, v_data_2330_, v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(
    mut v_m_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_b_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: u8 = 0;
    let mut v_val_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_unused_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2341_ = lean_ctor_get(v_m_2338_, 0);
                v_buckets_2342_ = lean_ctor_get(v_m_2338_, 1);
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
                    lean_inc_ref(v_buckets_2342_);
                    lean_inc(v_size_2341_);
                    v_isSharedCheck_2378_ = (!lean_is_exclusive(v_m_2338_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v_unused_2379_ = lean_ctor_get(v_m_2338_, 1);
                        lean_dec(v_unused_2379_);
                        v_unused_2380_ = lean_ctor_get(v_m_2338_, 0);
                        lean_dec(v_unused_2380_);
                        v___x_2359_ = v_m_2338_;
                        v_isShared_2360_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2338_);
                        v___x_2359_ = lean_box(0);
                        v_isShared_2360_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2340_);
                    lean_dec(v_a_2339_);
                    return v_m_2338_;
                }
            }
            1 => {
                v___x_2361_ = lean_unsigned_to_nat(1);
                v_size_x27_2362_ = lean_nat_add(v_size_2341_, v___x_2361_);
                lean_dec(v_size_2341_);
                lean_inc(v_bkt_2356_);
                v___x_2363_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2363_, 0, v_a_2339_);
                lean_ctor_set(v___x_2363_, 1, v_b_2340_);
                lean_ctor_set(v___x_2363_, 2, v_bkt_2356_);
                v_buckets_x27_2364_ = lean_array_uset(v_buckets_2342_, v___x_2355_, v___x_2363_);
                v___x_2365_ = lean_unsigned_to_nat(4);
                v___x_2366_ = lean_nat_mul(v_size_x27_2362_, v___x_2365_);
                v___x_2367_ = lean_unsigned_to_nat(3);
                v___x_2368_ = lean_nat_div(v___x_2366_, v___x_2367_);
                lean_dec(v___x_2366_);
                v___x_2369_ = lean_array_get_size(v_buckets_x27_2364_);
                v___x_2370_ = lean_nat_dec_le(v___x_2368_, v___x_2369_);
                lean_dec(v___x_2368_);
                if v___x_2370_ == 0 {
                    v_val_2371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_buckets_x27_2364_);
                    if v_isShared_2360_ == 0 {
                        lean_ctor_set(v___x_2359_, 1, v_val_2371_);
                        lean_ctor_set(v___x_2359_, 0, v_size_x27_2362_);
                        v___x_2373_ = v___x_2359_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_size_x27_2362_);
                        lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_val_2371_);
                        v___x_2373_ = v_reuseFailAlloc_2374_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2360_ == 0 {
                        lean_ctor_set(v___x_2359_, 1, v_buckets_x27_2364_);
                        lean_ctor_set(v___x_2359_, 0, v_size_x27_2362_);
                        v___x_2376_ = v___x_2359_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_size_x27_2362_);
                        lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_buckets_x27_2364_);
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
    mut v_as_2382_: *mut LeanObject,
    mut v_sz_2383_: usize,
    mut v_i_2384_: usize,
    mut v_b_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: usize = 0;
    let mut v___x_2395_: usize = 0;
    let mut v___x_2397_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: u8 = 0;
    let mut v_a_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v_a_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2397_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
                if v___x_2397_ == 0 {
                    v___x_2398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2398_, 0, v_b_2385_);
                    return v___x_2398_;
                } else {
                    v_a_2399_ = lean_array_uget_borrowed(v_as_2382_, v_i_2384_);
                    if v_includeDelayed_2381_ == 0 {
                        v___x_2403_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_a_2399_, v___y_2388_);
                        if lean_obj_tag(v___x_2403_) == 0 {
                            v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
                            lean_inc(v_a_2404_);
                            lean_dec_ref_known(v___x_2403_, 1);
                            v___x_2405_ = (lean_unbox(v_a_2404_) as u8);
                            lean_dec(v_a_2404_);
                            if v___x_2405_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v_a_2393_ = v_b_2385_;
                                state = 1;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2403_) == 0 {
                                v_a_2406_ = lean_ctor_get(v___x_2403_, 0);
                                lean_inc(v_a_2406_);
                                lean_dec_ref_known(v___x_2403_, 1);
                                v___x_2407_ = (lean_unbox(v_a_2406_) as u8);
                                lean_dec(v_a_2406_);
                                if v___x_2407_ == 0 {
                                    v_a_2393_ = v_b_2385_;
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_b_2385_);
                                v_a_2408_ = lean_ctor_get(v___x_2403_, 0);
                                v_isSharedCheck_2415_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                                if v_isSharedCheck_2415_ == 0 {
                                    v___x_2410_ = v___x_2403_;
                                    v_isShared_2411_ = v_isSharedCheck_2415_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2408_);
                                    lean_dec(v___x_2403_);
                                    v___x_2410_ = lean_box(0);
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
                v___x_2401_ = lean_box(0);
                lean_inc(v_a_2399_);
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
                    v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
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
    mut v_includeDelayed_2416_: *mut LeanObject,
    mut v_as_2417_: *mut LeanObject,
    mut v_sz_2418_: *mut LeanObject,
    mut v_i_2419_: *mut LeanObject,
    mut v_b_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_2427_: u8 = 0;
    let mut v_sz_boxed_2428_: usize = 0;
    let mut v_i_boxed_2429_: usize = 0;
    let mut v_res_2430_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_2427_ = (lean_unbox(v_includeDelayed_2416_) as u8);
    v_sz_boxed_2428_ = lean_unbox_usize(v_sz_2418_);
    lean_dec(v_sz_2418_);
    v_i_boxed_2429_ = lean_unbox_usize(v_i_2419_);
    lean_dec(v_i_2419_);
    v_res_2430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__2(v_includeDelayed_boxed_2427_, v_as_2417_, v_sz_boxed_2428_, v_i_boxed_2429_, v_b_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
    lean_dec(v___y_2425_);
    lean_dec_ref(v___y_2424_);
    lean_dec(v___y_2423_);
    lean_dec_ref(v___y_2422_);
    lean_dec(v___y_2421_);
    lean_dec_ref(v_as_2417_);
    return v_res_2430_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2436_ = l_Lean_maxRecDepthErrorMessage;
    v___x_2437_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2437_, 0, v___x_2436_);
    return v___x_2437_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2438_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__3);
    v___x_2439_ = l_Lean_MessageData_ofFormat(v___x_2438_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2440_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__4);
    v___x_2441_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__2;
    v___x_2442_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_2442_, 0, v___x_2441_);
    lean_ctor_set(v___x_2442_, 1, v___x_2440_);
    return v___x_2442_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(
    mut v_ref_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    v___x_2445_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___closed__5);
    v___x_2446_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2446_, 0, v_ref_2443_);
    lean_ctor_set(v___x_2446_, 1, v___x_2445_);
    v___x_2447_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2447_, 0, v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg___boxed(
    mut v_ref_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2450_: *mut LeanObject = core::ptr::null_mut();
    v_res_2450_ =
        l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(
            v_ref_2448_,
        );
    return v_res_2450_;
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(
    mut v_mvarId_2451_: *mut LeanObject,
    mut v___y_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    v___x_2454_ = lean_st_ref_get(v___y_2452_);
    v_mctx_2455_ = lean_ctor_get(v___x_2454_, 0);
    lean_inc_ref(v_mctx_2455_);
    lean_dec(v___x_2454_);
    v_eAssignment_2456_ = lean_ctor_get(v_mctx_2455_, 8);
    lean_inc_ref(v_eAssignment_2456_);
    v_dAssignment_2457_ = lean_ctor_get(v_mctx_2455_, 9);
    lean_inc_ref(v_dAssignment_2457_);
    lean_dec_ref(v_mctx_2455_);
    v___x_2458_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_eAssignment_2456_, v_mvarId_2451_);
    lean_dec_ref(v_eAssignment_2456_);
    if v___x_2458_ == 0 {
        let mut v___x_2459_: u8 = 0;
        let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
        v___x_2459_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_getMVarsNoDelayed_spec__0_spec__0___redArg(v_dAssignment_2457_, v_mvarId_2451_);
        lean_dec_ref(v_dAssignment_2457_);
        v___x_2460_ = lean_box((v___x_2459_) as usize);
        v___x_2461_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2461_, 0, v___x_2460_);
        return v___x_2461_;
    } else {
        let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_dAssignment_2457_);
        v___x_2462_ = lean_box((v___x_2458_) as usize);
        v___x_2463_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2463_, 0, v___x_2462_);
        return v___x_2463_;
    }
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg___boxed(
    mut v_mvarId_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
    mut v___y_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2467_: *mut LeanObject = core::ptr::null_mut();
    v_res_2467_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_2464_, v___y_2465_);
    lean_dec(v___y_2465_);
    lean_dec(v_mvarId_2464_);
    return v_res_2467_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(
    mut v_mvarId_2468_: *mut LeanObject,
    mut v___y_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2471_ = lean_st_ref_get(v___y_2469_);
    v_mctx_2472_ = lean_ctor_get(v___x_2471_, 0);
    lean_inc_ref(v_mctx_2472_);
    lean_dec(v___x_2471_);
    v___x_2473_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_2472_, v_mvarId_2468_);
    lean_dec_ref(v_mctx_2472_);
    v___x_2474_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    return v___x_2474_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg___boxed(
    mut v_mvarId_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2478_: *mut LeanObject = core::ptr::null_mut();
    v_res_2478_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_2475_, v___y_2476_);
    lean_dec(v___y_2476_);
    lean_dec(v_mvarId_2475_);
    return v_res_2478_;
}
pub unsafe fn _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0() -> *mut LeanObject
{
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = lean_box(0);
    v___x_2480_ = lean_unsigned_to_nat(16);
    v___x_2481_ = lean_mk_array(v___x_2480_, v___x_2479_);
    return v___x_2481_;
}
pub unsafe fn _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1() -> *mut LeanObject
{
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    v___x_2482_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0),
        core::ptr::addr_of_mut!(l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0_once),
        _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__0,
    );
    v___x_2483_ = lean_unsigned_to_nat(0);
    v___x_2484_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    lean_ctor_set(v___x_2484_, 1, v___x_2482_);
    return v___x_2484_;
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__addMVars(
    mut v_e_2485_: *mut LeanObject,
    mut v_includeDelayed_2486_: u8,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2499_: usize = 0;
    let mut v___x_2500_: usize = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_a_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_a_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2493_ =
                    l_Lean_Meta_getMVars(v_e_2485_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                if lean_obj_tag(v___x_2493_) == 0 {
                    v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
                    lean_inc(v_a_2494_);
                    lean_dec_ref_known(v___x_2493_, 1);
                    v___x_2495_ = lean_st_ref_get(v_a_2487_);
                    v___x_2496_ = lean_unsigned_to_nat(0);
                    v___x_2497_ = lean_obj_once(
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
                    if lean_obj_tag(v___x_2501_) == 0 {
                        v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
                        v_isSharedCheck_2521_ = (!lean_is_exclusive(v___x_2501_)) as u8;
                        if v_isSharedCheck_2521_ == 0 {
                            v___x_2504_ = v___x_2501_;
                            v_isShared_2505_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2502_);
                            lean_dec(v___x_2501_);
                            v___x_2504_ = lean_box(0);
                            v_isShared_2505_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2494_);
                        v_a_2522_ = lean_ctor_get(v___x_2501_, 0);
                        v_isSharedCheck_2529_ = (!lean_is_exclusive(v___x_2501_)) as u8;
                        if v_isSharedCheck_2529_ == 0 {
                            v___x_2524_ = v___x_2501_;
                            v_isShared_2525_ = v_isSharedCheck_2529_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2522_);
                            lean_dec(v___x_2501_);
                            v___x_2524_ = lean_box(0);
                            v_isShared_2525_ = v_isSharedCheck_2529_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_2530_ = lean_ctor_get(v___x_2493_, 0);
                    v_isSharedCheck_2537_ = (!lean_is_exclusive(v___x_2493_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v___x_2532_ = v___x_2493_;
                        v_isShared_2533_ = v_isSharedCheck_2537_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2530_);
                        lean_dec(v___x_2493_);
                        v___x_2532_ = lean_box(0);
                        v_isShared_2533_ = v_isSharedCheck_2537_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2506_ = lean_st_ref_set(v_a_2487_, v_a_2502_);
                v___x_2507_ = lean_array_get_size(v_a_2494_);
                v___x_2508_ = lean_box(0);
                v___x_2509_ = lean_nat_dec_lt(v___x_2496_, v___x_2507_);
                if v___x_2509_ == 0 {
                    lean_dec(v_a_2494_);
                    if v_isShared_2505_ == 0 {
                        lean_ctor_set(v___x_2504_, 0, v___x_2508_);
                        v___x_2511_ = v___x_2504_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2508_);
                        v___x_2511_ = v_reuseFailAlloc_2512_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2513_ = lean_nat_dec_le(v___x_2507_, v___x_2507_);
                    if v___x_2513_ == 0 {
                        if v___x_2509_ == 0 {
                            lean_dec(v_a_2494_);
                            if v_isShared_2505_ == 0 {
                                lean_ctor_set(v___x_2504_, 0, v___x_2508_);
                                v___x_2515_ = v___x_2504_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2508_);
                                v___x_2515_ = v_reuseFailAlloc_2516_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2504_);
                            v___x_2517_ = lean_usize_of_nat(v___x_2507_);
                            v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_2494_, v___x_2500_, v___x_2517_, v___x_2508_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                            lean_dec(v_a_2494_);
                            return v___x_2518_;
                        }
                    } else {
                        lean_del_object(v___x_2504_);
                        v___x_2519_ = lean_usize_of_nat(v___x_2507_);
                        v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_a_2494_, v___x_2500_, v___x_2519_, v___x_2508_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
                        lean_dec(v_a_2494_);
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
                    v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
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
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
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
    mut v_init_2538_: *mut LeanObject,
    mut v_includeDelayed_2539_: u8,
    mut v_as_2540_: *mut LeanObject,
    mut v_sz_2541_: usize,
    mut v_i_2542_: usize,
    mut v_b_2543_: *mut LeanObject,
    mut v___y_2544_: *mut LeanObject,
    mut v___y_2545_: *mut LeanObject,
    mut v___y_2546_: *mut LeanObject,
    mut v___y_2547_: *mut LeanObject,
    mut v___y_2548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v_a_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: usize = 0;
    let mut v___x_2574_: usize = 0;
    let mut v_reuseFailAlloc_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_a_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_unused_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_usize_dec_lt(v_i_2542_, v_sz_2541_);
                if v___x_2550_ == 0 {
                    v___x_2551_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2551_, 0, v_b_2543_);
                    return v___x_2551_;
                } else {
                    v_snd_2552_ = lean_ctor_get(v_b_2543_, 1);
                    v_isSharedCheck_2586_ = (!lean_is_exclusive(v_b_2543_)) as u8;
                    if v_isSharedCheck_2586_ == 0 {
                        v_unused_2587_ = lean_ctor_get(v_b_2543_, 0);
                        lean_dec(v_unused_2587_);
                        v___x_2554_ = v_b_2543_;
                        v_isShared_2555_ = v_isSharedCheck_2586_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2552_);
                        lean_dec(v_b_2543_);
                        v___x_2554_ = lean_box(0);
                        v_isShared_2555_ = v_isSharedCheck_2586_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2556_ = lean_array_uget_borrowed(v_as_2540_, v_i_2542_);
                lean_inc(v_snd_2552_);
                v___x_2557_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_2538_, v_includeDelayed_2539_, v_a_2556_, v_snd_2552_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
                if lean_obj_tag(v___x_2557_) == 0 {
                    v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
                    v_isSharedCheck_2577_ = (!lean_is_exclusive(v___x_2557_)) as u8;
                    if v_isSharedCheck_2577_ == 0 {
                        v___x_2560_ = v___x_2557_;
                        v_isShared_2561_ = v_isSharedCheck_2577_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2558_);
                        lean_dec(v___x_2557_);
                        v___x_2560_ = lean_box(0);
                        v_isShared_2561_ = v_isSharedCheck_2577_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2554_);
                    lean_dec(v_snd_2552_);
                    v_a_2578_ = lean_ctor_get(v___x_2557_, 0);
                    v_isSharedCheck_2585_ = (!lean_is_exclusive(v___x_2557_)) as u8;
                    if v_isSharedCheck_2585_ == 0 {
                        v___x_2580_ = v___x_2557_;
                        v_isShared_2581_ = v_isSharedCheck_2585_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2578_);
                        lean_dec(v___x_2557_);
                        v___x_2580_ = lean_box(0);
                        v_isShared_2581_ = v_isSharedCheck_2585_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2558_) == 0 {
                    v___x_2562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2562_, 0, v_a_2558_);
                    if v_isShared_2555_ == 0 {
                        lean_ctor_set(v___x_2554_, 0, v___x_2562_);
                        v___x_2564_ = v___x_2554_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2562_);
                        lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_snd_2552_);
                        v___x_2564_ = v_reuseFailAlloc_2568_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2560_);
                    lean_dec(v_snd_2552_);
                    v_a_2569_ = lean_ctor_get(v_a_2558_, 0);
                    lean_inc(v_a_2569_);
                    lean_dec_ref_known(v_a_2558_, 1);
                    v___x_2570_ = lean_box(0);
                    if v_isShared_2555_ == 0 {
                        lean_ctor_set(v___x_2554_, 1, v_a_2569_);
                        lean_ctor_set(v___x_2554_, 0, v___x_2570_);
                        v___x_2572_ = v___x_2554_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2570_);
                        lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_a_2569_);
                        v___x_2572_ = v_reuseFailAlloc_2576_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2561_ == 0 {
                    lean_ctor_set(v___x_2560_, 0, v___x_2564_);
                    v___x_2566_ = v___x_2560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
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
                    v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
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
    mut v_as_2589_: *mut LeanObject,
    mut v_sz_2590_: usize,
    mut v_i_2591_: usize,
    mut v_b_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
    mut v___y_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v_reuseFailAlloc_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2626_: u8 = 0;
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_a_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v_unused_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2599_ = lean_usize_dec_lt(v_i_2591_, v_sz_2590_);
                if v___x_2599_ == 0 {
                    v___x_2600_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2600_, 0, v_b_2592_);
                    return v___x_2600_;
                } else {
                    v_snd_2601_ = lean_ctor_get(v_b_2592_, 1);
                    v_isSharedCheck_2639_ = (!lean_is_exclusive(v_b_2592_)) as u8;
                    if v_isSharedCheck_2639_ == 0 {
                        v_unused_2640_ = lean_ctor_get(v_b_2592_, 0);
                        lean_dec(v_unused_2640_);
                        v___x_2603_ = v_b_2592_;
                        v_isShared_2604_ = v_isSharedCheck_2639_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2601_);
                        lean_dec(v_b_2592_);
                        v___x_2603_ = lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2605_ = lean_box(0);
                v_a_2614_ = lean_array_uget_borrowed(v_as_2589_, v_i_2591_);
                if lean_obj_tag(v_a_2614_) == 0 {
                    v_a_2607_ = v_snd_2601_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_2601_);
                    v_val_2615_ = lean_ctor_get(v_a_2614_, 0);
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
                    if lean_obj_tag(v___x_2617_) == 0 {
                        lean_dec_ref_known(v___x_2617_, 1);
                        v___x_2618_ = lean_box(0);
                        v___x_2619_ = 0;
                        v___x_2620_ = l_Lean_LocalDecl_value_x3f(v_val_2615_, v___x_2619_);
                        if lean_obj_tag(v___x_2620_) == 1 {
                            v_val_2621_ = lean_ctor_get(v___x_2620_, 0);
                            lean_inc(v_val_2621_);
                            lean_dec_ref_known(v___x_2620_, 1);
                            v___x_2622_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2621_,
                                v_includeDelayed_2588_,
                                v___y_2593_,
                                v___y_2594_,
                                v___y_2595_,
                                v___y_2596_,
                                v___y_2597_,
                            );
                            if lean_obj_tag(v___x_2622_) == 0 {
                                lean_dec_ref_known(v___x_2622_, 1);
                                v_a_2607_ = v___x_2618_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2603_);
                                v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
                                v_isSharedCheck_2630_ = (!lean_is_exclusive(v___x_2622_)) as u8;
                                if v_isSharedCheck_2630_ == 0 {
                                    v___x_2625_ = v___x_2622_;
                                    v_isShared_2626_ = v_isSharedCheck_2630_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2623_);
                                    lean_dec(v___x_2622_);
                                    v___x_2625_ = lean_box(0);
                                    v_isShared_2626_ = v_isSharedCheck_2630_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2620_);
                            v_a_2607_ = v___x_2618_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2603_);
                        v_a_2631_ = lean_ctor_get(v___x_2617_, 0);
                        v_isSharedCheck_2638_ = (!lean_is_exclusive(v___x_2617_)) as u8;
                        if v_isSharedCheck_2638_ == 0 {
                            v___x_2633_ = v___x_2617_;
                            v_isShared_2634_ = v_isSharedCheck_2638_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2631_);
                            lean_dec(v___x_2617_);
                            v___x_2633_ = lean_box(0);
                            v_isShared_2634_ = v_isSharedCheck_2638_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2604_ == 0 {
                    lean_ctor_set(v___x_2603_, 1, v_a_2607_);
                    lean_ctor_set(v___x_2603_, 0, v___x_2605_);
                    v___x_2609_ = v___x_2603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2605_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_a_2607_);
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
                    v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
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
                    v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
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
    mut v_as_2642_: *mut LeanObject,
    mut v_sz_2643_: usize,
    mut v_i_2644_: usize,
    mut v_b_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: usize = 0;
    let mut v___x_2664_: usize = 0;
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2691_: u8 = 0;
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_unused_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_usize_dec_lt(v_i_2644_, v_sz_2643_);
                if v___x_2652_ == 0 {
                    v___x_2653_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2653_, 0, v_b_2645_);
                    return v___x_2653_;
                } else {
                    v_snd_2654_ = lean_ctor_get(v_b_2645_, 1);
                    v_isSharedCheck_2692_ = (!lean_is_exclusive(v_b_2645_)) as u8;
                    if v_isSharedCheck_2692_ == 0 {
                        v_unused_2693_ = lean_ctor_get(v_b_2645_, 0);
                        lean_dec(v_unused_2693_);
                        v___x_2656_ = v_b_2645_;
                        v_isShared_2657_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2654_);
                        lean_dec(v_b_2645_);
                        v___x_2656_ = lean_box(0);
                        v_isShared_2657_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2658_ = lean_box(0);
                v_a_2667_ = lean_array_uget_borrowed(v_as_2642_, v_i_2644_);
                if lean_obj_tag(v_a_2667_) == 0 {
                    v_a_2660_ = v_snd_2654_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_2654_);
                    v_val_2668_ = lean_ctor_get(v_a_2667_, 0);
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
                    if lean_obj_tag(v___x_2670_) == 0 {
                        lean_dec_ref_known(v___x_2670_, 1);
                        v___x_2671_ = lean_box(0);
                        v___x_2672_ = 0;
                        v___x_2673_ = l_Lean_LocalDecl_value_x3f(v_val_2668_, v___x_2672_);
                        if lean_obj_tag(v___x_2673_) == 1 {
                            v_val_2674_ = lean_ctor_get(v___x_2673_, 0);
                            lean_inc(v_val_2674_);
                            lean_dec_ref_known(v___x_2673_, 1);
                            v___x_2675_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2674_,
                                v_includeDelayed_2641_,
                                v___y_2646_,
                                v___y_2647_,
                                v___y_2648_,
                                v___y_2649_,
                                v___y_2650_,
                            );
                            if lean_obj_tag(v___x_2675_) == 0 {
                                lean_dec_ref_known(v___x_2675_, 1);
                                v_a_2660_ = v___x_2671_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2656_);
                                v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
                                v_isSharedCheck_2683_ = (!lean_is_exclusive(v___x_2675_)) as u8;
                                if v_isSharedCheck_2683_ == 0 {
                                    v___x_2678_ = v___x_2675_;
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2676_);
                                    lean_dec(v___x_2675_);
                                    v___x_2678_ = lean_box(0);
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2673_);
                            v_a_2660_ = v___x_2671_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2656_);
                        v_a_2684_ = lean_ctor_get(v___x_2670_, 0);
                        v_isSharedCheck_2691_ = (!lean_is_exclusive(v___x_2670_)) as u8;
                        if v_isSharedCheck_2691_ == 0 {
                            v___x_2686_ = v___x_2670_;
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2684_);
                            lean_dec(v___x_2670_);
                            v___x_2686_ = lean_box(0);
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2657_ == 0 {
                    lean_ctor_set(v___x_2656_, 1, v_a_2660_);
                    lean_ctor_set(v___x_2656_, 0, v___x_2658_);
                    v___x_2662_ = v___x_2656_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2658_);
                    lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_a_2660_);
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
                    v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
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
                    v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
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
    mut v_init_2694_: *mut LeanObject,
    mut v_includeDelayed_2695_: u8,
    mut v_n_2696_: *mut LeanObject,
    mut v_b_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2707_: usize = 0;
    let mut v___x_2708_: usize = 0;
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v_fst_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_a_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2732_: u8 = 0;
    let mut v_vs_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2736_: usize = 0;
    let mut v___x_2737_: usize = 0;
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v_fst_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2753_: u8 = 0;
    let mut v_a_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2757_: u8 = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_2696_) == 0 {
                    v_cs_2704_ = lean_ctor_get(v_n_2696_, 0);
                    v___x_2705_ = lean_box(0);
                    v___x_2706_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2706_, 0, v___x_2705_);
                    lean_ctor_set(v___x_2706_, 1, v_b_2697_);
                    v_sz_2707_ = lean_array_size(v_cs_2704_);
                    v___x_2708_ = 0usize;
                    v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_2694_, v_includeDelayed_2695_, v_cs_2704_, v_sz_2707_, v___x_2708_, v___x_2706_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
                    if lean_obj_tag(v___x_2709_) == 0 {
                        v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_2724_ = (!lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_2724_ == 0 {
                            v___x_2712_ = v___x_2709_;
                            v_isShared_2713_ = v_isSharedCheck_2724_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2710_);
                            lean_dec(v___x_2709_);
                            v___x_2712_ = lean_box(0);
                            v_isShared_2713_ = v_isSharedCheck_2724_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2725_ = lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_2732_ = (!lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_2732_ == 0 {
                            v___x_2727_ = v___x_2709_;
                            v_isShared_2728_ = v_isSharedCheck_2732_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2725_);
                            lean_dec(v___x_2709_);
                            v___x_2727_ = lean_box(0);
                            v_isShared_2728_ = v_isSharedCheck_2732_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2733_ = lean_ctor_get(v_n_2696_, 0);
                    v___x_2734_ = lean_box(0);
                    v___x_2735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2735_, 0, v___x_2734_);
                    lean_ctor_set(v___x_2735_, 1, v_b_2697_);
                    v_sz_2736_ = lean_array_size(v_vs_2733_);
                    v___x_2737_ = 0usize;
                    v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_2695_, v_vs_2733_, v_sz_2736_, v___x_2737_, v___x_2735_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
                    if lean_obj_tag(v___x_2738_) == 0 {
                        v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
                        v_isSharedCheck_2753_ = (!lean_is_exclusive(v___x_2738_)) as u8;
                        if v_isSharedCheck_2753_ == 0 {
                            v___x_2741_ = v___x_2738_;
                            v_isShared_2742_ = v_isSharedCheck_2753_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2739_);
                            lean_dec(v___x_2738_);
                            v___x_2741_ = lean_box(0);
                            v_isShared_2742_ = v_isSharedCheck_2753_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2754_ = lean_ctor_get(v___x_2738_, 0);
                        v_isSharedCheck_2761_ = (!lean_is_exclusive(v___x_2738_)) as u8;
                        if v_isSharedCheck_2761_ == 0 {
                            v___x_2756_ = v___x_2738_;
                            v_isShared_2757_ = v_isSharedCheck_2761_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2754_);
                            lean_dec(v___x_2738_);
                            v___x_2756_ = lean_box(0);
                            v_isShared_2757_ = v_isSharedCheck_2761_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2714_ = lean_ctor_get(v_a_2710_, 0);
                if lean_obj_tag(v_fst_2714_) == 0 {
                    v_snd_2715_ = lean_ctor_get(v_a_2710_, 1);
                    lean_inc(v_snd_2715_);
                    lean_dec(v_a_2710_);
                    v___x_2716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2716_, 0, v_snd_2715_);
                    if v_isShared_2713_ == 0 {
                        lean_ctor_set(v___x_2712_, 0, v___x_2716_);
                        v___x_2718_ = v___x_2712_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                        v___x_2718_ = v_reuseFailAlloc_2719_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2714_);
                    lean_dec(v_a_2710_);
                    v_val_2720_ = lean_ctor_get(v_fst_2714_, 0);
                    lean_inc(v_val_2720_);
                    lean_dec_ref_known(v_fst_2714_, 1);
                    if v_isShared_2713_ == 0 {
                        lean_ctor_set(v___x_2712_, 0, v_val_2720_);
                        v___x_2722_ = v___x_2712_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_val_2720_);
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
                    v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
                    v___x_2730_ = v_reuseFailAlloc_2731_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2730_;
            }
            6 => {
                v_fst_2743_ = lean_ctor_get(v_a_2739_, 0);
                if lean_obj_tag(v_fst_2743_) == 0 {
                    v_snd_2744_ = lean_ctor_get(v_a_2739_, 1);
                    lean_inc(v_snd_2744_);
                    lean_dec(v_a_2739_);
                    v___x_2745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2745_, 0, v_snd_2744_);
                    if v_isShared_2742_ == 0 {
                        lean_ctor_set(v___x_2741_, 0, v___x_2745_);
                        v___x_2747_ = v___x_2741_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
                        v___x_2747_ = v_reuseFailAlloc_2748_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2743_);
                    lean_dec(v_a_2739_);
                    v_val_2749_ = lean_ctor_get(v_fst_2743_, 0);
                    lean_inc(v_val_2749_);
                    lean_dec_ref_known(v_fst_2743_, 1);
                    if v_isShared_2742_ == 0 {
                        lean_ctor_set(v___x_2741_, 0, v_val_2749_);
                        v___x_2751_ = v___x_2741_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_val_2749_);
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
                    v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
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
    mut v_as_2763_: *mut LeanObject,
    mut v_sz_2764_: usize,
    mut v_i_2765_: usize,
    mut v_b_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: usize = 0;
    let mut v___x_2785_: usize = 0;
    let mut v_reuseFailAlloc_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_a_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut v_isSharedCheck_2813_: u8 = 0;
    let mut v_unused_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2773_ = lean_usize_dec_lt(v_i_2765_, v_sz_2764_);
                if v___x_2773_ == 0 {
                    v___x_2774_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2774_, 0, v_b_2766_);
                    return v___x_2774_;
                } else {
                    v_snd_2775_ = lean_ctor_get(v_b_2766_, 1);
                    v_isSharedCheck_2813_ = (!lean_is_exclusive(v_b_2766_)) as u8;
                    if v_isSharedCheck_2813_ == 0 {
                        v_unused_2814_ = lean_ctor_get(v_b_2766_, 0);
                        lean_dec(v_unused_2814_);
                        v___x_2777_ = v_b_2766_;
                        v_isShared_2778_ = v_isSharedCheck_2813_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2775_);
                        lean_dec(v_b_2766_);
                        v___x_2777_ = lean_box(0);
                        v_isShared_2778_ = v_isSharedCheck_2813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2779_ = lean_box(0);
                v_a_2788_ = lean_array_uget_borrowed(v_as_2763_, v_i_2765_);
                if lean_obj_tag(v_a_2788_) == 0 {
                    v_a_2781_ = v_snd_2775_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_2775_);
                    v_val_2789_ = lean_ctor_get(v_a_2788_, 0);
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
                    if lean_obj_tag(v___x_2791_) == 0 {
                        lean_dec_ref_known(v___x_2791_, 1);
                        v___x_2792_ = lean_box(0);
                        v___x_2793_ = 0;
                        v___x_2794_ = l_Lean_LocalDecl_value_x3f(v_val_2789_, v___x_2793_);
                        if lean_obj_tag(v___x_2794_) == 1 {
                            v_val_2795_ = lean_ctor_get(v___x_2794_, 0);
                            lean_inc(v_val_2795_);
                            lean_dec_ref_known(v___x_2794_, 1);
                            v___x_2796_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2795_,
                                v_includeDelayed_2762_,
                                v___y_2767_,
                                v___y_2768_,
                                v___y_2769_,
                                v___y_2770_,
                                v___y_2771_,
                            );
                            if lean_obj_tag(v___x_2796_) == 0 {
                                lean_dec_ref_known(v___x_2796_, 1);
                                v_a_2781_ = v___x_2792_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2777_);
                                v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
                                v_isSharedCheck_2804_ = (!lean_is_exclusive(v___x_2796_)) as u8;
                                if v_isSharedCheck_2804_ == 0 {
                                    v___x_2799_ = v___x_2796_;
                                    v_isShared_2800_ = v_isSharedCheck_2804_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2797_);
                                    lean_dec(v___x_2796_);
                                    v___x_2799_ = lean_box(0);
                                    v_isShared_2800_ = v_isSharedCheck_2804_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2794_);
                            v_a_2781_ = v___x_2792_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2777_);
                        v_a_2805_ = lean_ctor_get(v___x_2791_, 0);
                        v_isSharedCheck_2812_ = (!lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_2812_ == 0 {
                            v___x_2807_ = v___x_2791_;
                            v_isShared_2808_ = v_isSharedCheck_2812_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2805_);
                            lean_dec(v___x_2791_);
                            v___x_2807_ = lean_box(0);
                            v_isShared_2808_ = v_isSharedCheck_2812_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2778_ == 0 {
                    lean_ctor_set(v___x_2777_, 1, v_a_2781_);
                    lean_ctor_set(v___x_2777_, 0, v___x_2779_);
                    v___x_2783_ = v___x_2777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2779_);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_a_2781_);
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
                    v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
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
                    v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
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
    mut v_as_2816_: *mut LeanObject,
    mut v_sz_2817_: usize,
    mut v_i_2818_: usize,
    mut v_b_2819_: *mut LeanObject,
    mut v___y_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: usize = 0;
    let mut v___x_2838_: usize = 0;
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_a_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v_isSharedCheck_2866_: u8 = 0;
    let mut v_unused_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2826_ = lean_usize_dec_lt(v_i_2818_, v_sz_2817_);
                if v___x_2826_ == 0 {
                    v___x_2827_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2827_, 0, v_b_2819_);
                    return v___x_2827_;
                } else {
                    v_snd_2828_ = lean_ctor_get(v_b_2819_, 1);
                    v_isSharedCheck_2866_ = (!lean_is_exclusive(v_b_2819_)) as u8;
                    if v_isSharedCheck_2866_ == 0 {
                        v_unused_2867_ = lean_ctor_get(v_b_2819_, 0);
                        lean_dec(v_unused_2867_);
                        v___x_2830_ = v_b_2819_;
                        v_isShared_2831_ = v_isSharedCheck_2866_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2828_);
                        lean_dec(v_b_2819_);
                        v___x_2830_ = lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2866_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2832_ = lean_box(0);
                v_a_2841_ = lean_array_uget_borrowed(v_as_2816_, v_i_2818_);
                if lean_obj_tag(v_a_2841_) == 0 {
                    v_a_2834_ = v_snd_2828_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_2828_);
                    v_val_2842_ = lean_ctor_get(v_a_2841_, 0);
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
                    if lean_obj_tag(v___x_2844_) == 0 {
                        lean_dec_ref_known(v___x_2844_, 1);
                        v___x_2845_ = lean_box(0);
                        v___x_2846_ = 0;
                        v___x_2847_ = l_Lean_LocalDecl_value_x3f(v_val_2842_, v___x_2846_);
                        if lean_obj_tag(v___x_2847_) == 1 {
                            v_val_2848_ = lean_ctor_get(v___x_2847_, 0);
                            lean_inc(v_val_2848_);
                            lean_dec_ref_known(v___x_2847_, 1);
                            v___x_2849_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                                v_val_2848_,
                                v_includeDelayed_2815_,
                                v___y_2820_,
                                v___y_2821_,
                                v___y_2822_,
                                v___y_2823_,
                                v___y_2824_,
                            );
                            if lean_obj_tag(v___x_2849_) == 0 {
                                lean_dec_ref_known(v___x_2849_, 1);
                                v_a_2834_ = v___x_2845_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2830_);
                                v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
                                v_isSharedCheck_2857_ = (!lean_is_exclusive(v___x_2849_)) as u8;
                                if v_isSharedCheck_2857_ == 0 {
                                    v___x_2852_ = v___x_2849_;
                                    v_isShared_2853_ = v_isSharedCheck_2857_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2850_);
                                    lean_dec(v___x_2849_);
                                    v___x_2852_ = lean_box(0);
                                    v_isShared_2853_ = v_isSharedCheck_2857_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2847_);
                            v_a_2834_ = v___x_2845_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2830_);
                        v_a_2858_ = lean_ctor_get(v___x_2844_, 0);
                        v_isSharedCheck_2865_ = (!lean_is_exclusive(v___x_2844_)) as u8;
                        if v_isSharedCheck_2865_ == 0 {
                            v___x_2860_ = v___x_2844_;
                            v_isShared_2861_ = v_isSharedCheck_2865_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2858_);
                            lean_dec(v___x_2844_);
                            v___x_2860_ = lean_box(0);
                            v_isShared_2861_ = v_isSharedCheck_2865_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2831_ == 0 {
                    lean_ctor_set(v___x_2830_, 1, v_a_2834_);
                    lean_ctor_set(v___x_2830_, 0, v___x_2832_);
                    v___x_2836_ = v___x_2830_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2832_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_a_2834_);
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
                    v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
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
                    v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
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
    mut v_t_2869_: *mut LeanObject,
    mut v_init_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v_a_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2891_: usize = 0;
    let mut v___x_2892_: usize = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v_fst_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v_a_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2877_ = lean_ctor_get(v_t_2869_, 0);
                v_tail_2878_ = lean_ctor_get(v_t_2869_, 1);
                v___x_2879_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_2870_, v_includeDelayed_2868_, v_root_2877_, v_init_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
                if lean_obj_tag(v___x_2879_) == 0 {
                    v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2916_ = (!lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2882_ = v___x_2879_;
                        v_isShared_2883_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2880_);
                        lean_dec(v___x_2879_);
                        v___x_2882_ = lean_box(0);
                        v_isShared_2883_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2917_ = lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2924_ = (!lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2924_ == 0 {
                        v___x_2919_ = v___x_2879_;
                        v_isShared_2920_ = v_isSharedCheck_2924_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2917_);
                        lean_dec(v___x_2879_);
                        v___x_2919_ = lean_box(0);
                        v_isShared_2920_ = v_isSharedCheck_2924_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2880_) == 0 {
                    v_a_2884_ = lean_ctor_get(v_a_2880_, 0);
                    lean_inc(v_a_2884_);
                    lean_dec_ref_known(v_a_2880_, 1);
                    if v_isShared_2883_ == 0 {
                        lean_ctor_set(v___x_2882_, 0, v_a_2884_);
                        v___x_2886_ = v___x_2882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2884_);
                        v___x_2886_ = v_reuseFailAlloc_2887_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2882_);
                    v_a_2888_ = lean_ctor_get(v_a_2880_, 0);
                    lean_inc(v_a_2888_);
                    lean_dec_ref_known(v_a_2880_, 1);
                    v___x_2889_ = lean_box(0);
                    v___x_2890_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2890_, 0, v___x_2889_);
                    lean_ctor_set(v___x_2890_, 1, v_a_2888_);
                    v_sz_2891_ = lean_array_size(v_tail_2878_);
                    v___x_2892_ = 0usize;
                    v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_2868_, v_tail_2878_, v_sz_2891_, v___x_2892_, v___x_2890_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
                    if lean_obj_tag(v___x_2893_) == 0 {
                        v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2907_ = (!lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2907_ == 0 {
                            v___x_2896_ = v___x_2893_;
                            v_isShared_2897_ = v_isSharedCheck_2907_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2894_);
                            lean_dec(v___x_2893_);
                            v___x_2896_ = lean_box(0);
                            v_isShared_2897_ = v_isSharedCheck_2907_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2908_ = lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2915_ = (!lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2915_ == 0 {
                            v___x_2910_ = v___x_2893_;
                            v_isShared_2911_ = v_isSharedCheck_2915_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2908_);
                            lean_dec(v___x_2893_);
                            v___x_2910_ = lean_box(0);
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
                v_fst_2898_ = lean_ctor_get(v_a_2894_, 0);
                if lean_obj_tag(v_fst_2898_) == 0 {
                    v_snd_2899_ = lean_ctor_get(v_a_2894_, 1);
                    lean_inc(v_snd_2899_);
                    lean_dec(v_a_2894_);
                    if v_isShared_2897_ == 0 {
                        lean_ctor_set(v___x_2896_, 0, v_snd_2899_);
                        v___x_2901_ = v___x_2896_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_snd_2899_);
                        v___x_2901_ = v_reuseFailAlloc_2902_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2898_);
                    lean_dec(v_a_2894_);
                    v_val_2903_ = lean_ctor_get(v_fst_2898_, 0);
                    lean_inc(v_val_2903_);
                    lean_dec_ref_known(v_fst_2898_, 1);
                    if v_isShared_2897_ == 0 {
                        lean_ctor_set(v___x_2896_, 0, v_val_2903_);
                        v___x_2905_ = v___x_2896_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_val_2903_);
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
                    v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
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
                    v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
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
    mut v_mvarId_2925_: *mut LeanObject,
    mut v_includeDelayed_2926_: u8,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2953_: u8 = 0;
    let mut v_cancelTk_x3f_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2955_: u8 = 0;
    let mut v_inheritedTraceOptions_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v_val_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v_a_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v_a_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_a_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_a_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2941_ = lean_ctor_get(v_a_2930_, 0);
                lean_inc_ref(v_fileName_2941_);
                v_fileMap_2942_ = lean_ctor_get(v_a_2930_, 1);
                lean_inc_ref(v_fileMap_2942_);
                v_options_2943_ = lean_ctor_get(v_a_2930_, 2);
                lean_inc_ref(v_options_2943_);
                v_currRecDepth_2944_ = lean_ctor_get(v_a_2930_, 3);
                lean_inc(v_currRecDepth_2944_);
                v_maxRecDepth_2945_ = lean_ctor_get(v_a_2930_, 4);
                lean_inc(v_maxRecDepth_2945_);
                v_ref_2946_ = lean_ctor_get(v_a_2930_, 5);
                lean_inc(v_ref_2946_);
                v_currNamespace_2947_ = lean_ctor_get(v_a_2930_, 6);
                lean_inc(v_currNamespace_2947_);
                v_openDecls_2948_ = lean_ctor_get(v_a_2930_, 7);
                lean_inc(v_openDecls_2948_);
                v_initHeartbeats_2949_ = lean_ctor_get(v_a_2930_, 8);
                lean_inc(v_initHeartbeats_2949_);
                v_maxHeartbeats_2950_ = lean_ctor_get(v_a_2930_, 9);
                lean_inc(v_maxHeartbeats_2950_);
                v_quotContext_2951_ = lean_ctor_get(v_a_2930_, 10);
                lean_inc(v_quotContext_2951_);
                v_currMacroScope_2952_ = lean_ctor_get(v_a_2930_, 11);
                lean_inc(v_currMacroScope_2952_);
                v_diag_2953_ = lean_ctor_get_uint8(
                    v_a_2930_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2954_ = lean_ctor_get(v_a_2930_, 12);
                lean_inc(v_cancelTk_x3f_2954_);
                v_suppressElabErrors_2955_ = lean_ctor_get_uint8(
                    v_a_2930_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2956_ = lean_ctor_get(v_a_2930_, 13);
                lean_inc_ref(v_inheritedTraceOptions_2956_);
                lean_dec_ref(v_a_2930_);
                v___x_3011_ = lean_unsigned_to_nat(0);
                v___x_3012_ = lean_nat_dec_eq(v_maxRecDepth_2945_, v___x_3011_);
                if v___x_3012_ == 0 {
                    v___x_3013_ = lean_nat_dec_eq(v_currRecDepth_2944_, v_maxRecDepth_2945_);
                    if v___x_3013_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_2956_);
                        lean_dec(v_cancelTk_x3f_2954_);
                        lean_dec(v_currMacroScope_2952_);
                        lean_dec(v_quotContext_2951_);
                        lean_dec(v_maxHeartbeats_2950_);
                        lean_dec(v_initHeartbeats_2949_);
                        lean_dec(v_openDecls_2948_);
                        lean_dec(v_currNamespace_2947_);
                        lean_dec(v_maxRecDepth_2945_);
                        lean_dec(v_currRecDepth_2944_);
                        lean_dec_ref(v_options_2943_);
                        lean_dec_ref(v_fileMap_2942_);
                        lean_dec_ref(v_fileName_2941_);
                        lean_dec(v_mvarId_2925_);
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
                lean_inc(v___y_2934_);
                v___x_2938_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v___x_2937_, v___y_2934_, v___y_2935_);
                v___x_2939_ = lean_st_ref_set(v_a_2927_, v___x_2938_);
                v_mvarId_2925_ = v___y_2934_;
                v_a_2930_ = v___y_2936_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2958_ = lean_unsigned_to_nat(1);
                v___x_2959_ = lean_nat_add(v_currRecDepth_2944_, v___x_2958_);
                lean_dec(v_currRecDepth_2944_);
                v___x_2960_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2960_, 0, v_fileName_2941_);
                lean_ctor_set(v___x_2960_, 1, v_fileMap_2942_);
                lean_ctor_set(v___x_2960_, 2, v_options_2943_);
                lean_ctor_set(v___x_2960_, 3, v___x_2959_);
                lean_ctor_set(v___x_2960_, 4, v_maxRecDepth_2945_);
                lean_ctor_set(v___x_2960_, 5, v_ref_2946_);
                lean_ctor_set(v___x_2960_, 6, v_currNamespace_2947_);
                lean_ctor_set(v___x_2960_, 7, v_openDecls_2948_);
                lean_ctor_set(v___x_2960_, 8, v_initHeartbeats_2949_);
                lean_ctor_set(v___x_2960_, 9, v_maxHeartbeats_2950_);
                lean_ctor_set(v___x_2960_, 10, v_quotContext_2951_);
                lean_ctor_set(v___x_2960_, 11, v_currMacroScope_2952_);
                lean_ctor_set(v___x_2960_, 12, v_cancelTk_x3f_2954_);
                lean_ctor_set(v___x_2960_, 13, v_inheritedTraceOptions_2956_);
                lean_ctor_set_uint8(
                    v___x_2960_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2953_,
                );
                lean_ctor_set_uint8(
                    v___x_2960_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2955_,
                );
                lean_inc(v_mvarId_2925_);
                v___x_2961_ = l_Lean_MVarId_getDecl(
                    v_mvarId_2925_,
                    v_a_2928_,
                    v_a_2929_,
                    v___x_2960_,
                    v_a_2931_,
                );
                if lean_obj_tag(v___x_2961_) == 0 {
                    v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
                    lean_inc(v_a_2962_);
                    lean_dec_ref_known(v___x_2961_, 1);
                    v_lctx_2963_ = lean_ctor_get(v_a_2962_, 1);
                    lean_inc_ref(v_lctx_2963_);
                    v_type_2964_ = lean_ctor_get(v_a_2962_, 2);
                    lean_inc_ref(v_type_2964_);
                    lean_dec(v_a_2962_);
                    v___x_2965_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
                        v_type_2964_,
                        v_includeDelayed_2926_,
                        v_a_2927_,
                        v_a_2928_,
                        v_a_2929_,
                        v___x_2960_,
                        v_a_2931_,
                    );
                    if lean_obj_tag(v___x_2965_) == 0 {
                        lean_dec_ref_known(v___x_2965_, 1);
                        v_decls_2966_ = lean_ctor_get(v_lctx_2963_, 1);
                        lean_inc_ref(v_decls_2966_);
                        lean_dec_ref(v_lctx_2963_);
                        v___x_2967_ = lean_box(0);
                        v___x_2968_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5(v_includeDelayed_2926_, v_decls_2966_, v___x_2967_, v_a_2927_, v_a_2928_, v_a_2929_, v___x_2960_, v_a_2931_);
                        lean_dec_ref(v_decls_2966_);
                        if lean_obj_tag(v___x_2968_) == 0 {
                            lean_dec_ref_known(v___x_2968_, 1);
                            v___x_2969_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_2925_, v_a_2929_);
                            lean_dec(v_mvarId_2925_);
                            if lean_obj_tag(v___x_2969_) == 0 {
                                v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
                                v_isSharedCheck_2994_ = (!lean_is_exclusive(v___x_2969_)) as u8;
                                if v_isSharedCheck_2994_ == 0 {
                                    v___x_2972_ = v___x_2969_;
                                    v_isShared_2973_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2970_);
                                    lean_dec(v___x_2969_);
                                    v___x_2972_ = lean_box(0);
                                    v_isShared_2973_ = v_isSharedCheck_2994_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_2960_, 14);
                                v_a_2995_ = lean_ctor_get(v___x_2969_, 0);
                                v_isSharedCheck_3002_ = (!lean_is_exclusive(v___x_2969_)) as u8;
                                if v_isSharedCheck_3002_ == 0 {
                                    v___x_2997_ = v___x_2969_;
                                    v_isShared_2998_ = v_isSharedCheck_3002_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2995_);
                                    lean_dec(v___x_2969_);
                                    v___x_2997_ = lean_box(0);
                                    v_isShared_2998_ = v_isSharedCheck_3002_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v___x_2960_, 14);
                            lean_dec(v_mvarId_2925_);
                            return v___x_2968_;
                        }
                    } else {
                        lean_dec_ref(v_lctx_2963_);
                        lean_dec_ref_known(v___x_2960_, 14);
                        lean_dec(v_mvarId_2925_);
                        return v___x_2965_;
                    }
                } else {
                    lean_dec_ref_known(v___x_2960_, 14);
                    lean_dec(v_mvarId_2925_);
                    v_a_3003_ = lean_ctor_get(v___x_2961_, 0);
                    v_isSharedCheck_3010_ = (!lean_is_exclusive(v___x_2961_)) as u8;
                    if v_isSharedCheck_3010_ == 0 {
                        v___x_3005_ = v___x_2961_;
                        v_isShared_3006_ = v_isSharedCheck_3010_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3003_);
                        lean_dec(v___x_2961_);
                        v___x_3005_ = lean_box(0);
                        v_isShared_3006_ = v_isSharedCheck_3010_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_2970_) == 1 {
                    lean_del_object(v___x_2972_);
                    v_val_2974_ = lean_ctor_get(v_a_2970_, 0);
                    lean_inc(v_val_2974_);
                    lean_dec_ref_known(v_a_2970_, 1);
                    v_mvarIdPending_2975_ = lean_ctor_get(v_val_2974_, 1);
                    lean_inc(v_mvarIdPending_2975_);
                    lean_dec(v_val_2974_);
                    v___x_2976_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarIdPending_2975_, v_a_2929_);
                    if lean_obj_tag(v___x_2976_) == 0 {
                        v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
                        lean_inc(v_a_2977_);
                        lean_dec_ref_known(v___x_2976_, 1);
                        v___x_2978_ = (lean_unbox(v_a_2977_) as u8);
                        lean_dec(v_a_2977_);
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
                        if lean_obj_tag(v___x_2976_) == 0 {
                            v_a_2980_ = lean_ctor_get(v___x_2976_, 0);
                            lean_inc(v_a_2980_);
                            lean_dec_ref_known(v___x_2976_, 1);
                            v___x_2981_ = (lean_unbox(v_a_2980_) as u8);
                            lean_dec(v_a_2980_);
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
                            lean_dec(v_mvarIdPending_2975_);
                            lean_dec_ref_known(v___x_2960_, 14);
                            v_a_2983_ = lean_ctor_get(v___x_2976_, 0);
                            v_isSharedCheck_2990_ = (!lean_is_exclusive(v___x_2976_)) as u8;
                            if v_isSharedCheck_2990_ == 0 {
                                v___x_2985_ = v___x_2976_;
                                v_isShared_2986_ = v_isSharedCheck_2990_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2983_);
                                lean_dec(v___x_2976_);
                                v___x_2985_ = lean_box(0);
                                v_isShared_2986_ = v_isSharedCheck_2990_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_2970_);
                    lean_dec_ref_known(v___x_2960_, 14);
                    if v_isShared_2973_ == 0 {
                        lean_ctor_set(v___x_2972_, 0, v___x_2967_);
                        v___x_2992_ = v___x_2972_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2967_);
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
                    v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
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
                    v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
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
                    v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
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
    mut v_as_3015_: *mut LeanObject,
    mut v_i_3016_: usize,
    mut v_stop_3017_: usize,
    mut v_b_3018_: *mut LeanObject,
    mut v___y_3019_: *mut LeanObject,
    mut v___y_3020_: *mut LeanObject,
    mut v___y_3021_: *mut LeanObject,
    mut v___y_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3025_ = lean_usize_dec_eq(v_i_3016_, v_stop_3017_);
                if v___x_3025_ == 0 {
                    v___x_3026_ = lean_array_uget_borrowed(v_as_3015_, v_i_3016_);
                    lean_inc_ref(v___y_3022_);
                    lean_inc(v___x_3026_);
                    v___x_3027_ = l___private_Lean_Meta_CollectMVars_0__go(
                        v___x_3026_,
                        v___x_3025_,
                        v___y_3019_,
                        v___y_3020_,
                        v___y_3021_,
                        v___y_3022_,
                        v___y_3023_,
                    );
                    if lean_obj_tag(v___x_3027_) == 0 {
                        v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
                        lean_inc(v_a_3028_);
                        lean_dec_ref_known(v___x_3027_, 1);
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
                    v___x_3032_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3032_, 0, v_b_3018_);
                    return v___x_3032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3___boxed(
    mut v_as_3033_: *mut LeanObject,
    mut v_i_3034_: *mut LeanObject,
    mut v_stop_3035_: *mut LeanObject,
    mut v_b_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3043_: usize = 0;
    let mut v_stop_boxed_3044_: usize = 0;
    let mut v_res_3045_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3043_ = lean_unbox_usize(v_i_3034_);
    lean_dec(v_i_3034_);
    v_stop_boxed_3044_ = lean_unbox_usize(v_stop_3035_);
    lean_dec(v_stop_3035_);
    v_res_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__3(v_as_3033_, v_i_boxed_3043_, v_stop_boxed_3044_, v_b_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
    lean_dec(v___y_3041_);
    lean_dec_ref(v___y_3040_);
    lean_dec(v___y_3039_);
    lean_dec_ref(v___y_3038_);
    lean_dec(v___y_3037_);
    lean_dec_ref(v_as_3033_);
    return v_res_3045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11___boxed(
    mut v_init_3046_: *mut LeanObject,
    mut v_includeDelayed_3047_: *mut LeanObject,
    mut v_as_3048_: *mut LeanObject,
    mut v_sz_3049_: *mut LeanObject,
    mut v_i_3050_: *mut LeanObject,
    mut v_b_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
    mut v___y_3054_: *mut LeanObject,
    mut v___y_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3058_: u8 = 0;
    let mut v_sz_boxed_3059_: usize = 0;
    let mut v_i_boxed_3060_: usize = 0;
    let mut v_res_3061_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3058_ = (lean_unbox(v_includeDelayed_3047_) as u8);
    v_sz_boxed_3059_ = lean_unbox_usize(v_sz_3049_);
    lean_dec(v_sz_3049_);
    v_i_boxed_3060_ = lean_unbox_usize(v_i_3050_);
    lean_dec(v_i_3050_);
    v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__11(v_init_3046_, v_includeDelayed_boxed_3058_, v_as_3048_, v_sz_boxed_3059_, v_i_boxed_3060_, v_b_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
    lean_dec(v___y_3056_);
    lean_dec_ref(v___y_3055_);
    lean_dec(v___y_3054_);
    lean_dec_ref(v___y_3053_);
    lean_dec(v___y_3052_);
    lean_dec_ref(v_as_3048_);
    return v_res_3061_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5___boxed(
    mut v_includeDelayed_3062_: *mut LeanObject,
    mut v_t_3063_: *mut LeanObject,
    mut v_init_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
    mut v___y_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3071_: u8 = 0;
    let mut v_res_3072_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3071_ = (lean_unbox(v_includeDelayed_3062_) as u8);
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
    lean_dec(v___y_3069_);
    lean_dec_ref(v___y_3068_);
    lean_dec(v___y_3067_);
    lean_dec_ref(v___y_3066_);
    lean_dec(v___y_3065_);
    lean_dec_ref(v_t_3063_);
    return v_res_3072_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8___boxed(
    mut v_includeDelayed_3073_: *mut LeanObject,
    mut v_as_3074_: *mut LeanObject,
    mut v_sz_3075_: *mut LeanObject,
    mut v_i_3076_: *mut LeanObject,
    mut v_b_3077_: *mut LeanObject,
    mut v___y_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
    mut v___y_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
    mut v___y_3083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3084_: u8 = 0;
    let mut v_sz_boxed_3085_: usize = 0;
    let mut v_i_boxed_3086_: usize = 0;
    let mut v_res_3087_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3084_ = (lean_unbox(v_includeDelayed_3073_) as u8);
    v_sz_boxed_3085_ = lean_unbox_usize(v_sz_3075_);
    lean_dec(v_sz_3075_);
    v_i_boxed_3086_ = lean_unbox_usize(v_i_3076_);
    lean_dec(v_i_3076_);
    v_res_3087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8(v_includeDelayed_boxed_3084_, v_as_3074_, v_sz_boxed_3085_, v_i_boxed_3086_, v_b_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
    lean_dec(v___y_3082_);
    lean_dec_ref(v___y_3081_);
    lean_dec(v___y_3080_);
    lean_dec_ref(v___y_3079_);
    lean_dec(v___y_3078_);
    lean_dec_ref(v_as_3074_);
    return v_res_3087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12___boxed(
    mut v_includeDelayed_3088_: *mut LeanObject,
    mut v_as_3089_: *mut LeanObject,
    mut v_sz_3090_: *mut LeanObject,
    mut v_i_3091_: *mut LeanObject,
    mut v_b_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3099_: u8 = 0;
    let mut v_sz_boxed_3100_: usize = 0;
    let mut v_i_boxed_3101_: usize = 0;
    let mut v_res_3102_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3099_ = (lean_unbox(v_includeDelayed_3088_) as u8);
    v_sz_boxed_3100_ = lean_unbox_usize(v_sz_3090_);
    lean_dec(v_sz_3090_);
    v_i_boxed_3101_ = lean_unbox_usize(v_i_3091_);
    lean_dec(v_i_3091_);
    v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12(v_includeDelayed_boxed_3099_, v_as_3089_, v_sz_boxed_3100_, v_i_boxed_3101_, v_b_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
    lean_dec(v___y_3097_);
    lean_dec_ref(v___y_3096_);
    lean_dec(v___y_3095_);
    lean_dec_ref(v___y_3094_);
    lean_dec(v___y_3093_);
    lean_dec_ref(v_as_3089_);
    return v_res_3102_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14___boxed(
    mut v_includeDelayed_3103_: *mut LeanObject,
    mut v_as_3104_: *mut LeanObject,
    mut v_sz_3105_: *mut LeanObject,
    mut v_i_3106_: *mut LeanObject,
    mut v_b_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3114_: u8 = 0;
    let mut v_sz_boxed_3115_: usize = 0;
    let mut v_i_boxed_3116_: usize = 0;
    let mut v_res_3117_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3114_ = (lean_unbox(v_includeDelayed_3103_) as u8);
    v_sz_boxed_3115_ = lean_unbox_usize(v_sz_3105_);
    lean_dec(v_sz_3105_);
    v_i_boxed_3116_ = lean_unbox_usize(v_i_3106_);
    lean_dec(v_i_3106_);
    v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__8_spec__14(v_includeDelayed_boxed_3114_, v_as_3104_, v_sz_boxed_3115_, v_i_boxed_3116_, v_b_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
    lean_dec(v___y_3112_);
    lean_dec_ref(v___y_3111_);
    lean_dec(v___y_3110_);
    lean_dec_ref(v___y_3109_);
    lean_dec(v___y_3108_);
    lean_dec_ref(v_as_3104_);
    return v_res_3117_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15___boxed(
    mut v_includeDelayed_3118_: *mut LeanObject,
    mut v_as_3119_: *mut LeanObject,
    mut v_sz_3120_: *mut LeanObject,
    mut v_i_3121_: *mut LeanObject,
    mut v_b_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
    mut v___y_3127_: *mut LeanObject,
    mut v___y_3128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3129_: u8 = 0;
    let mut v_sz_boxed_3130_: usize = 0;
    let mut v_i_boxed_3131_: usize = 0;
    let mut v_res_3132_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3129_ = (lean_unbox(v_includeDelayed_3118_) as u8);
    v_sz_boxed_3130_ = lean_unbox_usize(v_sz_3120_);
    lean_dec(v_sz_3120_);
    v_i_boxed_3131_ = lean_unbox_usize(v_i_3121_);
    lean_dec(v_i_3121_);
    v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7_spec__12_spec__15(v_includeDelayed_boxed_3129_, v_as_3119_, v_sz_boxed_3130_, v_i_boxed_3131_, v_b_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
    lean_dec(v___y_3127_);
    lean_dec_ref(v___y_3126_);
    lean_dec(v___y_3125_);
    lean_dec_ref(v___y_3124_);
    lean_dec(v___y_3123_);
    lean_dec_ref(v_as_3119_);
    return v_res_3132_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7___boxed(
    mut v_init_3133_: *mut LeanObject,
    mut v_includeDelayed_3134_: *mut LeanObject,
    mut v_n_3135_: *mut LeanObject,
    mut v_b_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3143_: u8 = 0;
    let mut v_res_3144_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3143_ = (lean_unbox(v_includeDelayed_3134_) as u8);
    v_res_3144_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_CollectMVars_0__go_spec__5_spec__7(v_init_3133_, v_includeDelayed_boxed_3143_, v_n_3135_, v_b_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
    lean_dec(v___y_3141_);
    lean_dec_ref(v___y_3140_);
    lean_dec(v___y_3139_);
    lean_dec_ref(v___y_3138_);
    lean_dec(v___y_3137_);
    lean_dec_ref(v_n_3135_);
    return v_res_3144_;
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__addMVars___boxed(
    mut v_e_3145_: *mut LeanObject,
    mut v_includeDelayed_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3153_: u8 = 0;
    let mut v_res_3154_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3153_ = (lean_unbox(v_includeDelayed_3146_) as u8);
    v_res_3154_ = l___private_Lean_Meta_CollectMVars_0__addMVars(
        v_e_3145_,
        v_includeDelayed_boxed_3153_,
        v_a_3147_,
        v_a_3148_,
        v_a_3149_,
        v_a_3150_,
        v_a_3151_,
    );
    lean_dec(v_a_3151_);
    lean_dec_ref(v_a_3150_);
    lean_dec(v_a_3149_);
    lean_dec_ref(v_a_3148_);
    lean_dec(v_a_3147_);
    return v_res_3154_;
}
pub unsafe fn l___private_Lean_Meta_CollectMVars_0__go___boxed(
    mut v_mvarId_3155_: *mut LeanObject,
    mut v_includeDelayed_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3163_: u8 = 0;
    let mut v_res_3164_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3163_ = (lean_unbox(v_includeDelayed_3156_) as u8);
    v_res_3164_ = l___private_Lean_Meta_CollectMVars_0__go(
        v_mvarId_3155_,
        v_includeDelayed_boxed_3163_,
        v_a_3157_,
        v_a_3158_,
        v_a_3159_,
        v_a_3160_,
        v_a_3161_,
    );
    lean_dec(v_a_3161_);
    lean_dec(v_a_3159_);
    lean_dec_ref(v_a_3158_);
    lean_dec(v_a_3157_);
    return v_res_3164_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(
    mut v_mvarId_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    v___x_3172_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___redArg(v_mvarId_3165_, v___y_3168_);
    return v___x_3172_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6___boxed(
    mut v_mvarId_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3180_: *mut LeanObject = core::ptr::null_mut();
    v_res_3180_ =
        l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_CollectMVars_0__go_spec__6(
            v_mvarId_3173_,
            v___y_3174_,
            v___y_3175_,
            v___y_3176_,
            v___y_3177_,
            v___y_3178_,
        );
    lean_dec(v___y_3178_);
    lean_dec_ref(v___y_3177_);
    lean_dec(v___y_3176_);
    lean_dec_ref(v___y_3175_);
    lean_dec(v___y_3174_);
    lean_dec(v_mvarId_3173_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(
    mut v_00_u03b1_3181_: *mut LeanObject,
    mut v_ref_3182_: *mut LeanObject,
    mut v___y_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
    mut v___y_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    v___x_3189_ =
        l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___redArg(
            v_ref_3182_,
        );
    return v___x_3189_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8___boxed(
    mut v_00_u03b1_3190_: *mut LeanObject,
    mut v_ref_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3198_: *mut LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_CollectMVars_0__go_spec__8(
        v_00_u03b1_3190_,
        v_ref_3191_,
        v___y_3192_,
        v___y_3193_,
        v___y_3194_,
        v___y_3195_,
        v___y_3196_,
    );
    lean_dec(v___y_3196_);
    lean_dec_ref(v___y_3195_);
    lean_dec(v___y_3194_);
    lean_dec_ref(v___y_3193_);
    lean_dec(v___y_3192_);
    return v_res_3198_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0(
    mut v_00_u03b2_3199_: *mut LeanObject,
    mut v_m_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_b_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    v___x_3203_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0___redArg(v_m_3200_, v_a_3201_, v_b_3202_);
    return v___x_3203_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(
    mut v_mvarId_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
    mut v___y_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    v___x_3211_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___redArg(v_mvarId_3204_, v___y_3207_);
    return v___x_3211_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1___boxed(
    mut v_mvarId_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
    mut v___y_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3219_: *mut LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__1(v_mvarId_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
    lean_dec(v___y_3217_);
    lean_dec_ref(v___y_3216_);
    lean_dec(v___y_3215_);
    lean_dec_ref(v___y_3214_);
    lean_dec(v___y_3213_);
    lean_dec(v_mvarId_3212_);
    return v_res_3219_;
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(
    mut v_mvarId_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___redArg(v_mvarId_3220_, v___y_3223_);
    return v___x_3227_;
}
pub unsafe fn l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7___boxed(
    mut v_mvarId_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3235_: *mut LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Lean_MVarId_isAssignedOrDelayedAssigned___at___00__private_Lean_Meta_CollectMVars_0__go_spec__7(v_mvarId_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
    lean_dec(v___y_3233_);
    lean_dec_ref(v___y_3232_);
    lean_dec(v___y_3231_);
    lean_dec_ref(v___y_3230_);
    lean_dec(v___y_3229_);
    lean_dec(v_mvarId_3228_);
    return v_res_3235_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(
    mut v_00_u03b2_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
    mut v_x_3238_: *mut LeanObject,
) -> u8 {
    let mut v___x_3239_: u8 = 0;
    v___x_3239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___redArg(v_a_3237_, v_x_3238_);
    return v___x_3239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_3240_: *mut LeanObject,
    mut v_a_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3243_: u8 = 0;
    let mut v_r_3244_: *mut LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__0(v_00_u03b2_3240_, v_a_3241_, v_x_3242_);
    lean_dec(v_x_3242_);
    lean_dec(v_a_3241_);
    v_r_3244_ = lean_box((v_res_3243_) as usize);
    return v_r_3244_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1(
    mut v_00_u03b2_3245_: *mut LeanObject,
    mut v_data_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1___redArg(v_data_3246_);
    return v___x_3247_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5(
    mut v_00_u03b2_3248_: *mut LeanObject,
    mut v_i_3249_: *mut LeanObject,
    mut v_source_3250_: *mut LeanObject,
    mut v_target_3251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    v___x_3252_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5___redArg(v_i_3249_, v_source_3250_, v_target_3251_);
    return v___x_3252_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11(
    mut v_00_u03b2_3253_: *mut LeanObject,
    mut v_x_3254_: *mut LeanObject,
    mut v_x_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_CollectMVars_0__addMVars_spec__0_spec__1_spec__5_spec__11___redArg(v_x_3254_, v_x_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_MVarId_getMVarDependencies(
    mut v_mvarId_3257_: *mut LeanObject,
    mut v_includeDelayed_3258_: u8,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut v_unused_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3264_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1_once
                    ),
                    _init_l___private_Lean_Meta_CollectMVars_0__addMVars___closed__1,
                );
                v___x_3265_ = lean_st_mk_ref(v___x_3264_);
                lean_inc_ref(v_a_3261_);
                v___x_3266_ = l___private_Lean_Meta_CollectMVars_0__go(
                    v_mvarId_3257_,
                    v_includeDelayed_3258_,
                    v___x_3265_,
                    v_a_3259_,
                    v_a_3260_,
                    v_a_3261_,
                    v_a_3262_,
                );
                if lean_obj_tag(v___x_3266_) == 0 {
                    v_isSharedCheck_3274_ = (!lean_is_exclusive(v___x_3266_)) as u8;
                    if v_isSharedCheck_3274_ == 0 {
                        v_unused_3275_ = lean_ctor_get(v___x_3266_, 0);
                        lean_dec(v_unused_3275_);
                        v___x_3268_ = v___x_3266_;
                        v_isShared_3269_ = v_isSharedCheck_3274_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3266_);
                        v___x_3268_ = lean_box(0);
                        v_isShared_3269_ = v_isSharedCheck_3274_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3265_);
                    v_a_3276_ = lean_ctor_get(v___x_3266_, 0);
                    v_isSharedCheck_3283_ = (!lean_is_exclusive(v___x_3266_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v___x_3278_ = v___x_3266_;
                        v_isShared_3279_ = v_isSharedCheck_3283_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3276_);
                        lean_dec(v___x_3266_);
                        v___x_3278_ = lean_box(0);
                        v_isShared_3279_ = v_isSharedCheck_3283_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3270_ = lean_st_ref_get(v___x_3265_);
                lean_dec(v___x_3265_);
                if v_isShared_3269_ == 0 {
                    lean_ctor_set(v___x_3268_, 0, v___x_3270_);
                    v___x_3272_ = v___x_3268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
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
                    v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
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
    mut v_mvarId_3284_: *mut LeanObject,
    mut v_includeDelayed_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
    mut v_a_3289_: *mut LeanObject,
    mut v_a_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3291_: u8 = 0;
    let mut v_res_3292_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3291_ = (lean_unbox(v_includeDelayed_3285_) as u8);
    v_res_3292_ = l_Lean_MVarId_getMVarDependencies(
        v_mvarId_3284_,
        v_includeDelayed_boxed_3291_,
        v_a_3286_,
        v_a_3287_,
        v_a_3288_,
        v_a_3289_,
    );
    lean_dec(v_a_3289_);
    lean_dec_ref(v_a_3288_);
    lean_dec(v_a_3287_);
    lean_dec_ref(v_a_3286_);
    return v_res_3292_;
}
pub unsafe fn l_Lean_Expr_getMVarDependencies(
    mut v_e_3293_: *mut LeanObject,
    mut v_includeDelayed_3294_: u8,
    mut v_a_3295_: *mut LeanObject,
    mut v_a_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut v_unused_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3300_ = lean_obj_once(
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
                if lean_obj_tag(v___x_3302_) == 0 {
                    v_isSharedCheck_3310_ = (!lean_is_exclusive(v___x_3302_)) as u8;
                    if v_isSharedCheck_3310_ == 0 {
                        v_unused_3311_ = lean_ctor_get(v___x_3302_, 0);
                        lean_dec(v_unused_3311_);
                        v___x_3304_ = v___x_3302_;
                        v_isShared_3305_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3302_);
                        v___x_3304_ = lean_box(0);
                        v_isShared_3305_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3301_);
                    v_a_3312_ = lean_ctor_get(v___x_3302_, 0);
                    v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3302_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3314_ = v___x_3302_;
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3312_);
                        lean_dec(v___x_3302_);
                        v___x_3314_ = lean_box(0);
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3306_ = lean_st_ref_get(v___x_3301_);
                lean_dec(v___x_3301_);
                if v_isShared_3305_ == 0 {
                    lean_ctor_set(v___x_3304_, 0, v___x_3306_);
                    v___x_3308_ = v___x_3304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
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
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
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
    mut v_e_3320_: *mut LeanObject,
    mut v_includeDelayed_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeDelayed_boxed_3327_: u8 = 0;
    let mut v_res_3328_: *mut LeanObject = core::ptr::null_mut();
    v_includeDelayed_boxed_3327_ = (lean_unbox(v_includeDelayed_3321_) as u8);
    v_res_3328_ = l_Lean_Expr_getMVarDependencies(
        v_e_3320_,
        v_includeDelayed_boxed_3327_,
        v_a_3322_,
        v_a_3323_,
        v_a_3324_,
        v_a_3325_,
    );
    lean_dec(v_a_3325_);
    lean_dec_ref(v_a_3324_);
    lean_dec(v_a_3323_);
    lean_dec_ref(v_a_3322_);
    return v_res_3328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CollectMVars(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CollectMVars(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CollectMVars(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_CollectMVars(builtin);
}
