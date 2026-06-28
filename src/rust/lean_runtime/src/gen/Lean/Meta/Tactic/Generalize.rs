// Lean compiler output
// Module: Lean.Meta.Tactic.Generalize
// Imports: Lean.Meta.KAbstract Lean.Meta.Tactic.Intro Lean.Meta.Tactic.FVarSubst Lean.Meta.Tactic.Revert Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_List_lengthTR___redArg};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppN, l_Lean_mkFVar, l_Lean_mkForall,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkHEq,
    l_Lean_Meta_mkHEqRefl, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkForallFVars,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_isTypeCorrect;
use crate::r#gen::Lean::Meta::KAbstract::{
    initialize_Lean_Meta_KAbstract, l_Lean_Meta_kabstract, runtime_initialize_Lean_Meta_KAbstract,
};
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, l_Lean_Meta_FVarSubst_insert,
    runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, l_Lean_Meta_introNCore,
    runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::{
    initialize_Lean_Meta_Tactic_Revert, l_Lean_MVarId_revert,
    runtime_initialize_Lean_Meta_Tactic_Revert,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedGeneralizeArg_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedGeneralizeArg: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [114, 101, 115, 117, 108, 116, 32, 105, 115, 32, 110, 111, 116, 32, 116, 121, 112, 101, 32, 99, 111, 114, 114, 101, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 0],
};
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13102016849987196918 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_generalizeHyp___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_MVarId_generalizeHyp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_generalizeHyp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = crate::leanh::lean_box(0);
    v___x_1535_ = l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1;
    v___x_1536_ = l_Lean_Expr_const___override(v___x_1535_, v___x_1534_);
    return v___x_1536_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = crate::leanh::lean_box(0);
    v___x_1538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2_once),
        _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2,
    );
    v___x_1539_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1539_, 0, v___x_1538_);
    crate::leanh::lean_ctor_set(v___x_1539_, 1, v___x_1537_);
    crate::leanh::lean_ctor_set(v___x_1539_, 2, v___x_1537_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedGeneralizeArg_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3_once),
        _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3,
    );
    return v___x_1540_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedGeneralizeArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1541_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
    return v___x_1541_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(
    mut v_e_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1545_: u8 = 0;
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_unused_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1545_ = l_Lean_Expr_hasMVar(v_e_1542_);
                if v___x_1545_ == 0 {
                    v___x_1546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1546_, 0, v_e_1542_);
                    return v___x_1546_;
                } else {
                    v___x_1547_ = lean_st_ref_get(v___y_1543_);
                    v_mctx_1548_ = crate::leanh::lean_ctor_get(v___x_1547_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1548_);
                    crate::leanh::lean_dec(v___x_1547_);
                    v___x_1549_ = l_Lean_instantiateMVarsCore(v_mctx_1548_, v_e_1542_);
                    v_fst_1550_ = crate::leanh::lean_ctor_get(v___x_1549_, 0);
                    crate::leanh::lean_inc(v_fst_1550_);
                    v_snd_1551_ = crate::leanh::lean_ctor_get(v___x_1549_, 1);
                    crate::leanh::lean_inc(v_snd_1551_);
                    crate::leanh::lean_dec_ref(v___x_1549_);
                    v___x_1552_ = lean_st_ref_take(v___y_1543_);
                    v_cache_1553_ = crate::leanh::lean_ctor_get(v___x_1552_, 1);
                    v_zetaDeltaFVarIds_1554_ = crate::leanh::lean_ctor_get(v___x_1552_, 2);
                    v_postponed_1555_ = crate::leanh::lean_ctor_get(v___x_1552_, 3);
                    v_diag_1556_ = crate::leanh::lean_ctor_get(v___x_1552_, 4);
                    v_isSharedCheck_1565_ = (!crate::leanh::lean_is_exclusive(v___x_1552_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v_unused_1566_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                        crate::leanh::lean_dec(v_unused_1566_);
                        v___x_1558_ = v___x_1552_;
                        v_isShared_1559_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1556_);
                        crate::leanh::lean_inc(v_postponed_1555_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1554_);
                        crate::leanh::lean_inc(v_cache_1553_);
                        crate::leanh::lean_dec(v___x_1552_);
                        v___x_1558_ = crate::leanh::lean_box(0);
                        v_isShared_1559_ = v_isSharedCheck_1565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1558_, 0, v_snd_1551_);
                    v___x_1561_ = v___x_1558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1564_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_snd_1551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_cache_1553_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1564_,
                        2,
                        v_zetaDeltaFVarIds_1554_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_postponed_1555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_diag_1556_);
                    v___x_1561_ = v_reuseFailAlloc_1564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1562_ = lean_st_ref_set(v___y_1543_, v___x_1561_);
                v___x_1563_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1563_, 0, v_fst_1550_);
                return v___x_1563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg___boxed(
    mut v_e_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_1567_, v___y_1568_);
    crate::leanh::lean_dec(v___y_1568_);
    return v_res_1570_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(
    mut v_e_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_1571_, v___y_1573_);
    return v___x_1577_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(
    mut v_e_1578_: *mut crate::leanh::LeanObject,
    mut v___y_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(v_e_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
    crate::leanh::lean_dec(v___y_1582_);
    crate::leanh::lean_dec_ref(v___y_1581_);
    crate::leanh::lean_dec(v___y_1580_);
    crate::leanh::lean_dec_ref(v___y_1579_);
    return v_res_1584_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(
    mut v_args_1588_: *mut crate::leanh::LeanObject,
    mut v_transparency_1589_: u8,
    mut v_target_1590_: *mut crate::leanh::LeanObject,
    mut v_i_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xName_x3f_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xName_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1620_: u8 = 0;
    let mut v_ctxApprox_1621_: u8 = 0;
    let mut v_quasiPatternApprox_1622_: u8 = 0;
    let mut v_constApprox_1623_: u8 = 0;
    let mut v_isDefEqStuckEx_1624_: u8 = 0;
    let mut v_unificationHints_1625_: u8 = 0;
    let mut v_proofIrrelevance_1626_: u8 = 0;
    let mut v_assignSyntheticOpaque_1627_: u8 = 0;
    let mut v_offsetCnstrs_1628_: u8 = 0;
    let mut v_etaStruct_1629_: u8 = 0;
    let mut v_univApprox_1630_: u8 = 0;
    let mut v_iota_1631_: u8 = 0;
    let mut v_beta_1632_: u8 = 0;
    let mut v_proj_1633_: u8 = 0;
    let mut v_zeta_1634_: u8 = 0;
    let mut v_zetaDelta_1635_: u8 = 0;
    let mut v_zetaUnused_1636_: u8 = 0;
    let mut v_zetaHave_1637_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_trackZetaDelta_1641_: u8 = 0;
    let mut v_zetaDeltaSet_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1648_: u8 = 0;
    let mut v_inTypeClassResolution_1649_: u8 = 0;
    let mut v_cacheInferType_1650_: u8 = 0;
    let mut v_config_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u64 = 0;
    let mut v___x_1654_: u64 = 0;
    let mut v___x_1655_: u64 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u64 = 0;
    let mut v___x_1658_: u64 = 0;
    let mut v_key_1659_: u64 = 0;
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1672_: u8 = 0;
    let mut v_reuseFailAlloc_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_val_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1597_ = lean_array_get_size(v_args_1588_);
                v___x_1598_ = lean_nat_dec_lt(v_i_1591_, v___x_1597_);
                if v___x_1598_ == 0 {
                    v___x_1599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1599_, 0, v_target_1590_);
                    return v___x_1599_;
                } else {
                    v_arg_1600_ = lean_array_fget_borrowed(v_args_1588_, v_i_1591_);
                    v_expr_1601_ = crate::leanh::lean_ctor_get(v_arg_1600_, 0);
                    v_xName_x3f_1602_ = crate::leanh::lean_ctor_get(v_arg_1600_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1601_);
                    v___x_1603_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1601_, v_a_1593_);
                    if crate::leanh::lean_obj_tag(v___x_1603_) == 0 {
                        v_a_1604_ = crate::leanh::lean_ctor_get(v___x_1603_, 0);
                        crate::leanh::lean_inc_n(v_a_1604_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1603_, 1);
                        crate::leanh::lean_inc(v_a_1595_);
                        crate::leanh::lean_inc_ref(v_a_1594_);
                        crate::leanh::lean_inc(v_a_1593_);
                        crate::leanh::lean_inc_ref(v_a_1592_);
                        v___x_1605_ =
                            lean_infer_type(v_a_1604_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
                        if crate::leanh::lean_obj_tag(v___x_1605_) == 0 {
                            v_a_1606_ = crate::leanh::lean_ctor_get(v___x_1605_, 0);
                            crate::leanh::lean_inc(v_a_1606_);
                            crate::leanh::lean_dec_ref_known(v___x_1605_, 1);
                            v___x_1607_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1606_, v_a_1593_);
                            if crate::leanh::lean_obj_tag(v___x_1607_) == 0 {
                                v_a_1608_ = crate::leanh::lean_ctor_get(v___x_1607_, 0);
                                crate::leanh::lean_inc(v_a_1608_);
                                crate::leanh::lean_dec_ref_known(v___x_1607_, 1);
                                v___x_1609_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1610_ = lean_nat_add(v_i_1591_, v___x_1609_);
                                v___x_1611_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_1588_, v_transparency_1589_, v_target_1590_, v___x_1610_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
                                crate::leanh::lean_dec(v___x_1610_);
                                if crate::leanh::lean_obj_tag(v___x_1611_) == 0 {
                                    v_a_1612_ = crate::leanh::lean_ctor_get(v___x_1611_, 0);
                                    crate::leanh::lean_inc(v_a_1612_);
                                    crate::leanh::lean_dec_ref_known(v___x_1611_, 1);
                                    if crate::leanh::lean_obj_tag(v_xName_x3f_1602_) == 1 {
                                        v_val_1675_ =
                                            crate::leanh::lean_ctor_get(v_xName_x3f_1602_, 0);
                                        crate::leanh::lean_inc(v_val_1675_);
                                        v_xName_1614_ = v_val_1675_;
                                        v___y_1615_ = v_a_1592_;
                                        v___y_1616_ = v_a_1593_;
                                        v___y_1617_ = v_a_1594_;
                                        v___y_1618_ = v_a_1595_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1676_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1;
                                        v___x_1677_ = l_Lean_Core_mkFreshUserName(
                                            v___x_1676_,
                                            v_a_1594_,
                                            v_a_1595_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1677_) == 0 {
                                            v_a_1678_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
                                            crate::leanh::lean_inc(v_a_1678_);
                                            crate::leanh::lean_dec_ref_known(v___x_1677_, 1);
                                            v_xName_1614_ = v_a_1678_;
                                            v___y_1615_ = v_a_1592_;
                                            v___y_1616_ = v_a_1593_;
                                            v___y_1617_ = v_a_1594_;
                                            v___y_1618_ = v_a_1595_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_1612_);
                                            crate::leanh::lean_dec(v_a_1608_);
                                            crate::leanh::lean_dec(v_a_1604_);
                                            v_a_1679_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
                                            v_isSharedCheck_1686_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1677_))
                                                    as u8;
                                            if v_isSharedCheck_1686_ == 0 {
                                                v___x_1681_ = v___x_1677_;
                                                v_isShared_1682_ = v_isSharedCheck_1686_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1679_);
                                                crate::leanh::lean_dec(v___x_1677_);
                                                v___x_1681_ = crate::leanh::lean_box(0);
                                                v_isShared_1682_ = v_isSharedCheck_1686_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1608_);
                                    crate::leanh::lean_dec(v_a_1604_);
                                    return v___x_1611_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1604_);
                                crate::leanh::lean_dec_ref(v_target_1590_);
                                return v___x_1607_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1604_);
                            crate::leanh::lean_dec_ref(v_target_1590_);
                            return v___x_1605_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_target_1590_);
                        return v___x_1603_;
                    }
                }
            }
            1 => {
                v___x_1619_ = l_Lean_Meta_Context_config(v___y_1615_);
                v_foApprox_1620_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 0 as u32);
                v_ctxApprox_1621_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 1 as u32);
                v_quasiPatternApprox_1622_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1619_, 2 as u32);
                v_constApprox_1623_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 3 as u32);
                v_isDefEqStuckEx_1624_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 4 as u32);
                v_unificationHints_1625_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 5 as u32);
                v_proofIrrelevance_1626_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 6 as u32);
                v_assignSyntheticOpaque_1627_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1619_, 7 as u32);
                v_offsetCnstrs_1628_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 8 as u32);
                v_etaStruct_1629_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 10 as u32);
                v_univApprox_1630_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 11 as u32);
                v_iota_1631_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 12 as u32);
                v_beta_1632_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 13 as u32);
                v_proj_1633_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 14 as u32);
                v_zeta_1634_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 15 as u32);
                v_zetaDelta_1635_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 16 as u32);
                v_zetaUnused_1636_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 17 as u32);
                v_zetaHave_1637_ = crate::leanh::lean_ctor_get_uint8(v___x_1619_, 18 as u32);
                v_isSharedCheck_1674_ = (!crate::leanh::lean_is_exclusive(v___x_1619_)) as u8;
                if v_isSharedCheck_1674_ == 0 {
                    v___x_1639_ = v___x_1619_;
                    v_isShared_1640_ = v_isSharedCheck_1674_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1619_);
                    v___x_1639_ = crate::leanh::lean_box(0);
                    v_isShared_1640_ = v_isSharedCheck_1674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_1641_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1642_ = crate::leanh::lean_ctor_get(v___y_1615_, 1);
                v_lctx_1643_ = crate::leanh::lean_ctor_get(v___y_1615_, 2);
                v_localInstances_1644_ = crate::leanh::lean_ctor_get(v___y_1615_, 3);
                v_defEqCtx_x3f_1645_ = crate::leanh::lean_ctor_get(v___y_1615_, 4);
                v_synthPendingDepth_1646_ = crate::leanh::lean_ctor_get(v___y_1615_, 5);
                v_canUnfold_x3f_1647_ = crate::leanh::lean_ctor_get(v___y_1615_, 6);
                v_univApprox_1648_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1649_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1650_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_1640_ == 0 {
                    v_config_1652_ = v___x_1639_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1673_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        0 as u32,
                        v_foApprox_1620_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        1 as u32,
                        v_ctxApprox_1621_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        2 as u32,
                        v_quasiPatternApprox_1622_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        3 as u32,
                        v_constApprox_1623_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        4 as u32,
                        v_isDefEqStuckEx_1624_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        5 as u32,
                        v_unificationHints_1625_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        6 as u32,
                        v_proofIrrelevance_1626_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        7 as u32,
                        v_assignSyntheticOpaque_1627_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        8 as u32,
                        v_offsetCnstrs_1628_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        10 as u32,
                        v_etaStruct_1629_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        11 as u32,
                        v_univApprox_1630_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        12 as u32,
                        v_iota_1631_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        13 as u32,
                        v_beta_1632_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        14 as u32,
                        v_proj_1633_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        15 as u32,
                        v_zeta_1634_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        16 as u32,
                        v_zetaDelta_1635_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        17 as u32,
                        v_zetaUnused_1636_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1673_,
                        18 as u32,
                        v_zetaHave_1637_,
                    );
                    v_config_1652_ = v_reuseFailAlloc_1673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_1652_, 9 as u32, v_transparency_1589_);
                v___x_1653_ = l_Lean_Meta_Context_configKey(v___y_1615_);
                v___x_1654_ = 3u64;
                v___x_1655_ = lean_uint64_shift_right(v___x_1653_, v___x_1654_);
                v___x_1656_ = crate::leanh::lean_box(0);
                v___x_1657_ = lean_uint64_shift_left(v___x_1655_, v___x_1654_);
                v___x_1658_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_1589_);
                v_key_1659_ = lean_uint64_lor(v___x_1657_, v___x_1658_);
                v___x_1660_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1660_, 0, v_config_1652_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1660_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_1659_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1647_);
                crate::leanh::lean_inc(v_synthPendingDepth_1646_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1645_);
                crate::leanh::lean_inc_ref(v_localInstances_1644_);
                crate::leanh::lean_inc_ref(v_lctx_1643_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1642_);
                v___x_1661_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1661_, 0, v___x_1660_);
                crate::leanh::lean_ctor_set(v___x_1661_, 1, v_zetaDeltaSet_1642_);
                crate::leanh::lean_ctor_set(v___x_1661_, 2, v_lctx_1643_);
                crate::leanh::lean_ctor_set(v___x_1661_, 3, v_localInstances_1644_);
                crate::leanh::lean_ctor_set(v___x_1661_, 4, v_defEqCtx_x3f_1645_);
                crate::leanh::lean_ctor_set(v___x_1661_, 5, v_synthPendingDepth_1646_);
                crate::leanh::lean_ctor_set(v___x_1661_, 6, v_canUnfold_x3f_1647_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1641_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1648_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1649_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1650_,
                );
                v___x_1662_ = l_Lean_Meta_kabstract(
                    v_a_1612_,
                    v_a_1604_,
                    v___x_1656_,
                    v___x_1661_,
                    v___y_1616_,
                    v___y_1617_,
                    v___y_1618_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1661_, 7);
                if crate::leanh::lean_obj_tag(v___x_1662_) == 0 {
                    v_a_1663_ = crate::leanh::lean_ctor_get(v___x_1662_, 0);
                    v_isSharedCheck_1672_ = (!crate::leanh::lean_is_exclusive(v___x_1662_)) as u8;
                    if v_isSharedCheck_1672_ == 0 {
                        v___x_1665_ = v___x_1662_;
                        v_isShared_1666_ = v_isSharedCheck_1672_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1663_);
                        crate::leanh::lean_dec(v___x_1662_);
                        v___x_1665_ = crate::leanh::lean_box(0);
                        v_isShared_1666_ = v_isSharedCheck_1672_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_xName_1614_);
                    crate::leanh::lean_dec(v_a_1608_);
                    return v___x_1662_;
                }
            }
            4 => {
                v___x_1667_ = 0;
                v___x_1668_ = l_Lean_mkForall(v_xName_1614_, v___x_1667_, v_a_1608_, v_a_1663_);
                if v_isShared_1666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1668_);
                    v___x_1670_ = v___x_1665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
                    v___x_1670_ = v_reuseFailAlloc_1671_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1670_;
            }
            6 => {
                if v_isShared_1682_ == 0 {
                    v___x_1684_ = v___x_1681_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1685_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(
    mut v_args_1687_: *mut crate::leanh::LeanObject,
    mut v_transparency_1688_: *mut crate::leanh::LeanObject,
    mut v_target_1689_: *mut crate::leanh::LeanObject,
    mut v_i_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_1696_: u8 = 0;
    let mut v_res_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1696_ = (crate::leanh::lean_unbox(v_transparency_1688_) as u8);
    v_res_1697_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(
        v_args_1687_,
        v_transparency_boxed_1696_,
        v_target_1689_,
        v_i_1690_,
        v_a_1691_,
        v_a_1692_,
        v_a_1693_,
        v_a_1694_,
    );
    crate::leanh::lean_dec(v_a_1694_);
    crate::leanh::lean_dec_ref(v_a_1693_);
    crate::leanh::lean_dec(v_a_1692_);
    crate::leanh::lean_dec_ref(v_a_1691_);
    crate::leanh::lean_dec(v_i_1690_);
    crate::leanh::lean_dec_ref(v_args_1687_);
    return v_res_1697_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(
    mut v_args_1698_: *mut crate::leanh::LeanObject,
    mut v_xs_1699_: *mut crate::leanh::LeanObject,
    mut v_type_1700_: *mut crate::leanh::LeanObject,
    mut v_i_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hName_x3f_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v_fst_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1766_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_a_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_a_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_a_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_a_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_a_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_a_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1707_ = lean_array_get_size(v_xs_1699_);
                v___x_1708_ = lean_nat_dec_lt(v_i_1701_, v___x_1707_);
                if v___x_1708_ == 0 {
                    crate::leanh::lean_dec(v_i_1701_);
                    v___x_1709_ = crate::leanh::lean_box(0);
                    v___x_1710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1710_, 0, v___x_1709_);
                    crate::leanh::lean_ctor_set(v___x_1710_, 1, v_type_1700_);
                    v___x_1711_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1711_, 0, v___x_1710_);
                    return v___x_1711_;
                } else {
                    v___x_1712_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
                    v_arg_1713_ = lean_array_get_borrowed(v___x_1712_, v_args_1698_, v_i_1701_);
                    v_hName_x3f_1714_ = crate::leanh::lean_ctor_get(v_arg_1713_, 2);
                    if crate::leanh::lean_obj_tag(v_hName_x3f_1714_) == 1 {
                        v_expr_1715_ = crate::leanh::lean_ctor_get(v_arg_1713_, 0);
                        v_val_1716_ = crate::leanh::lean_ctor_get(v_hName_x3f_1714_, 0);
                        v___x_1747_ = lean_array_fget_borrowed(v_xs_1699_, v_i_1701_);
                        crate::leanh::lean_inc(v_a_1705_);
                        crate::leanh::lean_inc_ref(v_a_1704_);
                        crate::leanh::lean_inc(v_a_1703_);
                        crate::leanh::lean_inc_ref(v_a_1702_);
                        crate::leanh::lean_inc(v___x_1747_);
                        v___x_1748_ = lean_infer_type(
                            v___x_1747_,
                            v_a_1702_,
                            v_a_1703_,
                            v_a_1704_,
                            v_a_1705_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1748_) == 0 {
                            v_a_1749_ = crate::leanh::lean_ctor_get(v___x_1748_, 0);
                            crate::leanh::lean_inc(v_a_1749_);
                            crate::leanh::lean_dec_ref_known(v___x_1748_, 1);
                            crate::leanh::lean_inc_ref(v_expr_1715_);
                            v___x_1750_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1715_, v_a_1703_);
                            if crate::leanh::lean_obj_tag(v___x_1750_) == 0 {
                                v_a_1751_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
                                crate::leanh::lean_inc_n(v_a_1751_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1750_, 1);
                                crate::leanh::lean_inc(v_a_1705_);
                                crate::leanh::lean_inc_ref(v_a_1704_);
                                crate::leanh::lean_inc(v_a_1703_);
                                crate::leanh::lean_inc_ref(v_a_1702_);
                                v___x_1752_ = lean_infer_type(
                                    v_a_1751_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1752_) == 0 {
                                    v_a_1753_ = crate::leanh::lean_ctor_get(v___x_1752_, 0);
                                    crate::leanh::lean_inc(v_a_1753_);
                                    crate::leanh::lean_dec_ref_known(v___x_1752_, 1);
                                    v___x_1754_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1753_, v_a_1703_);
                                    if crate::leanh::lean_obj_tag(v___x_1754_) == 0 {
                                        v_a_1755_ = crate::leanh::lean_ctor_get(v___x_1754_, 0);
                                        crate::leanh::lean_inc(v_a_1755_);
                                        crate::leanh::lean_dec_ref_known(v___x_1754_, 1);
                                        v___x_1756_ = l_Lean_Meta_isExprDefEq(
                                            v_a_1749_, v_a_1755_, v_a_1702_, v_a_1703_, v_a_1704_,
                                            v_a_1705_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                                            v_a_1757_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                                            crate::leanh::lean_inc(v_a_1757_);
                                            crate::leanh::lean_dec_ref_known(v___x_1756_, 1);
                                            v___x_1758_ =
                                                (crate::leanh::lean_unbox(v_a_1757_) as u8);
                                            crate::leanh::lean_dec(v_a_1757_);
                                            if v___x_1758_ == 0 {
                                                crate::leanh::lean_inc(v___x_1747_);
                                                crate::leanh::lean_inc(v_a_1751_);
                                                v___x_1759_ = l_Lean_Meta_mkHEq(
                                                    v_a_1751_,
                                                    v___x_1747_,
                                                    v_a_1702_,
                                                    v_a_1703_,
                                                    v_a_1704_,
                                                    v_a_1705_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_1759_) == 0 {
                                                    v_a_1760_ =
                                                        crate::leanh::lean_ctor_get(v___x_1759_, 0);
                                                    crate::leanh::lean_inc(v_a_1760_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1759_,
                                                        1,
                                                    );
                                                    v___x_1761_ = l_Lean_Meta_mkHEqRefl(
                                                        v_a_1751_, v_a_1702_, v_a_1703_, v_a_1704_,
                                                        v_a_1705_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_1761_) == 0
                                                    {
                                                        v_a_1762_ = crate::leanh::lean_ctor_get(
                                                            v___x_1761_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_1762_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_1761_,
                                                            1,
                                                        );
                                                        v_fst_1718_ = v_a_1760_;
                                                        v_snd_1719_ = v_a_1762_;
                                                        v___y_1720_ = v_a_1702_;
                                                        v___y_1721_ = v_a_1703_;
                                                        v___y_1722_ = v_a_1704_;
                                                        v___y_1723_ = v_a_1705_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1760_);
                                                        crate::leanh::lean_dec(v_i_1701_);
                                                        crate::leanh::lean_dec_ref(v_type_1700_);
                                                        v_a_1763_ = crate::leanh::lean_ctor_get(
                                                            v___x_1761_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1770_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_1761_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1770_ == 0 {
                                                            v___x_1765_ = v___x_1761_;
                                                            v_isShared_1766_ =
                                                                v_isSharedCheck_1770_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_1763_);
                                                            crate::leanh::lean_dec(v___x_1761_);
                                                            v___x_1765_ = crate::leanh::lean_box(0);
                                                            v_isShared_1766_ =
                                                                v_isSharedCheck_1770_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_1751_);
                                                    crate::leanh::lean_dec(v_i_1701_);
                                                    crate::leanh::lean_dec_ref(v_type_1700_);
                                                    v_a_1771_ =
                                                        crate::leanh::lean_ctor_get(v___x_1759_, 0);
                                                    v_isSharedCheck_1778_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1759_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1778_ == 0 {
                                                        v___x_1773_ = v___x_1759_;
                                                        v_isShared_1774_ = v_isSharedCheck_1778_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1771_);
                                                        crate::leanh::lean_dec(v___x_1759_);
                                                        v___x_1773_ = crate::leanh::lean_box(0);
                                                        v_isShared_1774_ = v_isSharedCheck_1778_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_inc(v___x_1747_);
                                                crate::leanh::lean_inc(v_a_1751_);
                                                v___x_1779_ = l_Lean_Meta_mkEq(
                                                    v_a_1751_,
                                                    v___x_1747_,
                                                    v_a_1702_,
                                                    v_a_1703_,
                                                    v_a_1704_,
                                                    v_a_1705_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_1779_) == 0 {
                                                    v_a_1780_ =
                                                        crate::leanh::lean_ctor_get(v___x_1779_, 0);
                                                    crate::leanh::lean_inc(v_a_1780_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1779_,
                                                        1,
                                                    );
                                                    v___x_1781_ = l_Lean_Meta_mkEqRefl(
                                                        v_a_1751_, v_a_1702_, v_a_1703_, v_a_1704_,
                                                        v_a_1705_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_1781_) == 0
                                                    {
                                                        v_a_1782_ = crate::leanh::lean_ctor_get(
                                                            v___x_1781_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_1782_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_1781_,
                                                            1,
                                                        );
                                                        v_fst_1718_ = v_a_1780_;
                                                        v_snd_1719_ = v_a_1782_;
                                                        v___y_1720_ = v_a_1702_;
                                                        v___y_1721_ = v_a_1703_;
                                                        v___y_1722_ = v_a_1704_;
                                                        v___y_1723_ = v_a_1705_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1780_);
                                                        crate::leanh::lean_dec(v_i_1701_);
                                                        crate::leanh::lean_dec_ref(v_type_1700_);
                                                        v_a_1783_ = crate::leanh::lean_ctor_get(
                                                            v___x_1781_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1790_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_1781_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1790_ == 0 {
                                                            v___x_1785_ = v___x_1781_;
                                                            v_isShared_1786_ =
                                                                v_isSharedCheck_1790_;
                                                            state = 10;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_1783_);
                                                            crate::leanh::lean_dec(v___x_1781_);
                                                            v___x_1785_ = crate::leanh::lean_box(0);
                                                            v_isShared_1786_ =
                                                                v_isSharedCheck_1790_;
                                                            state = 10;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_1751_);
                                                    crate::leanh::lean_dec(v_i_1701_);
                                                    crate::leanh::lean_dec_ref(v_type_1700_);
                                                    v_a_1791_ =
                                                        crate::leanh::lean_ctor_get(v___x_1779_, 0);
                                                    v_isSharedCheck_1798_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1779_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1798_ == 0 {
                                                        v___x_1793_ = v___x_1779_;
                                                        v_isShared_1794_ = v_isSharedCheck_1798_;
                                                        state = 12;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1791_);
                                                        crate::leanh::lean_dec(v___x_1779_);
                                                        v___x_1793_ = crate::leanh::lean_box(0);
                                                        v_isShared_1794_ = v_isSharedCheck_1798_;
                                                        state = 12;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_1751_);
                                            crate::leanh::lean_dec(v_i_1701_);
                                            crate::leanh::lean_dec_ref(v_type_1700_);
                                            v_a_1799_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                                            v_isSharedCheck_1806_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1756_))
                                                    as u8;
                                            if v_isSharedCheck_1806_ == 0 {
                                                v___x_1801_ = v___x_1756_;
                                                v_isShared_1802_ = v_isSharedCheck_1806_;
                                                state = 14;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1799_);
                                                crate::leanh::lean_dec(v___x_1756_);
                                                v___x_1801_ = crate::leanh::lean_box(0);
                                                v_isShared_1802_ = v_isSharedCheck_1806_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1751_);
                                        crate::leanh::lean_dec(v_a_1749_);
                                        crate::leanh::lean_dec(v_i_1701_);
                                        crate::leanh::lean_dec_ref(v_type_1700_);
                                        v_a_1807_ = crate::leanh::lean_ctor_get(v___x_1754_, 0);
                                        v_isSharedCheck_1814_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1754_)) as u8;
                                        if v_isSharedCheck_1814_ == 0 {
                                            v___x_1809_ = v___x_1754_;
                                            v_isShared_1810_ = v_isSharedCheck_1814_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1807_);
                                            crate::leanh::lean_dec(v___x_1754_);
                                            v___x_1809_ = crate::leanh::lean_box(0);
                                            v_isShared_1810_ = v_isSharedCheck_1814_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1751_);
                                    crate::leanh::lean_dec(v_a_1749_);
                                    crate::leanh::lean_dec(v_i_1701_);
                                    crate::leanh::lean_dec_ref(v_type_1700_);
                                    v_a_1815_ = crate::leanh::lean_ctor_get(v___x_1752_, 0);
                                    v_isSharedCheck_1822_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1752_)) as u8;
                                    if v_isSharedCheck_1822_ == 0 {
                                        v___x_1817_ = v___x_1752_;
                                        v_isShared_1818_ = v_isSharedCheck_1822_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1815_);
                                        crate::leanh::lean_dec(v___x_1752_);
                                        v___x_1817_ = crate::leanh::lean_box(0);
                                        v_isShared_1818_ = v_isSharedCheck_1822_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1749_);
                                crate::leanh::lean_dec(v_i_1701_);
                                crate::leanh::lean_dec_ref(v_type_1700_);
                                v_a_1823_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
                                v_isSharedCheck_1830_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1750_)) as u8;
                                if v_isSharedCheck_1830_ == 0 {
                                    v___x_1825_ = v___x_1750_;
                                    v_isShared_1826_ = v_isSharedCheck_1830_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1823_);
                                    crate::leanh::lean_dec(v___x_1750_);
                                    v___x_1825_ = crate::leanh::lean_box(0);
                                    v_isShared_1826_ = v_isSharedCheck_1830_;
                                    state = 20;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_i_1701_);
                            crate::leanh::lean_dec_ref(v_type_1700_);
                            v_a_1831_ = crate::leanh::lean_ctor_get(v___x_1748_, 0);
                            v_isSharedCheck_1838_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1748_)) as u8;
                            if v_isSharedCheck_1838_ == 0 {
                                v___x_1833_ = v___x_1748_;
                                v_isShared_1834_ = v_isSharedCheck_1838_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1831_);
                                crate::leanh::lean_dec(v___x_1748_);
                                v___x_1833_ = crate::leanh::lean_box(0);
                                v_isShared_1834_ = v_isSharedCheck_1838_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        v___x_1839_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1840_ = lean_nat_add(v_i_1701_, v___x_1839_);
                        crate::leanh::lean_dec(v_i_1701_);
                        v_i_1701_ = v___x_1840_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1724_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1725_ = lean_nat_add(v_i_1701_, v___x_1724_);
                crate::leanh::lean_dec(v_i_1701_);
                v___x_1726_ =
                    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(
                        v_args_1698_,
                        v_xs_1699_,
                        v_type_1700_,
                        v___x_1725_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1726_) == 0 {
                    v_a_1727_ = crate::leanh::lean_ctor_get(v___x_1726_, 0);
                    v_isSharedCheck_1746_ = (!crate::leanh::lean_is_exclusive(v___x_1726_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v___x_1729_ = v___x_1726_;
                        v_isShared_1730_ = v_isSharedCheck_1746_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1727_);
                        crate::leanh::lean_dec(v___x_1726_);
                        v___x_1729_ = crate::leanh::lean_box(0);
                        v_isShared_1730_ = v_isSharedCheck_1746_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snd_1719_);
                    crate::leanh::lean_dec_ref(v_fst_1718_);
                    return v___x_1726_;
                }
            }
            2 => {
                v_fst_1731_ = crate::leanh::lean_ctor_get(v_a_1727_, 0);
                v_snd_1732_ = crate::leanh::lean_ctor_get(v_a_1727_, 1);
                v_isSharedCheck_1745_ = (!crate::leanh::lean_is_exclusive(v_a_1727_)) as u8;
                if v_isSharedCheck_1745_ == 0 {
                    v___x_1734_ = v_a_1727_;
                    v_isShared_1735_ = v_isSharedCheck_1745_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1732_);
                    crate::leanh::lean_inc(v_fst_1731_);
                    crate::leanh::lean_dec(v_a_1727_);
                    v___x_1734_ = crate::leanh::lean_box(0);
                    v_isShared_1735_ = v_isSharedCheck_1745_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1736_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1736_, 0, v_snd_1719_);
                crate::leanh::lean_ctor_set(v___x_1736_, 1, v_fst_1731_);
                v___x_1737_ = 0;
                crate::leanh::lean_inc(v_val_1716_);
                v___x_1738_ = l_Lean_mkForall(v_val_1716_, v___x_1737_, v_fst_1718_, v_snd_1732_);
                if v_isShared_1735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1734_, 1, v___x_1738_);
                    crate::leanh::lean_ctor_set(v___x_1734_, 0, v___x_1736_);
                    v___x_1740_ = v___x_1734_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1738_);
                    v___x_1740_ = v_reuseFailAlloc_1744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1740_);
                    v___x_1742_ = v___x_1729_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
                    v___x_1742_ = v_reuseFailAlloc_1743_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1742_;
            }
            6 => {
                if v_isShared_1766_ == 0 {
                    v___x_1768_ = v___x_1765_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
                    v___x_1768_ = v_reuseFailAlloc_1769_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1768_;
            }
            8 => {
                if v_isShared_1774_ == 0 {
                    v___x_1776_ = v___x_1773_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
                    v___x_1776_ = v_reuseFailAlloc_1777_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1776_;
            }
            10 => {
                if v_isShared_1786_ == 0 {
                    v___x_1788_ = v___x_1785_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
                    v___x_1788_ = v_reuseFailAlloc_1789_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1788_;
            }
            12 => {
                if v_isShared_1794_ == 0 {
                    v___x_1796_ = v___x_1793_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
                    v___x_1796_ = v_reuseFailAlloc_1797_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1796_;
            }
            14 => {
                if v_isShared_1802_ == 0 {
                    v___x_1804_ = v___x_1801_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
                    v___x_1804_ = v_reuseFailAlloc_1805_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1804_;
            }
            16 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1812_;
            }
            18 => {
                if v_isShared_1818_ == 0 {
                    v___x_1820_ = v___x_1817_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1820_;
            }
            20 => {
                if v_isShared_1826_ == 0 {
                    v___x_1828_ = v___x_1825_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
                    v___x_1828_ = v_reuseFailAlloc_1829_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1828_;
            }
            22 => {
                if v_isShared_1834_ == 0 {
                    v___x_1836_ = v___x_1833_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
                    v___x_1836_ = v_reuseFailAlloc_1837_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(
    mut v_args_1842_: *mut crate::leanh::LeanObject,
    mut v_xs_1843_: *mut crate::leanh::LeanObject,
    mut v_type_1844_: *mut crate::leanh::LeanObject,
    mut v_i_1845_: *mut crate::leanh::LeanObject,
    mut v_a_1846_: *mut crate::leanh::LeanObject,
    mut v_a_1847_: *mut crate::leanh::LeanObject,
    mut v_a_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(
        v_args_1842_,
        v_xs_1843_,
        v_type_1844_,
        v_i_1845_,
        v_a_1846_,
        v_a_1847_,
        v_a_1848_,
        v_a_1849_,
    );
    crate::leanh::lean_dec(v_a_1849_);
    crate::leanh::lean_dec_ref(v_a_1848_);
    crate::leanh::lean_dec(v_a_1847_);
    crate::leanh::lean_dec_ref(v_a_1846_);
    crate::leanh::lean_dec_ref(v_xs_1843_);
    crate::leanh::lean_dec_ref(v_args_1842_);
    return v_res_1851_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(
    mut v_k_1852_: *mut crate::leanh::LeanObject,
    mut v_b_1853_: *mut crate::leanh::LeanObject,
    mut v_c_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1858_);
    crate::leanh::lean_inc_ref(v___y_1857_);
    crate::leanh::lean_inc(v___y_1856_);
    crate::leanh::lean_inc_ref(v___y_1855_);
    v___x_1860_ = crate::leanh::lean_apply_7(
        v_k_1852_,
        v_b_1853_,
        v_c_1854_,
        v___y_1855_,
        v___y_1856_,
        v___y_1857_,
        v___y_1858_,
        crate::leanh::lean_box(0),
    );
    return v___x_1860_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(
    mut v_k_1861_: *mut crate::leanh::LeanObject,
    mut v_b_1862_: *mut crate::leanh::LeanObject,
    mut v_c_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_1861_, v_b_1862_, v_c_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
    crate::leanh::lean_dec(v___y_1867_);
    crate::leanh::lean_dec_ref(v___y_1866_);
    crate::leanh::lean_dec(v___y_1865_);
    crate::leanh::lean_dec_ref(v___y_1864_);
    return v_res_1869_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(
    mut v_type_1870_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1871_: *mut crate::leanh::LeanObject,
    mut v_k_1872_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1873_: u8,
    mut v_whnfType_1874_: u8,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1885_: u8 = 0;
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1889_: u8 = 0;
    let mut v_a_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1880_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1880_, 0, v_k_1872_);
                v___x_1881_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_1870_,
                    v_maxFVars_x3f_1871_,
                    v___f_1880_,
                    v_cleanupAnnotations_1873_,
                    v_whnfType_1874_,
                    v___y_1875_,
                    v___y_1876_,
                    v___y_1877_,
                    v___y_1878_,
                );
                if crate::leanh::lean_obj_tag(v___x_1881_) == 0 {
                    v_a_1882_ = crate::leanh::lean_ctor_get(v___x_1881_, 0);
                    v_isSharedCheck_1889_ = (!crate::leanh::lean_is_exclusive(v___x_1881_)) as u8;
                    if v_isSharedCheck_1889_ == 0 {
                        v___x_1884_ = v___x_1881_;
                        v_isShared_1885_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1882_);
                        crate::leanh::lean_dec(v___x_1881_);
                        v___x_1884_ = crate::leanh::lean_box(0);
                        v_isShared_1885_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1890_ = crate::leanh::lean_ctor_get(v___x_1881_, 0);
                    v_isSharedCheck_1897_ = (!crate::leanh::lean_is_exclusive(v___x_1881_)) as u8;
                    if v_isSharedCheck_1897_ == 0 {
                        v___x_1892_ = v___x_1881_;
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1890_);
                        crate::leanh::lean_dec(v___x_1881_);
                        v___x_1892_ = crate::leanh::lean_box(0);
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1885_ == 0 {
                    v___x_1887_ = v___x_1884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
                    v___x_1887_ = v_reuseFailAlloc_1888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1887_;
            }
            3 => {
                if v_isShared_1893_ == 0 {
                    v___x_1895_ = v___x_1892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(
    mut v_type_1898_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1899_: *mut crate::leanh::LeanObject,
    mut v_k_1900_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1901_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1908_: u8 = 0;
    let mut v_whnfType_boxed_1909_: u8 = 0;
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1908_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1901_) as u8);
    v_whnfType_boxed_1909_ = (crate::leanh::lean_unbox(v_whnfType_1902_) as u8);
    v_res_1910_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_1898_, v_maxFVars_x3f_1899_, v_k_1900_, v_cleanupAnnotations_boxed_1908_, v_whnfType_boxed_1909_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
    crate::leanh::lean_dec(v___y_1906_);
    crate::leanh::lean_dec_ref(v___y_1905_);
    crate::leanh::lean_dec(v___y_1904_);
    crate::leanh::lean_dec_ref(v___y_1903_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(
    mut v_00_u03b1_1911_: *mut crate::leanh::LeanObject,
    mut v_type_1912_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1913_: *mut crate::leanh::LeanObject,
    mut v_k_1914_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1915_: u8,
    mut v_whnfType_1916_: u8,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_1912_, v_maxFVars_x3f_1913_, v_k_1914_, v_cleanupAnnotations_1915_, v_whnfType_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
    return v___x_1922_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(
    mut v_00_u03b1_1923_: *mut crate::leanh::LeanObject,
    mut v_type_1924_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1925_: *mut crate::leanh::LeanObject,
    mut v_k_1926_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1927_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1934_: u8 = 0;
    let mut v_whnfType_boxed_1935_: u8 = 0;
    let mut v_res_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1934_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1927_) as u8);
    v_whnfType_boxed_1935_ = (crate::leanh::lean_unbox(v_whnfType_1928_) as u8);
    v_res_1936_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_00_u03b1_1923_, v_type_1924_, v_maxFVars_x3f_1925_, v_k_1926_, v_cleanupAnnotations_boxed_1934_, v_whnfType_boxed_1935_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
    crate::leanh::lean_dec(v___y_1932_);
    crate::leanh::lean_dec_ref(v___y_1931_);
    crate::leanh::lean_dec(v___y_1930_);
    crate::leanh::lean_dec_ref(v___y_1929_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(
    mut v_mvarId_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_a_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1944_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1937_,
                    v_x_1938_,
                    v___y_1939_,
                    v___y_1940_,
                    v___y_1941_,
                    v___y_1942_,
                );
                if crate::leanh::lean_obj_tag(v___x_1944_) == 0 {
                    v_a_1945_ = crate::leanh::lean_ctor_get(v___x_1944_, 0);
                    v_isSharedCheck_1952_ = (!crate::leanh::lean_is_exclusive(v___x_1944_)) as u8;
                    if v_isSharedCheck_1952_ == 0 {
                        v___x_1947_ = v___x_1944_;
                        v_isShared_1948_ = v_isSharedCheck_1952_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1945_);
                        crate::leanh::lean_dec(v___x_1944_);
                        v___x_1947_ = crate::leanh::lean_box(0);
                        v_isShared_1948_ = v_isSharedCheck_1952_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1953_ = crate::leanh::lean_ctor_get(v___x_1944_, 0);
                    v_isSharedCheck_1960_ = (!crate::leanh::lean_is_exclusive(v___x_1944_)) as u8;
                    if v_isSharedCheck_1960_ == 0 {
                        v___x_1955_ = v___x_1944_;
                        v_isShared_1956_ = v_isSharedCheck_1960_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1953_);
                        crate::leanh::lean_dec(v___x_1944_);
                        v___x_1955_ = crate::leanh::lean_box(0);
                        v_isShared_1956_ = v_isSharedCheck_1960_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1950_;
            }
            3 => {
                if v_isShared_1956_ == 0 {
                    v___x_1958_ = v___x_1955_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
                    v___x_1958_ = v_reuseFailAlloc_1959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(
    mut v_mvarId_1961_: *mut crate::leanh::LeanObject,
    mut v_x_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_1961_, v_x_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
    crate::leanh::lean_dec(v___y_1966_);
    crate::leanh::lean_dec_ref(v___y_1965_);
    crate::leanh::lean_dec(v___y_1964_);
    crate::leanh::lean_dec_ref(v___y_1963_);
    return v_res_1968_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(
    mut v_00_u03b1_1969_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1970_: *mut crate::leanh::LeanObject,
    mut v_x_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_1970_, v_x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
    return v___x_1977_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(
    mut v_00_u03b1_1978_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1979_: *mut crate::leanh::LeanObject,
    mut v_x_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1986_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_1978_, v_mvarId_1979_, v_x_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
    crate::leanh::lean_dec(v___y_1984_);
    crate::leanh::lean_dec_ref(v___y_1983_);
    crate::leanh::lean_dec(v___y_1982_);
    crate::leanh::lean_dec_ref(v___y_1981_);
    return v_res_1986_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(
    mut v_args_1987_: *mut crate::leanh::LeanObject,
    mut v___x_1988_: *mut crate::leanh::LeanObject,
    mut v___x_1989_: u8,
    mut v___x_1990_: u8,
    mut v_xs_1991_: *mut crate::leanh::LeanObject,
    mut v_type_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2005_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1998_ =
                    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(
                        v_args_1987_,
                        v_xs_1991_,
                        v_type_1992_,
                        v___x_1988_,
                        v___y_1993_,
                        v___y_1994_,
                        v___y_1995_,
                        v___y_1996_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1998_) == 0 {
                    v_a_1999_ = crate::leanh::lean_ctor_get(v___x_1998_, 0);
                    crate::leanh::lean_inc(v_a_1999_);
                    crate::leanh::lean_dec_ref_known(v___x_1998_, 1);
                    v_fst_2000_ = crate::leanh::lean_ctor_get(v_a_1999_, 0);
                    v_snd_2001_ = crate::leanh::lean_ctor_get(v_a_1999_, 1);
                    v_isSharedCheck_2026_ = (!crate::leanh::lean_is_exclusive(v_a_1999_)) as u8;
                    if v_isSharedCheck_2026_ == 0 {
                        v___x_2003_ = v_a_1999_;
                        v_isShared_2004_ = v_isSharedCheck_2026_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2001_);
                        crate::leanh::lean_inc(v_fst_2000_);
                        crate::leanh::lean_dec(v_a_1999_);
                        v___x_2003_ = crate::leanh::lean_box(0);
                        v_isShared_2004_ = v_isSharedCheck_2026_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1998_;
                }
            }
            1 => {
                v___x_2005_ = 1;
                v___x_2006_ = l_Lean_Meta_mkForallFVars(
                    v_xs_1991_,
                    v_snd_2001_,
                    v___x_1989_,
                    v___x_1990_,
                    v___x_1990_,
                    v___x_2005_,
                    v___y_1993_,
                    v___y_1994_,
                    v___y_1995_,
                    v___y_1996_,
                );
                if crate::leanh::lean_obj_tag(v___x_2006_) == 0 {
                    v_a_2007_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                    v_isSharedCheck_2017_ = (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_2009_ = v___x_2006_;
                        v_isShared_2010_ = v_isSharedCheck_2017_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2007_);
                        crate::leanh::lean_dec(v___x_2006_);
                        v___x_2009_ = crate::leanh::lean_box(0);
                        v_isShared_2010_ = v_isSharedCheck_2017_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2003_);
                    crate::leanh::lean_dec(v_fst_2000_);
                    v_a_2018_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                    v_isSharedCheck_2025_ = (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_2020_ = v___x_2006_;
                        v_isShared_2021_ = v_isSharedCheck_2025_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2018_);
                        crate::leanh::lean_dec(v___x_2006_);
                        v___x_2020_ = crate::leanh::lean_box(0);
                        v_isShared_2021_ = v_isSharedCheck_2025_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2003_, 1, v_a_2007_);
                    v___x_2012_ = v___x_2003_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_fst_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_a_2007_);
                    v___x_2012_ = v_reuseFailAlloc_2016_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2010_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2012_);
                    v___x_2014_ = v___x_2009_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
                    v___x_2014_ = v_reuseFailAlloc_2015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2014_;
            }
            5 => {
                if v_isShared_2021_ == 0 {
                    v___x_2023_ = v___x_2020_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(
    mut v_args_2027_: *mut crate::leanh::LeanObject,
    mut v___x_2028_: *mut crate::leanh::LeanObject,
    mut v___x_2029_: *mut crate::leanh::LeanObject,
    mut v___x_2030_: *mut crate::leanh::LeanObject,
    mut v_xs_2031_: *mut crate::leanh::LeanObject,
    mut v_type_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4823__boxed_2038_: u8 = 0;
    let mut v___x_4824__boxed_2039_: u8 = 0;
    let mut v_res_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4823__boxed_2038_ = (crate::leanh::lean_unbox(v___x_2029_) as u8);
    v___x_4824__boxed_2039_ = (crate::leanh::lean_unbox(v___x_2030_) as u8);
    v_res_2040_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(
        v_args_2027_,
        v___x_2028_,
        v___x_4823__boxed_2038_,
        v___x_4824__boxed_2039_,
        v_xs_2031_,
        v_type_2032_,
        v___y_2033_,
        v___y_2034_,
        v___y_2035_,
        v___y_2036_,
    );
    crate::leanh::lean_dec(v___y_2036_);
    crate::leanh::lean_dec_ref(v___y_2035_);
    crate::leanh::lean_dec(v___y_2034_);
    crate::leanh::lean_dec_ref(v___y_2033_);
    crate::leanh::lean_dec_ref(v_xs_2031_);
    crate::leanh::lean_dec_ref(v_args_2027_);
    return v_res_2040_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(
    mut v_as_2041_: *mut crate::leanh::LeanObject,
    mut v_i_2042_: usize,
    mut v_stop_2043_: usize,
) -> u8 {
    let mut v___x_2044_: u8 = 0;
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hName_x3f_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: usize = 0;
    let mut v___x_2051_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2044_ = lean_usize_dec_eq(v_i_2042_, v_stop_2043_);
                if v___x_2044_ == 0 {
                    v___x_2045_ = lean_array_uget_borrowed(v_as_2041_, v_i_2042_);
                    v_hName_x3f_2046_ = crate::leanh::lean_ctor_get(v___x_2045_, 2);
                    v___x_2047_ = 1;
                    if crate::leanh::lean_obj_tag(v_hName_x3f_2046_) == 0 {
                        if v___x_2044_ == 0 {
                            v___x_2048_ = 1usize;
                            v___x_2049_ = lean_usize_add(v_i_2042_, v___x_2048_);
                            v_i_2042_ = v___x_2049_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2047_;
                        }
                    } else {
                        return v___x_2047_;
                    }
                } else {
                    v___x_2051_ = 0;
                    return v___x_2051_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(
    mut v_as_2052_: *mut crate::leanh::LeanObject,
    mut v_i_2053_: *mut crate::leanh::LeanObject,
    mut v_stop_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2055_: usize = 0;
    let mut v_stop_boxed_2056_: usize = 0;
    let mut v_res_2057_: u8 = 0;
    let mut v_r_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2055_ = crate::leanh::lean_unbox_usize(v_i_2053_);
    crate::leanh::lean_dec(v_i_2053_);
    v_stop_boxed_2056_ = crate::leanh::lean_unbox_usize(v_stop_2054_);
    crate::leanh::lean_dec(v_stop_2054_);
    v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_2052_, v_i_boxed_2055_, v_stop_boxed_2056_);
    crate::leanh::lean_dec_ref(v_as_2052_);
    v_r_2058_ = crate::leanh::lean_box((v_res_2057_) as usize);
    return v_r_2058_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(
    mut v_sz_2059_: usize,
    mut v_i_2060_: usize,
    mut v_bs_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: u8 = 0;
    let mut v_v_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: usize = 0;
    let mut v___x_2068_: usize = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2062_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
                if v___x_2062_ == 0 {
                    return v_bs_2061_;
                } else {
                    v_v_2063_ = lean_array_uget_borrowed(v_bs_2061_, v_i_2060_);
                    v_expr_2064_ = crate::leanh::lean_ctor_get(v_v_2063_, 0);
                    crate::leanh::lean_inc_ref(v_expr_2064_);
                    v___x_2065_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2066_ = lean_array_uset(v_bs_2061_, v_i_2060_, v___x_2065_);
                    v___x_2067_ = 1usize;
                    v___x_2068_ = lean_usize_add(v_i_2060_, v___x_2067_);
                    v___x_2069_ = lean_array_uset(v_bs_x27_2066_, v_i_2060_, v_expr_2064_);
                    v_i_2060_ = v___x_2068_;
                    v_bs_2061_ = v___x_2069_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(
    mut v_sz_2071_: *mut crate::leanh::LeanObject,
    mut v_i_2072_: *mut crate::leanh::LeanObject,
    mut v_bs_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2074_: usize = 0;
    let mut v_i_boxed_2075_: usize = 0;
    let mut v_res_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2074_ = crate::leanh::lean_unbox_usize(v_sz_2071_);
    crate::leanh::lean_dec(v_sz_2071_);
    v_i_boxed_2075_ = crate::leanh::lean_unbox_usize(v_i_2072_);
    crate::leanh::lean_dec(v_i_2072_);
    v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_2074_, v_i_boxed_2075_, v_bs_2073_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(
    mut v_x_2077_: *mut crate::leanh::LeanObject,
    mut v_x_2078_: *mut crate::leanh::LeanObject,
    mut v_x_2079_: *mut crate::leanh::LeanObject,
    mut v_x_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2081_ = crate::leanh::lean_ctor_get(v_x_2077_, 0);
                v_vs_2082_ = crate::leanh::lean_ctor_get(v_x_2077_, 1);
                v_isSharedCheck_2106_ = (!crate::leanh::lean_is_exclusive(v_x_2077_)) as u8;
                if v_isSharedCheck_2106_ == 0 {
                    v___x_2084_ = v_x_2077_;
                    v_isShared_2085_ = v_isSharedCheck_2106_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2082_);
                    crate::leanh::lean_inc(v_ks_2081_);
                    crate::leanh::lean_dec(v_x_2077_);
                    v___x_2084_ = crate::leanh::lean_box(0);
                    v_isShared_2085_ = v_isSharedCheck_2106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2086_ = lean_array_get_size(v_ks_2081_);
                v___x_2087_ = lean_nat_dec_lt(v_x_2078_, v___x_2086_);
                if v___x_2087_ == 0 {
                    crate::leanh::lean_dec(v_x_2078_);
                    v___x_2088_ = lean_array_push(v_ks_2081_, v_x_2079_);
                    v___x_2089_ = lean_array_push(v_vs_2082_, v_x_2080_);
                    if v_isShared_2085_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2084_, 1, v___x_2089_);
                        crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2088_);
                        v___x_2091_ = v___x_2084_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2092_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2088_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2089_);
                        v___x_2091_ = v_reuseFailAlloc_2092_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2093_ = lean_array_fget_borrowed(v_ks_2081_, v_x_2078_);
                    v___x_2094_ = l_Lean_instBEqMVarId_beq(v_x_2079_, v_k_x27_2093_);
                    if v___x_2094_ == 0 {
                        if v_isShared_2085_ == 0 {
                            v___x_2096_ = v___x_2084_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2100_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_ks_2081_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_vs_2082_);
                            v___x_2096_ = v_reuseFailAlloc_2100_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2101_ = lean_array_fset(v_ks_2081_, v_x_2078_, v_x_2079_);
                        v___x_2102_ = lean_array_fset(v_vs_2082_, v_x_2078_, v_x_2080_);
                        crate::leanh::lean_dec(v_x_2078_);
                        if v_isShared_2085_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2084_, 1, v___x_2102_);
                            crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2101_);
                            v___x_2104_ = v___x_2084_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2105_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2101_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2102_);
                            v___x_2104_ = v_reuseFailAlloc_2105_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2091_;
            }
            3 => {
                v___x_2097_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2098_ = lean_nat_add(v_x_2078_, v___x_2097_);
                crate::leanh::lean_dec(v_x_2078_);
                v_x_2077_ = v___x_2096_;
                v_x_2078_ = v___x_2098_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(
    mut v_n_2107_: *mut crate::leanh::LeanObject,
    mut v_k_2108_: *mut crate::leanh::LeanObject,
    mut v_v_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2111_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_n_2107_, v___x_2110_, v_k_2108_, v_v_2109_);
    return v___x_2111_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_2112_: usize = 0;
    let mut v___x_2113_: usize = 0;
    let mut v___x_2114_: usize = 0;
    v___x_2112_ = 5usize;
    v___x_2113_ = 1usize;
    v___x_2114_ = lean_usize_shift_left(v___x_2113_, v___x_2112_);
    return v___x_2114_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_2115_: usize = 0;
    let mut v___x_2116_: usize = 0;
    let mut v___x_2117_: usize = 0;
    v___x_2115_ = 1usize;
    v___x_2116_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
    v___x_2117_ = lean_usize_sub(v___x_2116_, v___x_2115_);
    return v___x_2117_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(
    mut v_x_2119_: *mut crate::leanh::LeanObject,
    mut v_x_2120_: usize,
    mut v_x_2121_: usize,
    mut v_x_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: usize = 0;
    let mut v___x_2126_: usize = 0;
    let mut v___x_2127_: usize = 0;
    let mut v___x_2128_: usize = 0;
    let mut v_j_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v_v_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2148_: u8 = 0;
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_node_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: usize = 0;
    let mut v___x_2161_: usize = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_unused_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: u8 = 0;
    let mut v_ks_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: usize = 0;
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v_reuseFailAlloc_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2119_) == 0 {
                    v_es_2124_ = crate::leanh::lean_ctor_get(v_x_2119_, 0);
                    v___x_2125_ = 5usize;
                    v___x_2126_ = 1usize;
                    v___x_2127_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1);
                    v___x_2128_ = lean_usize_land(v_x_2120_, v___x_2127_);
                    v_j_2129_ = lean_usize_to_nat(v___x_2128_);
                    v___x_2130_ = lean_array_get_size(v_es_2124_);
                    v___x_2131_ = lean_nat_dec_lt(v_j_2129_, v___x_2130_);
                    if v___x_2131_ == 0 {
                        crate::leanh::lean_dec(v_j_2129_);
                        crate::leanh::lean_dec(v_x_2123_);
                        crate::leanh::lean_dec(v_x_2122_);
                        return v_x_2119_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2124_);
                        v_isSharedCheck_2168_ = (!crate::leanh::lean_is_exclusive(v_x_2119_)) as u8;
                        if v_isSharedCheck_2168_ == 0 {
                            v_unused_2169_ = crate::leanh::lean_ctor_get(v_x_2119_, 0);
                            crate::leanh::lean_dec(v_unused_2169_);
                            v___x_2133_ = v_x_2119_;
                            v_isShared_2134_ = v_isSharedCheck_2168_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2119_);
                            v___x_2133_ = crate::leanh::lean_box(0);
                            v_isShared_2134_ = v_isSharedCheck_2168_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2170_ = crate::leanh::lean_ctor_get(v_x_2119_, 0);
                    v_vs_2171_ = crate::leanh::lean_ctor_get(v_x_2119_, 1);
                    v_isSharedCheck_2191_ = (!crate::leanh::lean_is_exclusive(v_x_2119_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2173_ = v_x_2119_;
                        v_isShared_2174_ = v_isSharedCheck_2191_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2171_);
                        crate::leanh::lean_inc(v_ks_2170_);
                        crate::leanh::lean_dec(v_x_2119_);
                        v___x_2173_ = crate::leanh::lean_box(0);
                        v_isShared_2174_ = v_isSharedCheck_2191_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2135_ = lean_array_fget(v_es_2124_, v_j_2129_);
                v___x_2136_ = crate::leanh::lean_box(0);
                v_xs_x27_2137_ = lean_array_fset(v_es_2124_, v_j_2129_, v___x_2136_);
                match crate::leanh::lean_obj_tag(v_v_2135_) {
                    0 => {
                        v_key_2144_ = crate::leanh::lean_ctor_get(v_v_2135_, 0);
                        v_val_2145_ = crate::leanh::lean_ctor_get(v_v_2135_, 1);
                        v_isSharedCheck_2155_ = (!crate::leanh::lean_is_exclusive(v_v_2135_)) as u8;
                        if v_isSharedCheck_2155_ == 0 {
                            v___x_2147_ = v_v_2135_;
                            v_isShared_2148_ = v_isSharedCheck_2155_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2145_);
                            crate::leanh::lean_inc(v_key_2144_);
                            crate::leanh::lean_dec(v_v_2135_);
                            v___x_2147_ = crate::leanh::lean_box(0);
                            v_isShared_2148_ = v_isSharedCheck_2155_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2156_ = crate::leanh::lean_ctor_get(v_v_2135_, 0);
                        v_isSharedCheck_2166_ = (!crate::leanh::lean_is_exclusive(v_v_2135_)) as u8;
                        if v_isSharedCheck_2166_ == 0 {
                            v___x_2158_ = v_v_2135_;
                            v_isShared_2159_ = v_isSharedCheck_2166_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2156_);
                            crate::leanh::lean_dec(v_v_2135_);
                            v___x_2158_ = crate::leanh::lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2166_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2167_, 0, v_x_2122_);
                        crate::leanh::lean_ctor_set(v___x_2167_, 1, v_x_2123_);
                        v___y_2139_ = v___x_2167_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2140_ = lean_array_fset(v_xs_x27_2137_, v_j_2129_, v___y_2139_);
                crate::leanh::lean_dec(v_j_2129_);
                if v_isShared_2134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2140_);
                    v___x_2142_ = v___x_2133_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
                    v___x_2142_ = v_reuseFailAlloc_2143_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2142_;
            }
            4 => {
                v___x_2149_ = l_Lean_instBEqMVarId_beq(v_x_2122_, v_key_2144_);
                if v___x_2149_ == 0 {
                    crate::leanh::lean_del_object(v___x_2147_);
                    v___x_2150_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2144_,
                        v_val_2145_,
                        v_x_2122_,
                        v_x_2123_,
                    );
                    v___x_2151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2150_);
                    v___y_2139_ = v___x_2151_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2145_);
                    crate::leanh::lean_dec(v_key_2144_);
                    if v_isShared_2148_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2147_, 1, v_x_2123_);
                        crate::leanh::lean_ctor_set(v___x_2147_, 0, v_x_2122_);
                        v___x_2153_ = v___x_2147_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_x_2122_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_x_2123_);
                        v___x_2153_ = v_reuseFailAlloc_2154_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2139_ = v___x_2153_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2160_ = lean_usize_shift_right(v_x_2120_, v___x_2125_);
                v___x_2161_ = lean_usize_add(v_x_2121_, v___x_2126_);
                v___x_2162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_2156_, v___x_2160_, v___x_2161_, v_x_2122_, v_x_2123_);
                if v_isShared_2159_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2158_, 0, v___x_2162_);
                    v___x_2164_ = v___x_2158_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
                    v___x_2164_ = v_reuseFailAlloc_2165_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2139_ = v___x_2164_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2174_ == 0 {
                    v___x_2176_ = v___x_2173_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_ks_2170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_vs_2171_);
                    v___x_2176_ = v_reuseFailAlloc_2190_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2177_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_2176_, v_x_2122_, v_x_2123_);
                v___x_2185_ = 7usize;
                v___x_2186_ = lean_usize_dec_le(v___x_2185_, v_x_2121_);
                if v___x_2186_ == 0 {
                    v___x_2187_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2177_);
                    v___x_2188_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2189_ = lean_nat_dec_lt(v___x_2187_, v___x_2188_);
                    crate::leanh::lean_dec(v___x_2187_);
                    v___y_2179_ = v___x_2189_;
                    state = 10;
                    continue;
                } else {
                    v___y_2179_ = v___x_2186_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2179_ == 0 {
                    v_ks_2180_ = crate::leanh::lean_ctor_get(v_newNode_2177_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2180_);
                    v_vs_2181_ = crate::leanh::lean_ctor_get(v_newNode_2177_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2181_);
                    crate::leanh::lean_dec_ref(v_newNode_2177_);
                    v___x_2182_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2183_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2);
                    v___x_2184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_2121_, v_ks_2180_, v_vs_2181_, v___x_2182_, v___x_2183_);
                    crate::leanh::lean_dec_ref(v_vs_2181_);
                    crate::leanh::lean_dec_ref(v_ks_2180_);
                    return v___x_2184_;
                } else {
                    return v_newNode_2177_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(
    mut v_depth_2192_: usize,
    mut v_keys_2193_: *mut crate::leanh::LeanObject,
    mut v_vals_2194_: *mut crate::leanh::LeanObject,
    mut v_i_2195_: *mut crate::leanh::LeanObject,
    mut v_entries_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v_k_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: u64 = 0;
    let mut v_h_2202_: usize = 0;
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: usize = 0;
    let mut v___x_2207_: usize = 0;
    let mut v_h_2208_: usize = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2197_ = lean_array_get_size(v_keys_2193_);
                v___x_2198_ = lean_nat_dec_lt(v_i_2195_, v___x_2197_);
                if v___x_2198_ == 0 {
                    crate::leanh::lean_dec(v_i_2195_);
                    return v_entries_2196_;
                } else {
                    v_k_2199_ = lean_array_fget_borrowed(v_keys_2193_, v_i_2195_);
                    v_v_2200_ = lean_array_fget_borrowed(v_vals_2194_, v_i_2195_);
                    v___x_2201_ = l_Lean_instHashableMVarId_hash(v_k_2199_);
                    v_h_2202_ = lean_uint64_to_usize(v___x_2201_);
                    v___x_2203_ = 5usize;
                    v___x_2204_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2205_ = 1usize;
                    v___x_2206_ = lean_usize_sub(v_depth_2192_, v___x_2205_);
                    v___x_2207_ = lean_usize_mul(v___x_2203_, v___x_2206_);
                    v_h_2208_ = lean_usize_shift_right(v_h_2202_, v___x_2207_);
                    v___x_2209_ = lean_nat_add(v_i_2195_, v___x_2204_);
                    crate::leanh::lean_dec(v_i_2195_);
                    crate::leanh::lean_inc(v_v_2200_);
                    crate::leanh::lean_inc(v_k_2199_);
                    v___x_2210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_2196_, v_h_2208_, v_depth_2192_, v_k_2199_, v_v_2200_);
                    v_i_2195_ = v___x_2209_;
                    v_entries_2196_ = v___x_2210_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(
    mut v_depth_2212_: *mut crate::leanh::LeanObject,
    mut v_keys_2213_: *mut crate::leanh::LeanObject,
    mut v_vals_2214_: *mut crate::leanh::LeanObject,
    mut v_i_2215_: *mut crate::leanh::LeanObject,
    mut v_entries_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2217_: usize = 0;
    let mut v_res_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2217_ = crate::leanh::lean_unbox_usize(v_depth_2212_);
    crate::leanh::lean_dec(v_depth_2212_);
    v_res_2218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_2217_, v_keys_2213_, v_vals_2214_, v_i_2215_, v_entries_2216_);
    crate::leanh::lean_dec_ref(v_vals_2214_);
    crate::leanh::lean_dec_ref(v_keys_2213_);
    return v_res_2218_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_x_2219_: *mut crate::leanh::LeanObject,
    mut v_x_2220_: *mut crate::leanh::LeanObject,
    mut v_x_2221_: *mut crate::leanh::LeanObject,
    mut v_x_2222_: *mut crate::leanh::LeanObject,
    mut v_x_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5021__boxed_2224_: usize = 0;
    let mut v_x_5022__boxed_2225_: usize = 0;
    let mut v_res_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5021__boxed_2224_ = crate::leanh::lean_unbox_usize(v_x_2220_);
    crate::leanh::lean_dec(v_x_2220_);
    v_x_5022__boxed_2225_ = crate::leanh::lean_unbox_usize(v_x_2221_);
    crate::leanh::lean_dec(v_x_2221_);
    v_res_2226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_2219_, v_x_5021__boxed_2224_, v_x_5022__boxed_2225_, v_x_2222_, v_x_2223_);
    return v_res_2226_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(
    mut v_x_2227_: *mut crate::leanh::LeanObject,
    mut v_x_2228_: *mut crate::leanh::LeanObject,
    mut v_x_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: u64 = 0;
    let mut v___x_2231_: usize = 0;
    let mut v___x_2232_: usize = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_instHashableMVarId_hash(v_x_2228_);
    v___x_2231_ = lean_uint64_to_usize(v___x_2230_);
    v___x_2232_ = 1usize;
    v___x_2233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_2227_, v___x_2231_, v___x_2232_, v_x_2228_, v_x_2229_);
    return v___x_2233_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(
    mut v_mvarId_2234_: *mut crate::leanh::LeanObject,
    mut v_val_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v_depth_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2259_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2238_ = lean_st_ref_take(v___y_2236_);
                v_mctx_2239_ = crate::leanh::lean_ctor_get(v___x_2238_, 0);
                v_cache_2240_ = crate::leanh::lean_ctor_get(v___x_2238_, 1);
                v_zetaDeltaFVarIds_2241_ = crate::leanh::lean_ctor_get(v___x_2238_, 2);
                v_postponed_2242_ = crate::leanh::lean_ctor_get(v___x_2238_, 3);
                v_diag_2243_ = crate::leanh::lean_ctor_get(v___x_2238_, 4);
                v_isSharedCheck_2271_ = (!crate::leanh::lean_is_exclusive(v___x_2238_)) as u8;
                if v_isSharedCheck_2271_ == 0 {
                    v___x_2245_ = v___x_2238_;
                    v_isShared_2246_ = v_isSharedCheck_2271_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2243_);
                    crate::leanh::lean_inc(v_postponed_2242_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2241_);
                    crate::leanh::lean_inc(v_cache_2240_);
                    crate::leanh::lean_inc(v_mctx_2239_);
                    crate::leanh::lean_dec(v___x_2238_);
                    v___x_2245_ = crate::leanh::lean_box(0);
                    v_isShared_2246_ = v_isSharedCheck_2271_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2247_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 0);
                v_levelAssignDepth_2248_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 1);
                v_lmvarCounter_2249_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 2);
                v_mvarCounter_2250_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 3);
                v_lDecls_2251_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 4);
                v_decls_2252_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 5);
                v_userNames_2253_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 6);
                v_lAssignment_2254_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 7);
                v_eAssignment_2255_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 8);
                v_dAssignment_2256_ = crate::leanh::lean_ctor_get(v_mctx_2239_, 9);
                v_isSharedCheck_2270_ = (!crate::leanh::lean_is_exclusive(v_mctx_2239_)) as u8;
                if v_isSharedCheck_2270_ == 0 {
                    v___x_2258_ = v_mctx_2239_;
                    v_isShared_2259_ = v_isSharedCheck_2270_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2256_);
                    crate::leanh::lean_inc(v_eAssignment_2255_);
                    crate::leanh::lean_inc(v_lAssignment_2254_);
                    crate::leanh::lean_inc(v_userNames_2253_);
                    crate::leanh::lean_inc(v_decls_2252_);
                    crate::leanh::lean_inc(v_lDecls_2251_);
                    crate::leanh::lean_inc(v_mvarCounter_2250_);
                    crate::leanh::lean_inc(v_lmvarCounter_2249_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2248_);
                    crate::leanh::lean_inc(v_depth_2247_);
                    crate::leanh::lean_dec(v_mctx_2239_);
                    v___x_2258_ = crate::leanh::lean_box(0);
                    v_isShared_2259_ = v_isSharedCheck_2270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2260_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_2255_, v_mvarId_2234_, v_val_2235_);
                if v_isShared_2259_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2258_, 8, v___x_2260_);
                    v___x_2262_ = v___x_2258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_depth_2247_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2269_,
                        1,
                        v_levelAssignDepth_2248_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_lmvarCounter_2249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_mvarCounter_2250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_lDecls_2251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 5, v_decls_2252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 6, v_userNames_2253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 7, v_lAssignment_2254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 8, v___x_2260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 9, v_dAssignment_2256_);
                    v___x_2262_ = v_reuseFailAlloc_2269_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2262_);
                    v___x_2264_ = v___x_2245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2268_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_cache_2240_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2268_,
                        2,
                        v_zetaDeltaFVarIds_2241_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_postponed_2242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 4, v_diag_2243_);
                    v___x_2264_ = v_reuseFailAlloc_2268_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2265_ = lean_st_ref_set(v___y_2236_, v___x_2264_);
                v___x_2266_ = crate::leanh::lean_box(0);
                v___x_2267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2266_);
                return v___x_2267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(
    mut v_mvarId_2272_: *mut crate::leanh::LeanObject,
    mut v_val_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_2272_, v_val_2273_, v___y_2274_);
    crate::leanh::lean_dec(v___y_2274_);
    return v_res_2276_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2278_ =
        l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0;
    v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
    return v___x_2279_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(
    mut v_mvarId_2280_: *mut crate::leanh::LeanObject,
    mut v___x_2281_: *mut crate::leanh::LeanObject,
    mut v_args_2282_: *mut crate::leanh::LeanObject,
    mut v_transparency_2283_: u8,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2309_: u8 = 0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut v___y_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2331_: usize = 0;
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: u8 = 0;
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_a_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_reuseFailAlloc_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut v_a_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2395_: u8 = 0;
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut v_a_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_a_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut v_a_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2428_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_2281_);
                crate::leanh::lean_inc(v_mvarId_2280_);
                v___x_2289_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2280_,
                    v___x_2281_,
                    v___y_2284_,
                    v___y_2285_,
                    v___y_2286_,
                    v___y_2287_,
                );
                if crate::leanh::lean_obj_tag(v___x_2289_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2289_, 1);
                    crate::leanh::lean_inc(v_mvarId_2280_);
                    v___x_2290_ = l_Lean_MVarId_getTag(
                        v_mvarId_2280_,
                        v___y_2284_,
                        v___y_2285_,
                        v___y_2286_,
                        v___y_2287_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2290_) == 0 {
                        v_a_2291_ = crate::leanh::lean_ctor_get(v___x_2290_, 0);
                        crate::leanh::lean_inc(v_a_2291_);
                        crate::leanh::lean_dec_ref_known(v___x_2290_, 1);
                        crate::leanh::lean_inc(v_mvarId_2280_);
                        v___x_2292_ = l_Lean_MVarId_getType(
                            v_mvarId_2280_,
                            v___y_2284_,
                            v___y_2285_,
                            v___y_2286_,
                            v___y_2287_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2292_) == 0 {
                            v_a_2293_ = crate::leanh::lean_ctor_get(v___x_2292_, 0);
                            crate::leanh::lean_inc(v_a_2293_);
                            crate::leanh::lean_dec_ref_known(v___x_2292_, 1);
                            v___x_2294_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_2293_, v___y_2285_);
                            v_a_2295_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                            v_isSharedCheck_2408_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                            if v_isSharedCheck_2408_ == 0 {
                                v___x_2297_ = v___x_2294_;
                                v_isShared_2298_ = v_isSharedCheck_2408_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2295_);
                                crate::leanh::lean_dec(v___x_2294_);
                                v___x_2297_ = crate::leanh::lean_box(0);
                                v_isShared_2298_ = v_isSharedCheck_2408_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2291_);
                            crate::leanh::lean_dec_ref(v_args_2282_);
                            crate::leanh::lean_dec(v___x_2281_);
                            crate::leanh::lean_dec(v_mvarId_2280_);
                            v_a_2409_ = crate::leanh::lean_ctor_get(v___x_2292_, 0);
                            v_isSharedCheck_2416_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2292_)) as u8;
                            if v_isSharedCheck_2416_ == 0 {
                                v___x_2411_ = v___x_2292_;
                                v_isShared_2412_ = v_isSharedCheck_2416_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2409_);
                                crate::leanh::lean_dec(v___x_2292_);
                                v___x_2411_ = crate::leanh::lean_box(0);
                                v_isShared_2412_ = v_isSharedCheck_2416_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_2282_);
                        crate::leanh::lean_dec(v___x_2281_);
                        crate::leanh::lean_dec(v_mvarId_2280_);
                        v_a_2417_ = crate::leanh::lean_ctor_get(v___x_2290_, 0);
                        v_isSharedCheck_2424_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2290_)) as u8;
                        if v_isSharedCheck_2424_ == 0 {
                            v___x_2419_ = v___x_2290_;
                            v_isShared_2420_ = v_isSharedCheck_2424_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2417_);
                            crate::leanh::lean_dec(v___x_2290_);
                            v___x_2419_ = crate::leanh::lean_box(0);
                            v_isShared_2420_ = v_isSharedCheck_2424_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_2282_);
                    crate::leanh::lean_dec(v___x_2281_);
                    crate::leanh::lean_dec(v_mvarId_2280_);
                    v_a_2425_ = crate::leanh::lean_ctor_get(v___x_2289_, 0);
                    v_isSharedCheck_2432_ = (!crate::leanh::lean_is_exclusive(v___x_2289_)) as u8;
                    if v_isSharedCheck_2432_ == 0 {
                        v___x_2427_ = v___x_2289_;
                        v_isShared_2428_ = v_isSharedCheck_2432_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2425_);
                        crate::leanh::lean_dec(v___x_2289_);
                        v___x_2427_ = crate::leanh::lean_box(0);
                        v_isShared_2428_ = v_isSharedCheck_2432_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2299_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2300_ =
                    l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(
                        v_args_2282_,
                        v_transparency_2283_,
                        v_a_2295_,
                        v___x_2299_,
                        v___y_2284_,
                        v___y_2285_,
                        v___y_2286_,
                        v___y_2287_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2300_) == 0 {
                    v_a_2301_ = crate::leanh::lean_ctor_get(v___x_2300_, 0);
                    crate::leanh::lean_inc_n(v_a_2301_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2300_, 1);
                    v___x_2376_ = l_Lean_Meta_isTypeCorrect(
                        v_a_2301_,
                        v___y_2284_,
                        v___y_2285_,
                        v___y_2286_,
                        v___y_2287_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2376_) == 0 {
                        v_a_2377_ = crate::leanh::lean_ctor_get(v___x_2376_, 0);
                        crate::leanh::lean_inc(v_a_2377_);
                        crate::leanh::lean_dec_ref_known(v___x_2376_, 1);
                        v___x_2378_ = (crate::leanh::lean_unbox(v_a_2377_) as u8);
                        crate::leanh::lean_dec(v_a_2377_);
                        if v___x_2378_ == 0 {
                            v___x_2379_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once), _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
                            crate::leanh::lean_inc(v_a_2301_);
                            v___x_2380_ = l_Lean_indentExpr(v_a_2301_);
                            v___x_2381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2381_, 0, v___x_2379_);
                            crate::leanh::lean_ctor_set(v___x_2381_, 1, v___x_2380_);
                            v___x_2382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2382_, 0, v___x_2381_);
                            crate::leanh::lean_inc(v_mvarId_2280_);
                            v___x_2383_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_2281_,
                                v_mvarId_2280_,
                                v___x_2382_,
                                v___y_2284_,
                                v___y_2285_,
                                v___y_2286_,
                                v___y_2287_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2383_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2383_, 1);
                                v___y_2327_ = v___y_2284_;
                                v___y_2328_ = v___y_2285_;
                                v___y_2329_ = v___y_2286_;
                                v___y_2330_ = v___y_2287_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_2301_);
                                crate::leanh::lean_del_object(v___x_2297_);
                                crate::leanh::lean_dec(v_a_2291_);
                                crate::leanh::lean_dec_ref(v_args_2282_);
                                crate::leanh::lean_dec(v_mvarId_2280_);
                                v_a_2384_ = crate::leanh::lean_ctor_get(v___x_2383_, 0);
                                v_isSharedCheck_2391_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2383_)) as u8;
                                if v_isSharedCheck_2391_ == 0 {
                                    v___x_2386_ = v___x_2383_;
                                    v_isShared_2387_ = v_isSharedCheck_2391_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2384_);
                                    crate::leanh::lean_dec(v___x_2383_);
                                    v___x_2386_ = crate::leanh::lean_box(0);
                                    v_isShared_2387_ = v_isSharedCheck_2391_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2281_);
                            v___y_2327_ = v___y_2284_;
                            v___y_2328_ = v___y_2285_;
                            v___y_2329_ = v___y_2286_;
                            v___y_2330_ = v___y_2287_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2301_);
                        crate::leanh::lean_del_object(v___x_2297_);
                        crate::leanh::lean_dec(v_a_2291_);
                        crate::leanh::lean_dec_ref(v_args_2282_);
                        crate::leanh::lean_dec(v___x_2281_);
                        crate::leanh::lean_dec(v_mvarId_2280_);
                        v_a_2392_ = crate::leanh::lean_ctor_get(v___x_2376_, 0);
                        v_isSharedCheck_2399_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2376_)) as u8;
                        if v_isSharedCheck_2399_ == 0 {
                            v___x_2394_ = v___x_2376_;
                            v_isShared_2395_ = v_isSharedCheck_2399_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2392_);
                            crate::leanh::lean_dec(v___x_2376_);
                            v___x_2394_ = crate::leanh::lean_box(0);
                            v_isShared_2395_ = v_isSharedCheck_2399_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2297_);
                    crate::leanh::lean_dec(v_a_2291_);
                    crate::leanh::lean_dec_ref(v_args_2282_);
                    crate::leanh::lean_dec(v___x_2281_);
                    crate::leanh::lean_dec(v_mvarId_2280_);
                    v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2300_, 0);
                    v_isSharedCheck_2407_ = (!crate::leanh::lean_is_exclusive(v___x_2300_)) as u8;
                    if v_isSharedCheck_2407_ == 0 {
                        v___x_2402_ = v___x_2300_;
                        v_isShared_2403_ = v_isSharedCheck_2407_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2400_);
                        crate::leanh::lean_dec(v___x_2300_);
                        v___x_2402_ = crate::leanh::lean_box(0);
                        v_isShared_2403_ = v_isSharedCheck_2407_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2310_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_a_2301_,
                    v_a_2291_,
                    v___y_2306_,
                    v___y_2303_,
                    v___y_2308_,
                    v___y_2305_,
                );
                if crate::leanh::lean_obj_tag(v___x_2310_) == 0 {
                    v_a_2311_ = crate::leanh::lean_ctor_get(v___x_2310_, 0);
                    crate::leanh::lean_inc_n(v_a_2311_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2310_, 1);
                    v___x_2312_ = l_Lean_mkAppN(v_a_2311_, v___y_2304_);
                    crate::leanh::lean_dec_ref(v___y_2304_);
                    v___x_2313_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_2280_, v___x_2312_, v___y_2303_);
                    crate::leanh::lean_dec_ref(v___x_2313_);
                    v___x_2314_ = 1;
                    v___x_2315_ = l_Lean_Expr_mvarId_x21(v_a_2311_);
                    crate::leanh::lean_dec(v_a_2311_);
                    v___x_2316_ = crate::leanh::lean_box(0);
                    v___x_2317_ = l_Lean_Meta_introNCore(
                        v___x_2315_,
                        v___y_2307_,
                        v___x_2316_,
                        v___y_2309_,
                        v___x_2314_,
                        v___y_2306_,
                        v___y_2303_,
                        v___y_2308_,
                        v___y_2305_,
                    );
                    return v___x_2317_;
                } else {
                    crate::leanh::lean_dec(v___y_2307_);
                    crate::leanh::lean_dec_ref(v___y_2304_);
                    crate::leanh::lean_dec(v_mvarId_2280_);
                    v_a_2318_ = crate::leanh::lean_ctor_get(v___x_2310_, 0);
                    v_isSharedCheck_2325_ = (!crate::leanh::lean_is_exclusive(v___x_2310_)) as u8;
                    if v_isSharedCheck_2325_ == 0 {
                        v___x_2320_ = v___x_2310_;
                        v_isShared_2321_ = v_isSharedCheck_2325_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2318_);
                        crate::leanh::lean_dec(v___x_2310_);
                        v___x_2320_ = crate::leanh::lean_box(0);
                        v_isShared_2321_ = v_isSharedCheck_2325_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2321_ == 0 {
                    v___x_2323_ = v___x_2320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
                    v___x_2323_ = v_reuseFailAlloc_2324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2323_;
            }
            5 => {
                v_sz_2331_ = lean_array_size(v_args_2282_);
                v___x_2332_ = 0usize;
                crate::leanh::lean_inc_ref(v_args_2282_);
                v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_2331_, v___x_2332_, v_args_2282_);
                v___x_2334_ = lean_array_get_size(v_args_2282_);
                v___x_2335_ = lean_nat_dec_lt(v___x_2299_, v___x_2334_);
                if v___x_2335_ == 0 {
                    crate::leanh::lean_del_object(v___x_2297_);
                    crate::leanh::lean_dec_ref(v_args_2282_);
                    v___y_2303_ = v___y_2328_;
                    v___y_2304_ = v___x_2333_;
                    v___y_2305_ = v___y_2330_;
                    v___y_2306_ = v___y_2327_;
                    v___y_2307_ = v___x_2334_;
                    v___y_2308_ = v___y_2329_;
                    v___y_2309_ = v___x_2335_;
                    state = 2;
                    continue;
                } else {
                    if v___x_2335_ == 0 {
                        crate::leanh::lean_del_object(v___x_2297_);
                        crate::leanh::lean_dec_ref(v_args_2282_);
                        v___y_2303_ = v___y_2328_;
                        v___y_2304_ = v___x_2333_;
                        v___y_2305_ = v___y_2330_;
                        v___y_2306_ = v___y_2327_;
                        v___y_2307_ = v___x_2334_;
                        v___y_2308_ = v___y_2329_;
                        v___y_2309_ = v___x_2335_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2336_ = lean_usize_of_nat(v___x_2334_);
                        v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_2282_, v___x_2332_, v___x_2336_);
                        if v___x_2337_ == 0 {
                            crate::leanh::lean_del_object(v___x_2297_);
                            crate::leanh::lean_dec_ref(v_args_2282_);
                            v___y_2303_ = v___y_2328_;
                            v___y_2304_ = v___x_2333_;
                            v___y_2305_ = v___y_2330_;
                            v___y_2306_ = v___y_2327_;
                            v___y_2307_ = v___x_2334_;
                            v___y_2308_ = v___y_2329_;
                            v___y_2309_ = v___x_2337_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2338_ = 0;
                            v___x_2339_ = crate::leanh::lean_box((v___x_2338_) as usize);
                            v___x_2340_ = crate::leanh::lean_box((v___x_2337_) as usize);
                            v___f_2341_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                            crate::leanh::lean_closure_set(v___f_2341_, 0, v_args_2282_);
                            crate::leanh::lean_closure_set(v___f_2341_, 1, v___x_2299_);
                            crate::leanh::lean_closure_set(v___f_2341_, 2, v___x_2339_);
                            crate::leanh::lean_closure_set(v___f_2341_, 3, v___x_2340_);
                            if v_isShared_2298_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2297_, 1);
                                crate::leanh::lean_ctor_set(v___x_2297_, 0, v___x_2334_);
                                v___x_2343_ = v___x_2297_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2375_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2334_);
                                v___x_2343_ = v_reuseFailAlloc_2375_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_2344_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_2301_, v___x_2343_, v___f_2341_, v___x_2338_, v___x_2338_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                if crate::leanh::lean_obj_tag(v___x_2344_) == 0 {
                    v_a_2345_ = crate::leanh::lean_ctor_get(v___x_2344_, 0);
                    crate::leanh::lean_inc(v_a_2345_);
                    crate::leanh::lean_dec_ref_known(v___x_2344_, 1);
                    v_fst_2346_ = crate::leanh::lean_ctor_get(v_a_2345_, 0);
                    crate::leanh::lean_inc(v_fst_2346_);
                    v_snd_2347_ = crate::leanh::lean_ctor_get(v_a_2345_, 1);
                    crate::leanh::lean_inc(v_snd_2347_);
                    crate::leanh::lean_dec(v_a_2345_);
                    v___x_2348_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_snd_2347_,
                        v_a_2291_,
                        v___y_2327_,
                        v___y_2328_,
                        v___y_2329_,
                        v___y_2330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                        v_a_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                        crate::leanh::lean_inc_n(v_a_2349_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2348_, 1);
                        v___x_2350_ = l_Lean_mkAppN(v_a_2349_, v___x_2333_);
                        crate::leanh::lean_dec_ref(v___x_2333_);
                        crate::leanh::lean_inc(v_fst_2346_);
                        v___x_2351_ = lean_array_mk(v_fst_2346_);
                        v___x_2352_ = l_Lean_mkAppN(v___x_2350_, v___x_2351_);
                        crate::leanh::lean_dec_ref(v___x_2351_);
                        v___x_2353_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_2280_, v___x_2352_, v___y_2328_);
                        crate::leanh::lean_dec_ref(v___x_2353_);
                        v___x_2354_ = l_Lean_Expr_mvarId_x21(v_a_2349_);
                        crate::leanh::lean_dec(v_a_2349_);
                        v___x_2355_ = l_List_lengthTR___redArg(v_fst_2346_);
                        crate::leanh::lean_dec(v_fst_2346_);
                        v___x_2356_ = lean_nat_add(v___x_2334_, v___x_2355_);
                        crate::leanh::lean_dec(v___x_2355_);
                        v___x_2357_ = crate::leanh::lean_box(0);
                        v___x_2358_ = l_Lean_Meta_introNCore(
                            v___x_2354_,
                            v___x_2356_,
                            v___x_2357_,
                            v___x_2338_,
                            v___x_2337_,
                            v___y_2327_,
                            v___y_2328_,
                            v___y_2329_,
                            v___y_2330_,
                        );
                        return v___x_2358_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2346_);
                        crate::leanh::lean_dec_ref(v___x_2333_);
                        crate::leanh::lean_dec(v_mvarId_2280_);
                        v_a_2359_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2366_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2366_ == 0 {
                            v___x_2361_ = v___x_2348_;
                            v_isShared_2362_ = v_isSharedCheck_2366_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2359_);
                            crate::leanh::lean_dec(v___x_2348_);
                            v___x_2361_ = crate::leanh::lean_box(0);
                            v_isShared_2362_ = v_isSharedCheck_2366_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2333_);
                    crate::leanh::lean_dec(v_a_2291_);
                    crate::leanh::lean_dec(v_mvarId_2280_);
                    v_a_2367_ = crate::leanh::lean_ctor_get(v___x_2344_, 0);
                    v_isSharedCheck_2374_ = (!crate::leanh::lean_is_exclusive(v___x_2344_)) as u8;
                    if v_isSharedCheck_2374_ == 0 {
                        v___x_2369_ = v___x_2344_;
                        v_isShared_2370_ = v_isSharedCheck_2374_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2367_);
                        crate::leanh::lean_dec(v___x_2344_);
                        v___x_2369_ = crate::leanh::lean_box(0);
                        v_isShared_2370_ = v_isSharedCheck_2374_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2362_ == 0 {
                    v___x_2364_ = v___x_2361_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
                    v___x_2364_ = v_reuseFailAlloc_2365_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2364_;
            }
            9 => {
                if v_isShared_2370_ == 0 {
                    v___x_2372_ = v___x_2369_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
                    v___x_2372_ = v_reuseFailAlloc_2373_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2372_;
            }
            11 => {
                if v_isShared_2387_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2389_;
            }
            13 => {
                if v_isShared_2395_ == 0 {
                    v___x_2397_ = v___x_2394_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
                    v___x_2397_ = v_reuseFailAlloc_2398_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2397_;
            }
            15 => {
                if v_isShared_2403_ == 0 {
                    v___x_2405_ = v___x_2402_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
                    v___x_2405_ = v_reuseFailAlloc_2406_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2405_;
            }
            17 => {
                if v_isShared_2412_ == 0 {
                    v___x_2414_ = v___x_2411_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
                    v___x_2414_ = v_reuseFailAlloc_2415_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2414_;
            }
            19 => {
                if v_isShared_2420_ == 0 {
                    v___x_2422_ = v___x_2419_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
                    v___x_2422_ = v_reuseFailAlloc_2423_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2422_;
            }
            21 => {
                if v_isShared_2428_ == 0 {
                    v___x_2430_ = v___x_2427_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
                    v___x_2430_ = v_reuseFailAlloc_2431_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(
    mut v_mvarId_2433_: *mut crate::leanh::LeanObject,
    mut v___x_2434_: *mut crate::leanh::LeanObject,
    mut v_args_2435_: *mut crate::leanh::LeanObject,
    mut v_transparency_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_2442_: u8 = 0;
    let mut v_res_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_2442_ = (crate::leanh::lean_unbox(v_transparency_2436_) as u8);
    v_res_2443_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(
        v_mvarId_2433_,
        v___x_2434_,
        v_args_2435_,
        v_transparency_boxed_2442_,
        v___y_2437_,
        v___y_2438_,
        v___y_2439_,
        v___y_2440_,
    );
    crate::leanh::lean_dec(v___y_2440_);
    crate::leanh::lean_dec_ref(v___y_2439_);
    crate::leanh::lean_dec(v___y_2438_);
    crate::leanh::lean_dec_ref(v___y_2437_);
    return v_res_2443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(
    mut v_mvarId_2447_: *mut crate::leanh::LeanObject,
    mut v_args_2448_: *mut crate::leanh::LeanObject,
    mut v_transparency_2449_: u8,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_a_2453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1;
    v___x_2456_ = crate::leanh::lean_box((v_transparency_2449_) as usize);
    crate::leanh::lean_inc(v_mvarId_2447_);
    v___f_2457_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2457_, 0, v_mvarId_2447_);
    crate::leanh::lean_closure_set(v___f_2457_, 1, v___x_2455_);
    crate::leanh::lean_closure_set(v___f_2457_, 2, v_args_2448_);
    crate::leanh::lean_closure_set(v___f_2457_, 3, v___x_2456_);
    v___x_2458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_2447_, v___f_2457_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
    return v___x_2458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(
    mut v_mvarId_2459_: *mut crate::leanh::LeanObject,
    mut v_args_2460_: *mut crate::leanh::LeanObject,
    mut v_transparency_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_2467_: u8 = 0;
    let mut v_res_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_2467_ = (crate::leanh::lean_unbox(v_transparency_2461_) as u8);
    v_res_2468_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(
        v_mvarId_2459_,
        v_args_2460_,
        v_transparency_boxed_2467_,
        v_a_2462_,
        v_a_2463_,
        v_a_2464_,
        v_a_2465_,
    );
    crate::leanh::lean_dec(v_a_2465_);
    crate::leanh::lean_dec_ref(v_a_2464_);
    crate::leanh::lean_dec(v_a_2463_);
    crate::leanh::lean_dec_ref(v_a_2462_);
    return v_res_2468_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(
    mut v_mvarId_2469_: *mut crate::leanh::LeanObject,
    mut v_val_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_2469_, v_val_2470_, v___y_2472_);
    return v___x_2476_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(
    mut v_mvarId_2477_: *mut crate::leanh::LeanObject,
    mut v_val_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_2477_, v_val_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
    crate::leanh::lean_dec(v___y_2482_);
    crate::leanh::lean_dec_ref(v___y_2481_);
    crate::leanh::lean_dec(v___y_2480_);
    crate::leanh::lean_dec_ref(v___y_2479_);
    return v_res_2484_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(
    mut v_00_u03b2_2485_: *mut crate::leanh::LeanObject,
    mut v_x_2486_: *mut crate::leanh::LeanObject,
    mut v_x_2487_: *mut crate::leanh::LeanObject,
    mut v_x_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_2486_, v_x_2487_, v_x_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(
    mut v_00_u03b2_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: *mut crate::leanh::LeanObject,
    mut v_x_2492_: usize,
    mut v_x_2493_: usize,
    mut v_x_2494_: *mut crate::leanh::LeanObject,
    mut v_x_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_2491_, v_x_2492_, v_x_2493_, v_x_2494_, v_x_2495_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_2497_: *mut crate::leanh::LeanObject,
    mut v_x_2498_: *mut crate::leanh::LeanObject,
    mut v_x_2499_: *mut crate::leanh::LeanObject,
    mut v_x_2500_: *mut crate::leanh::LeanObject,
    mut v_x_2501_: *mut crate::leanh::LeanObject,
    mut v_x_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5606__boxed_2503_: usize = 0;
    let mut v_x_5607__boxed_2504_: usize = 0;
    let mut v_res_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5606__boxed_2503_ = crate::leanh::lean_unbox_usize(v_x_2499_);
    crate::leanh::lean_dec(v_x_2499_);
    v_x_5607__boxed_2504_ = crate::leanh::lean_unbox_usize(v_x_2500_);
    crate::leanh::lean_dec(v_x_2500_);
    v_res_2505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_2497_, v_x_2498_, v_x_5606__boxed_2503_, v_x_5607__boxed_2504_, v_x_2501_, v_x_2502_);
    return v_res_2505_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(
    mut v_00_u03b2_2506_: *mut crate::leanh::LeanObject,
    mut v_n_2507_: *mut crate::leanh::LeanObject,
    mut v_k_2508_: *mut crate::leanh::LeanObject,
    mut v_v_2509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_2507_, v_k_2508_, v_v_2509_);
    return v___x_2510_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(
    mut v_00_u03b2_2511_: *mut crate::leanh::LeanObject,
    mut v_depth_2512_: usize,
    mut v_keys_2513_: *mut crate::leanh::LeanObject,
    mut v_vals_2514_: *mut crate::leanh::LeanObject,
    mut v_heq_2515_: *mut crate::leanh::LeanObject,
    mut v_i_2516_: *mut crate::leanh::LeanObject,
    mut v_entries_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_2512_, v_keys_2513_, v_vals_2514_, v_i_2516_, v_entries_2517_);
    return v___x_2518_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(
    mut v_00_u03b2_2519_: *mut crate::leanh::LeanObject,
    mut v_depth_2520_: *mut crate::leanh::LeanObject,
    mut v_keys_2521_: *mut crate::leanh::LeanObject,
    mut v_vals_2522_: *mut crate::leanh::LeanObject,
    mut v_heq_2523_: *mut crate::leanh::LeanObject,
    mut v_i_2524_: *mut crate::leanh::LeanObject,
    mut v_entries_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2526_: usize = 0;
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2526_ = crate::leanh::lean_unbox_usize(v_depth_2520_);
    crate::leanh::lean_dec(v_depth_2520_);
    v_res_2527_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_2519_, v_depth_boxed_2526_, v_keys_2521_, v_vals_2522_, v_heq_2523_, v_i_2524_, v_entries_2525_);
    crate::leanh::lean_dec_ref(v_vals_2522_);
    crate::leanh::lean_dec_ref(v_keys_2521_);
    return v_res_2527_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(
    mut v_00_u03b2_2528_: *mut crate::leanh::LeanObject,
    mut v_x_2529_: *mut crate::leanh::LeanObject,
    mut v_x_2530_: *mut crate::leanh::LeanObject,
    mut v_x_2531_: *mut crate::leanh::LeanObject,
    mut v_x_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_2529_, v_x_2530_, v_x_2531_, v_x_2532_);
    return v___x_2533_;
}
pub unsafe fn l_Lean_MVarId_generalize(
    mut v_mvarId_2534_: *mut crate::leanh::LeanObject,
    mut v_args_2535_: *mut crate::leanh::LeanObject,
    mut v_transparency_2536_: u8,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
    mut v_a_2539_: *mut crate::leanh::LeanObject,
    mut v_a_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(
        v_mvarId_2534_,
        v_args_2535_,
        v_transparency_2536_,
        v_a_2537_,
        v_a_2538_,
        v_a_2539_,
        v_a_2540_,
    );
    return v___x_2542_;
}
pub unsafe fn l_Lean_MVarId_generalize___boxed(
    mut v_mvarId_2543_: *mut crate::leanh::LeanObject,
    mut v_args_2544_: *mut crate::leanh::LeanObject,
    mut v_transparency_2545_: *mut crate::leanh::LeanObject,
    mut v_a_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
    mut v_a_2549_: *mut crate::leanh::LeanObject,
    mut v_a_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_2551_: u8 = 0;
    let mut v_res_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_2551_ = (crate::leanh::lean_unbox(v_transparency_2545_) as u8);
    v_res_2552_ = l_Lean_MVarId_generalize(
        v_mvarId_2543_,
        v_args_2544_,
        v_transparency_boxed_2551_,
        v_a_2546_,
        v_a_2547_,
        v_a_2548_,
        v_a_2549_,
    );
    crate::leanh::lean_dec(v_a_2549_);
    crate::leanh::lean_dec_ref(v_a_2548_);
    crate::leanh::lean_dec(v_a_2547_);
    crate::leanh::lean_dec_ref(v_a_2546_);
    return v_res_2552_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(
    mut v_as_2553_: *mut crate::leanh::LeanObject,
    mut v_sz_2554_: usize,
    mut v_i_2555_: usize,
    mut v_b_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2557_: u8 = 0;
    let mut v_snd_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v_array_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v_a_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_unused_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2557_ = lean_usize_dec_lt(v_i_2555_, v_sz_2554_);
                if v___x_2557_ == 0 {
                    return v_b_2556_;
                } else {
                    v_snd_2558_ = crate::leanh::lean_ctor_get(v_b_2556_, 1);
                    v_fst_2559_ = crate::leanh::lean_ctor_get(v_b_2556_, 0);
                    v_isSharedCheck_2592_ = (!crate::leanh::lean_is_exclusive(v_b_2556_)) as u8;
                    if v_isSharedCheck_2592_ == 0 {
                        v___x_2561_ = v_b_2556_;
                        v_isShared_2562_ = v_isSharedCheck_2592_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2558_);
                        crate::leanh::lean_inc(v_fst_2559_);
                        crate::leanh::lean_dec(v_b_2556_);
                        v___x_2561_ = crate::leanh::lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_2563_ = crate::leanh::lean_ctor_get(v_snd_2558_, 0);
                v_start_2564_ = crate::leanh::lean_ctor_get(v_snd_2558_, 1);
                v_stop_2565_ = crate::leanh::lean_ctor_get(v_snd_2558_, 2);
                v___x_2566_ = lean_nat_dec_lt(v_start_2564_, v_stop_2565_);
                if v___x_2566_ == 0 {
                    if v_isShared_2562_ == 0 {
                        v___x_2568_ = v___x_2561_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2569_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_fst_2559_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_snd_2558_);
                        v___x_2568_ = v_reuseFailAlloc_2569_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_2565_);
                    crate::leanh::lean_inc(v_start_2564_);
                    crate::leanh::lean_inc_ref(v_array_2563_);
                    v_isSharedCheck_2588_ = (!crate::leanh::lean_is_exclusive(v_snd_2558_)) as u8;
                    if v_isSharedCheck_2588_ == 0 {
                        v_unused_2589_ = crate::leanh::lean_ctor_get(v_snd_2558_, 2);
                        crate::leanh::lean_dec(v_unused_2589_);
                        v_unused_2590_ = crate::leanh::lean_ctor_get(v_snd_2558_, 1);
                        crate::leanh::lean_dec(v_unused_2590_);
                        v_unused_2591_ = crate::leanh::lean_ctor_get(v_snd_2558_, 0);
                        crate::leanh::lean_dec(v_unused_2591_);
                        v___x_2571_ = v_snd_2558_;
                        v_isShared_2572_ = v_isSharedCheck_2588_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2558_);
                        v___x_2571_ = crate::leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2588_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2568_;
            }
            3 => {
                v_a_2573_ = lean_array_uget_borrowed(v_as_2553_, v_i_2555_);
                v___x_2574_ = lean_array_fget(v_array_2563_, v_start_2564_);
                v___x_2575_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2576_ = lean_nat_add(v_start_2564_, v___x_2575_);
                crate::leanh::lean_dec(v_start_2564_);
                if v_isShared_2572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2576_);
                    v___x_2578_ = v___x_2571_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2587_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_array_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___x_2576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_stop_2565_);
                    v___x_2578_ = v_reuseFailAlloc_2587_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2579_ = l_Lean_mkFVar(v___x_2574_);
                crate::leanh::lean_inc(v_a_2573_);
                v___x_2580_ = l_Lean_Meta_FVarSubst_insert(v_fst_2559_, v_a_2573_, v___x_2579_);
                if v_isShared_2562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2561_, 1, v___x_2578_);
                    crate::leanh::lean_ctor_set(v___x_2561_, 0, v___x_2580_);
                    v___x_2582_ = v___x_2561_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2578_);
                    v___x_2582_ = v_reuseFailAlloc_2586_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2583_ = 1usize;
                v___x_2584_ = lean_usize_add(v_i_2555_, v___x_2583_);
                v_i_2555_ = v___x_2584_;
                v_b_2556_ = v___x_2582_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(
    mut v_as_2593_: *mut crate::leanh::LeanObject,
    mut v_sz_2594_: *mut crate::leanh::LeanObject,
    mut v_i_2595_: *mut crate::leanh::LeanObject,
    mut v_b_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2597_: usize = 0;
    let mut v_i_boxed_2598_: usize = 0;
    let mut v_res_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2597_ = crate::leanh::lean_unbox_usize(v_sz_2594_);
    crate::leanh::lean_dec(v_sz_2594_);
    v_i_boxed_2598_ = crate::leanh::lean_unbox_usize(v_i_2595_);
    crate::leanh::lean_dec(v_i_2595_);
    v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_2593_, v_sz_boxed_2597_, v_i_boxed_2598_, v_b_2596_);
    crate::leanh::lean_dec_ref(v_as_2593_);
    return v_res_2599_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(
    mut v_sz_2600_: usize,
    mut v_i_2601_: usize,
    mut v_bs_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2605_: u8 = 0;
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xName_x3f_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hName_x3f_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2632_: u8 = 0;
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2605_ = lean_usize_dec_lt(v_i_2601_, v_sz_2600_);
                if v___x_2605_ == 0 {
                    v___x_2606_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2606_, 0, v_bs_2602_);
                    return v___x_2606_;
                } else {
                    v_v_2607_ = lean_array_uget(v_bs_2602_, v_i_2601_);
                    v_expr_2608_ = crate::leanh::lean_ctor_get(v_v_2607_, 0);
                    v_xName_x3f_2609_ = crate::leanh::lean_ctor_get(v_v_2607_, 1);
                    v_hName_x3f_2610_ = crate::leanh::lean_ctor_get(v_v_2607_, 2);
                    v_isSharedCheck_2633_ = (!crate::leanh::lean_is_exclusive(v_v_2607_)) as u8;
                    if v_isSharedCheck_2633_ == 0 {
                        v___x_2612_ = v_v_2607_;
                        v_isShared_2613_ = v_isSharedCheck_2633_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_hName_x3f_2610_);
                        crate::leanh::lean_inc(v_xName_x3f_2609_);
                        crate::leanh::lean_inc(v_expr_2608_);
                        crate::leanh::lean_dec(v_v_2607_);
                        v___x_2612_ = crate::leanh::lean_box(0);
                        v_isShared_2613_ = v_isSharedCheck_2633_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2614_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_2608_, v___y_2603_);
                if crate::leanh::lean_obj_tag(v___x_2614_) == 0 {
                    v_a_2615_ = crate::leanh::lean_ctor_get(v___x_2614_, 0);
                    crate::leanh::lean_inc(v_a_2615_);
                    crate::leanh::lean_dec_ref_known(v___x_2614_, 1);
                    v___x_2616_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2617_ = lean_array_uset(v_bs_2602_, v_i_2601_, v___x_2616_);
                    if v_isShared_2613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2612_, 0, v_a_2615_);
                        v___x_2619_ = v___x_2612_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_xName_x3f_2609_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_hName_x3f_2610_);
                        v___x_2619_ = v_reuseFailAlloc_2624_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2612_);
                    crate::leanh::lean_dec(v_hName_x3f_2610_);
                    crate::leanh::lean_dec(v_xName_x3f_2609_);
                    crate::leanh::lean_dec_ref(v_bs_2602_);
                    v_a_2625_ = crate::leanh::lean_ctor_get(v___x_2614_, 0);
                    v_isSharedCheck_2632_ = (!crate::leanh::lean_is_exclusive(v___x_2614_)) as u8;
                    if v_isSharedCheck_2632_ == 0 {
                        v___x_2627_ = v___x_2614_;
                        v_isShared_2628_ = v_isSharedCheck_2632_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2625_);
                        crate::leanh::lean_dec(v___x_2614_);
                        v___x_2627_ = crate::leanh::lean_box(0);
                        v_isShared_2628_ = v_isSharedCheck_2632_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2620_ = 1usize;
                v___x_2621_ = lean_usize_add(v_i_2601_, v___x_2620_);
                v___x_2622_ = lean_array_uset(v_bs_x27_2617_, v_i_2601_, v___x_2619_);
                v_i_2601_ = v___x_2621_;
                v_bs_2602_ = v___x_2622_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2628_ == 0 {
                    v___x_2630_ = v___x_2627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
                    v___x_2630_ = v_reuseFailAlloc_2631_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(
    mut v_sz_2634_: *mut crate::leanh::LeanObject,
    mut v_i_2635_: *mut crate::leanh::LeanObject,
    mut v_bs_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2639_: usize = 0;
    let mut v_i_boxed_2640_: usize = 0;
    let mut v_res_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2639_ = crate::leanh::lean_unbox_usize(v_sz_2634_);
    crate::leanh::lean_dec(v_sz_2634_);
    v_i_boxed_2640_ = crate::leanh::lean_unbox_usize(v_i_2635_);
    crate::leanh::lean_dec(v_i_2635_);
    v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_2639_, v_i_boxed_2640_, v_bs_2636_, v___y_2637_);
    crate::leanh::lean_dec(v___y_2637_);
    return v_res_2641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(
    mut v_transparency_2642_: u8,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_as_2644_: *mut crate::leanh::LeanObject,
    mut v_i_2645_: usize,
    mut v_stop_2646_: usize,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: u8 = 0;
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2656_: u8 = 0;
    let mut v_ctxApprox_2657_: u8 = 0;
    let mut v_quasiPatternApprox_2658_: u8 = 0;
    let mut v_constApprox_2659_: u8 = 0;
    let mut v_isDefEqStuckEx_2660_: u8 = 0;
    let mut v_unificationHints_2661_: u8 = 0;
    let mut v_proofIrrelevance_2662_: u8 = 0;
    let mut v_assignSyntheticOpaque_2663_: u8 = 0;
    let mut v_offsetCnstrs_2664_: u8 = 0;
    let mut v_etaStruct_2665_: u8 = 0;
    let mut v_univApprox_2666_: u8 = 0;
    let mut v_iota_2667_: u8 = 0;
    let mut v_beta_2668_: u8 = 0;
    let mut v_proj_2669_: u8 = 0;
    let mut v_zeta_2670_: u8 = 0;
    let mut v_zetaDelta_2671_: u8 = 0;
    let mut v_zetaUnused_2672_: u8 = 0;
    let mut v_zetaHave_2673_: u8 = 0;
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v_trackZetaDelta_2677_: u8 = 0;
    let mut v_zetaDeltaSet_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2684_: u8 = 0;
    let mut v_inTypeClassResolution_2685_: u8 = 0;
    let mut v_cacheInferType_2686_: u8 = 0;
    let mut v_config_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: u64 = 0;
    let mut v___x_2690_: u64 = 0;
    let mut v___x_2691_: u64 = 0;
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u64 = 0;
    let mut v___x_2694_: u64 = 0;
    let mut v_key_2695_: u64 = 0;
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___x_2703_: u8 = 0;
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v_a_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2719_: u8 = 0;
    let mut v_reuseFailAlloc_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_usize_dec_eq(v_i_2645_, v_stop_2646_);
                if v___x_2652_ == 0 {
                    v___x_2653_ = lean_array_uget_borrowed(v_as_2644_, v_i_2645_);
                    v_expr_2654_ = crate::leanh::lean_ctor_get(v___x_2653_, 0);
                    v___x_2655_ = l_Lean_Meta_Context_config(v___y_2647_);
                    v_foApprox_2656_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 0 as u32);
                    v_ctxApprox_2657_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 1 as u32);
                    v_quasiPatternApprox_2658_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2655_, 2 as u32);
                    v_constApprox_2659_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 3 as u32);
                    v_isDefEqStuckEx_2660_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2655_, 4 as u32);
                    v_unificationHints_2661_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2655_, 5 as u32);
                    v_proofIrrelevance_2662_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2655_, 6 as u32);
                    v_assignSyntheticOpaque_2663_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2655_, 7 as u32);
                    v_offsetCnstrs_2664_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 8 as u32);
                    v_etaStruct_2665_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 10 as u32);
                    v_univApprox_2666_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 11 as u32);
                    v_iota_2667_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 12 as u32);
                    v_beta_2668_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 13 as u32);
                    v_proj_2669_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 14 as u32);
                    v_zeta_2670_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 15 as u32);
                    v_zetaDelta_2671_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 16 as u32);
                    v_zetaUnused_2672_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 17 as u32);
                    v_zetaHave_2673_ = crate::leanh::lean_ctor_get_uint8(v___x_2655_, 18 as u32);
                    v_isSharedCheck_2721_ = (!crate::leanh::lean_is_exclusive(v___x_2655_)) as u8;
                    if v_isSharedCheck_2721_ == 0 {
                        v___x_2675_ = v___x_2655_;
                        v_isShared_2676_ = v_isSharedCheck_2721_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2655_);
                        v___x_2675_ = crate::leanh::lean_box(0);
                        v_isShared_2676_ = v_isSharedCheck_2721_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2643_);
                    v___x_2722_ = 0;
                    v___x_2723_ = crate::leanh::lean_box((v___x_2722_) as usize);
                    v___x_2724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2723_);
                    return v___x_2724_;
                }
            }
            1 => {
                v_trackZetaDelta_2677_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2647_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2678_ = crate::leanh::lean_ctor_get(v___y_2647_, 1);
                v_lctx_2679_ = crate::leanh::lean_ctor_get(v___y_2647_, 2);
                v_localInstances_2680_ = crate::leanh::lean_ctor_get(v___y_2647_, 3);
                v_defEqCtx_x3f_2681_ = crate::leanh::lean_ctor_get(v___y_2647_, 4);
                v_synthPendingDepth_2682_ = crate::leanh::lean_ctor_get(v___y_2647_, 5);
                v_canUnfold_x3f_2683_ = crate::leanh::lean_ctor_get(v___y_2647_, 6);
                v_univApprox_2684_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2647_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2685_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2647_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2686_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2647_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2676_ == 0 {
                    v_config_2688_ = v___x_2675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        0 as u32,
                        v_foApprox_2656_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        1 as u32,
                        v_ctxApprox_2657_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        2 as u32,
                        v_quasiPatternApprox_2658_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        3 as u32,
                        v_constApprox_2659_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        4 as u32,
                        v_isDefEqStuckEx_2660_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        5 as u32,
                        v_unificationHints_2661_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        6 as u32,
                        v_proofIrrelevance_2662_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        7 as u32,
                        v_assignSyntheticOpaque_2663_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        8 as u32,
                        v_offsetCnstrs_2664_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        10 as u32,
                        v_etaStruct_2665_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        11 as u32,
                        v_univApprox_2666_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        12 as u32,
                        v_iota_2667_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        13 as u32,
                        v_beta_2668_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        14 as u32,
                        v_proj_2669_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        15 as u32,
                        v_zeta_2670_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        16 as u32,
                        v_zetaDelta_2671_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        17 as u32,
                        v_zetaUnused_2672_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2720_,
                        18 as u32,
                        v_zetaHave_2673_,
                    );
                    v_config_2688_ = v_reuseFailAlloc_2720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2688_, 9 as u32, v_transparency_2642_);
                v___x_2689_ = l_Lean_Meta_Context_configKey(v___y_2647_);
                v___x_2690_ = 3u64;
                v___x_2691_ = lean_uint64_shift_right(v___x_2689_, v___x_2690_);
                v___x_2692_ = crate::leanh::lean_box(0);
                v___x_2693_ = lean_uint64_shift_left(v___x_2691_, v___x_2690_);
                v___x_2694_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_2642_);
                v_key_2695_ = lean_uint64_lor(v___x_2693_, v___x_2694_);
                v___x_2696_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2696_, 0, v_config_2688_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2696_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2695_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2683_);
                crate::leanh::lean_inc(v_synthPendingDepth_2682_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2681_);
                crate::leanh::lean_inc_ref(v_localInstances_2680_);
                crate::leanh::lean_inc_ref(v_lctx_2679_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2678_);
                v___x_2697_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2697_, 0, v___x_2696_);
                crate::leanh::lean_ctor_set(v___x_2697_, 1, v_zetaDeltaSet_2678_);
                crate::leanh::lean_ctor_set(v___x_2697_, 2, v_lctx_2679_);
                crate::leanh::lean_ctor_set(v___x_2697_, 3, v_localInstances_2680_);
                crate::leanh::lean_ctor_set(v___x_2697_, 4, v_defEqCtx_x3f_2681_);
                crate::leanh::lean_ctor_set(v___x_2697_, 5, v_synthPendingDepth_2682_);
                crate::leanh::lean_ctor_set(v___x_2697_, 6, v_canUnfold_x3f_2683_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2677_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2684_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2685_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2686_,
                );
                crate::leanh::lean_inc_ref(v_expr_2654_);
                crate::leanh::lean_inc_ref(v_a_2643_);
                v___x_2698_ = l_Lean_Meta_kabstract(
                    v_a_2643_,
                    v_expr_2654_,
                    v___x_2692_,
                    v___x_2697_,
                    v___y_2648_,
                    v___y_2649_,
                    v___y_2650_,
                );
                crate::leanh::lean_dec_ref_known(v___x_2697_, 7);
                if crate::leanh::lean_obj_tag(v___x_2698_) == 0 {
                    v_a_2699_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
                    v_isSharedCheck_2711_ = (!crate::leanh::lean_is_exclusive(v___x_2698_)) as u8;
                    if v_isSharedCheck_2711_ == 0 {
                        v___x_2701_ = v___x_2698_;
                        v_isShared_2702_ = v_isSharedCheck_2711_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2699_);
                        crate::leanh::lean_dec(v___x_2698_);
                        v___x_2701_ = crate::leanh::lean_box(0);
                        v_isShared_2702_ = v_isSharedCheck_2711_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2643_);
                    v_a_2712_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
                    v_isSharedCheck_2719_ = (!crate::leanh::lean_is_exclusive(v___x_2698_)) as u8;
                    if v_isSharedCheck_2719_ == 0 {
                        v___x_2714_ = v___x_2698_;
                        v_isShared_2715_ = v_isSharedCheck_2719_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2712_);
                        crate::leanh::lean_dec(v___x_2698_);
                        v___x_2714_ = crate::leanh::lean_box(0);
                        v_isShared_2715_ = v_isSharedCheck_2719_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2703_ = l_Lean_Expr_hasLooseBVars(v_a_2699_);
                crate::leanh::lean_dec(v_a_2699_);
                if v___x_2703_ == 0 {
                    crate::leanh::lean_del_object(v___x_2701_);
                    v___x_2704_ = 1usize;
                    v___x_2705_ = lean_usize_add(v_i_2645_, v___x_2704_);
                    v_i_2645_ = v___x_2705_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_2643_);
                    v___x_2707_ = crate::leanh::lean_box((v___x_2703_) as usize);
                    if v_isShared_2702_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2701_, 0, v___x_2707_);
                        v___x_2709_ = v___x_2701_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                        v___x_2709_ = v_reuseFailAlloc_2710_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2709_;
            }
            5 => {
                if v_isShared_2715_ == 0 {
                    v___x_2717_ = v___x_2714_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
                    v___x_2717_ = v_reuseFailAlloc_2718_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(
    mut v_transparency_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_as_2727_: *mut crate::leanh::LeanObject,
    mut v_i_2728_: *mut crate::leanh::LeanObject,
    mut v_stop_2729_: *mut crate::leanh::LeanObject,
    mut v___y_2730_: *mut crate::leanh::LeanObject,
    mut v___y_2731_: *mut crate::leanh::LeanObject,
    mut v___y_2732_: *mut crate::leanh::LeanObject,
    mut v___y_2733_: *mut crate::leanh::LeanObject,
    mut v___y_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_2735_: u8 = 0;
    let mut v_i_boxed_2736_: usize = 0;
    let mut v_stop_boxed_2737_: usize = 0;
    let mut v_res_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_2735_ = (crate::leanh::lean_unbox(v_transparency_2725_) as u8);
    v_i_boxed_2736_ = crate::leanh::lean_unbox_usize(v_i_2728_);
    crate::leanh::lean_dec(v_i_2728_);
    v_stop_boxed_2737_ = crate::leanh::lean_unbox_usize(v_stop_2729_);
    crate::leanh::lean_dec(v_stop_2729_);
    v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_2735_, v_a_2726_, v_as_2727_, v_i_boxed_2736_, v_stop_boxed_2737_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
    crate::leanh::lean_dec(v___y_2733_);
    crate::leanh::lean_dec_ref(v___y_2732_);
    crate::leanh::lean_dec(v___y_2731_);
    crate::leanh::lean_dec_ref(v___y_2730_);
    crate::leanh::lean_dec_ref(v_as_2727_);
    return v_res_2738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v___x_2740_: *mut crate::leanh::LeanObject,
    mut v_transparency_2741_: u8,
    mut v_as_2742_: *mut crate::leanh::LeanObject,
    mut v_i_2743_: usize,
    mut v_stop_2744_: usize,
    mut v_b_2745_: *mut crate::leanh::LeanObject,
    mut v___y_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: usize = 0;
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2759_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: usize = 0;
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: u8 = 0;
    let mut v_a_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_a_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut v_a_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2756_ = lean_usize_dec_eq(v_i_2743_, v_stop_2744_);
                if v___x_2756_ == 0 {
                    v___x_2757_ = lean_array_uget_borrowed(v_as_2742_, v_i_2743_);
                    crate::leanh::lean_inc(v___x_2757_);
                    v___x_2761_ = l_Lean_FVarId_getType___redArg(
                        v___x_2757_,
                        v___y_2746_,
                        v___y_2748_,
                        v___y_2749_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2761_) == 0 {
                        v_a_2762_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                        crate::leanh::lean_inc(v_a_2762_);
                        crate::leanh::lean_dec_ref_known(v___x_2761_, 1);
                        v___x_2763_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_2762_, v___y_2747_);
                        if crate::leanh::lean_obj_tag(v___x_2763_) == 0 {
                            v_a_2764_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                            crate::leanh::lean_inc(v_a_2764_);
                            crate::leanh::lean_dec_ref_known(v___x_2763_, 1);
                            v___x_2765_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2766_ = lean_nat_dec_eq(v___x_2740_, v___x_2765_);
                            v___x_2767_ = lean_array_get_size(v_a_2739_);
                            v___x_2768_ = lean_nat_dec_lt(v___x_2765_, v___x_2767_);
                            if v___x_2768_ == 0 {
                                crate::leanh::lean_dec(v_a_2764_);
                                v_a_2759_ = v___x_2766_;
                                state = 2;
                                continue;
                            } else {
                                if v___x_2768_ == 0 {
                                    crate::leanh::lean_dec(v_a_2764_);
                                    v_a_2759_ = v___x_2766_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2769_ = 0usize;
                                    v___x_2770_ = lean_usize_of_nat(v___x_2767_);
                                    v___x_2771_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_2741_, v_a_2764_, v_a_2739_, v___x_2769_, v___x_2770_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
                                    if crate::leanh::lean_obj_tag(v___x_2771_) == 0 {
                                        v_a_2772_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                                        crate::leanh::lean_inc(v_a_2772_);
                                        crate::leanh::lean_dec_ref_known(v___x_2771_, 1);
                                        v___x_2773_ = (crate::leanh::lean_unbox(v_a_2772_) as u8);
                                        crate::leanh::lean_dec(v_a_2772_);
                                        v_a_2759_ = v___x_2773_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_2745_);
                                        v_a_2774_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                                        v_isSharedCheck_2781_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2771_)) as u8;
                                        if v_isSharedCheck_2781_ == 0 {
                                            v___x_2776_ = v___x_2771_;
                                            v_isShared_2777_ = v_isSharedCheck_2781_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2774_);
                                            crate::leanh::lean_dec(v___x_2771_);
                                            v___x_2776_ = crate::leanh::lean_box(0);
                                            v_isShared_2777_ = v_isSharedCheck_2781_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2745_);
                            v_a_2782_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                            v_isSharedCheck_2789_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2763_)) as u8;
                            if v_isSharedCheck_2789_ == 0 {
                                v___x_2784_ = v___x_2763_;
                                v_isShared_2785_ = v_isSharedCheck_2789_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2782_);
                                crate::leanh::lean_dec(v___x_2763_);
                                v___x_2784_ = crate::leanh::lean_box(0);
                                v_isShared_2785_ = v_isSharedCheck_2789_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2745_);
                        v_a_2790_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                        v_isSharedCheck_2797_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2761_)) as u8;
                        if v_isSharedCheck_2797_ == 0 {
                            v___x_2792_ = v___x_2761_;
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2790_);
                            crate::leanh::lean_dec(v___x_2761_);
                            v___x_2792_ = crate::leanh::lean_box(0);
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_2798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2798_, 0, v_b_2745_);
                    return v___x_2798_;
                }
            }
            1 => {
                v___x_2753_ = 1usize;
                v___x_2754_ = lean_usize_add(v_i_2743_, v___x_2753_);
                v_i_2743_ = v___x_2754_;
                v_b_2745_ = v_a_2752_;
                state = 0;
                continue;
            }
            2 => {
                if v_a_2759_ == 0 {
                    v_a_2752_ = v_b_2745_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___x_2757_);
                    v___x_2760_ = lean_array_push(v_b_2745_, v___x_2757_);
                    v_a_2752_ = v___x_2760_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2777_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
                    v___x_2779_ = v_reuseFailAlloc_2780_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2779_;
            }
            5 => {
                if v_isShared_2785_ == 0 {
                    v___x_2787_ = v___x_2784_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2788_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
                    v___x_2787_ = v_reuseFailAlloc_2788_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2787_;
            }
            7 => {
                if v_isShared_2793_ == 0 {
                    v___x_2795_ = v___x_2792_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
                    v___x_2795_ = v_reuseFailAlloc_2796_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v___x_2800_: *mut crate::leanh::LeanObject,
    mut v_transparency_2801_: *mut crate::leanh::LeanObject,
    mut v_as_2802_: *mut crate::leanh::LeanObject,
    mut v_i_2803_: *mut crate::leanh::LeanObject,
    mut v_stop_2804_: *mut crate::leanh::LeanObject,
    mut v_b_2805_: *mut crate::leanh::LeanObject,
    mut v___y_2806_: *mut crate::leanh::LeanObject,
    mut v___y_2807_: *mut crate::leanh::LeanObject,
    mut v___y_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_2811_: u8 = 0;
    let mut v_i_boxed_2812_: usize = 0;
    let mut v_stop_boxed_2813_: usize = 0;
    let mut v_res_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_2811_ = (crate::leanh::lean_unbox(v_transparency_2801_) as u8);
    v_i_boxed_2812_ = crate::leanh::lean_unbox_usize(v_i_2803_);
    crate::leanh::lean_dec(v_i_2803_);
    v_stop_boxed_2813_ = crate::leanh::lean_unbox_usize(v_stop_2804_);
    crate::leanh::lean_dec(v_stop_2804_);
    v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_2799_, v___x_2800_, v_transparency_boxed_2811_, v_as_2802_, v_i_boxed_2812_, v_stop_boxed_2813_, v_b_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
    crate::leanh::lean_dec(v___y_2809_);
    crate::leanh::lean_dec_ref(v___y_2808_);
    crate::leanh::lean_dec(v___y_2807_);
    crate::leanh::lean_dec_ref(v___y_2806_);
    crate::leanh::lean_dec_ref(v_as_2802_);
    crate::leanh::lean_dec(v___x_2800_);
    crate::leanh::lean_dec_ref(v_a_2799_);
    return v_res_2814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(
    mut v_transparency_2815_: u8,
    mut v_a_2816_: *mut crate::leanh::LeanObject,
    mut v___x_2817_: *mut crate::leanh::LeanObject,
    mut v_as_2818_: *mut crate::leanh::LeanObject,
    mut v_i_2819_: usize,
    mut v_stop_2820_: usize,
    mut v_b_2821_: *mut crate::leanh::LeanObject,
    mut v___y_2822_: *mut crate::leanh::LeanObject,
    mut v___y_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: usize = 0;
    let mut v___x_2830_: usize = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: usize = 0;
    let mut v___x_2846_: usize = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    let mut v_a_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_a_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v_a_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2832_ = lean_usize_dec_eq(v_i_2819_, v_stop_2820_);
                if v___x_2832_ == 0 {
                    v___x_2833_ = lean_array_uget_borrowed(v_as_2818_, v_i_2819_);
                    crate::leanh::lean_inc(v___x_2833_);
                    v___x_2837_ = l_Lean_FVarId_getType___redArg(
                        v___x_2833_,
                        v___y_2822_,
                        v___y_2824_,
                        v___y_2825_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2837_) == 0 {
                        v_a_2838_ = crate::leanh::lean_ctor_get(v___x_2837_, 0);
                        crate::leanh::lean_inc(v_a_2838_);
                        crate::leanh::lean_dec_ref_known(v___x_2837_, 1);
                        v___x_2839_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_2838_, v___y_2823_);
                        if crate::leanh::lean_obj_tag(v___x_2839_) == 0 {
                            v_a_2840_ = crate::leanh::lean_ctor_get(v___x_2839_, 0);
                            crate::leanh::lean_inc(v_a_2840_);
                            crate::leanh::lean_dec_ref_known(v___x_2839_, 1);
                            v___x_2841_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2842_ = lean_nat_dec_eq(v___x_2817_, v___x_2841_);
                            v___x_2843_ = lean_array_get_size(v_a_2816_);
                            v___x_2844_ = lean_nat_dec_lt(v___x_2841_, v___x_2843_);
                            if v___x_2844_ == 0 {
                                crate::leanh::lean_dec(v_a_2840_);
                                v_a_2835_ = v___x_2842_;
                                state = 2;
                                continue;
                            } else {
                                if v___x_2844_ == 0 {
                                    crate::leanh::lean_dec(v_a_2840_);
                                    v_a_2835_ = v___x_2842_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2845_ = 0usize;
                                    v___x_2846_ = lean_usize_of_nat(v___x_2843_);
                                    v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_2815_, v_a_2840_, v_a_2816_, v___x_2845_, v___x_2846_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
                                    if crate::leanh::lean_obj_tag(v___x_2847_) == 0 {
                                        v_a_2848_ = crate::leanh::lean_ctor_get(v___x_2847_, 0);
                                        crate::leanh::lean_inc(v_a_2848_);
                                        crate::leanh::lean_dec_ref_known(v___x_2847_, 1);
                                        v___x_2849_ = (crate::leanh::lean_unbox(v_a_2848_) as u8);
                                        crate::leanh::lean_dec(v_a_2848_);
                                        v_a_2835_ = v___x_2849_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_2821_);
                                        v_a_2850_ = crate::leanh::lean_ctor_get(v___x_2847_, 0);
                                        v_isSharedCheck_2857_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2847_)) as u8;
                                        if v_isSharedCheck_2857_ == 0 {
                                            v___x_2852_ = v___x_2847_;
                                            v_isShared_2853_ = v_isSharedCheck_2857_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2850_);
                                            crate::leanh::lean_dec(v___x_2847_);
                                            v___x_2852_ = crate::leanh::lean_box(0);
                                            v_isShared_2853_ = v_isSharedCheck_2857_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2821_);
                            v_a_2858_ = crate::leanh::lean_ctor_get(v___x_2839_, 0);
                            v_isSharedCheck_2865_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2839_)) as u8;
                            if v_isSharedCheck_2865_ == 0 {
                                v___x_2860_ = v___x_2839_;
                                v_isShared_2861_ = v_isSharedCheck_2865_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2858_);
                                crate::leanh::lean_dec(v___x_2839_);
                                v___x_2860_ = crate::leanh::lean_box(0);
                                v_isShared_2861_ = v_isSharedCheck_2865_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2821_);
                        v_a_2866_ = crate::leanh::lean_ctor_get(v___x_2837_, 0);
                        v_isSharedCheck_2873_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2837_)) as u8;
                        if v_isSharedCheck_2873_ == 0 {
                            v___x_2868_ = v___x_2837_;
                            v_isShared_2869_ = v_isSharedCheck_2873_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2866_);
                            crate::leanh::lean_dec(v___x_2837_);
                            v___x_2868_ = crate::leanh::lean_box(0);
                            v_isShared_2869_ = v_isSharedCheck_2873_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_2874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2874_, 0, v_b_2821_);
                    return v___x_2874_;
                }
            }
            1 => {
                v___x_2829_ = 1usize;
                v___x_2830_ = lean_usize_add(v_i_2819_, v___x_2829_);
                v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_2816_, v___x_2817_, v_transparency_2815_, v_as_2818_, v___x_2830_, v_stop_2820_, v_a_2828_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
                return v___x_2831_;
            }
            2 => {
                if v_a_2835_ == 0 {
                    v_a_2828_ = v_b_2821_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___x_2833_);
                    v___x_2836_ = lean_array_push(v_b_2821_, v___x_2833_);
                    v_a_2828_ = v___x_2836_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2853_ == 0 {
                    v___x_2855_ = v___x_2852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2855_;
            }
            5 => {
                if v_isShared_2861_ == 0 {
                    v___x_2863_ = v___x_2860_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2863_;
            }
            7 => {
                if v_isShared_2869_ == 0 {
                    v___x_2871_ = v___x_2868_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
                    v___x_2871_ = v_reuseFailAlloc_2872_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(
    mut v_transparency_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v___x_2877_: *mut crate::leanh::LeanObject,
    mut v_as_2878_: *mut crate::leanh::LeanObject,
    mut v_i_2879_: *mut crate::leanh::LeanObject,
    mut v_stop_2880_: *mut crate::leanh::LeanObject,
    mut v_b_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_2887_: u8 = 0;
    let mut v_i_boxed_2888_: usize = 0;
    let mut v_stop_boxed_2889_: usize = 0;
    let mut v_res_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_2887_ = (crate::leanh::lean_unbox(v_transparency_2875_) as u8);
    v_i_boxed_2888_ = crate::leanh::lean_unbox_usize(v_i_2879_);
    crate::leanh::lean_dec(v_i_2879_);
    v_stop_boxed_2889_ = crate::leanh::lean_unbox_usize(v_stop_2880_);
    crate::leanh::lean_dec(v_stop_2880_);
    v_res_2890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_2887_, v_a_2876_, v___x_2877_, v_as_2878_, v_i_boxed_2888_, v_stop_boxed_2889_, v_b_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
    crate::leanh::lean_dec(v___y_2885_);
    crate::leanh::lean_dec_ref(v___y_2884_);
    crate::leanh::lean_dec(v___y_2883_);
    crate::leanh::lean_dec_ref(v___y_2882_);
    crate::leanh::lean_dec_ref(v_as_2878_);
    crate::leanh::lean_dec(v___x_2877_);
    crate::leanh::lean_dec_ref(v_a_2876_);
    return v_res_2890_;
}
pub unsafe fn l_Lean_MVarId_generalizeHyp(
    mut v_mvarId_2893_: *mut crate::leanh::LeanObject,
    mut v_args_2894_: *mut crate::leanh::LeanObject,
    mut v_hyps_2895_: *mut crate::leanh::LeanObject,
    mut v_fvarSubst_2896_: *mut crate::leanh::LeanObject,
    mut v_transparency_2897_: u8,
    mut v_a_2898_: *mut crate::leanh::LeanObject,
    mut v_a_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    let mut v_sz_2906_: usize = 0;
    let mut v___x_2907_: usize = 0;
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: u8 = 0;
    let mut v_a_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v_fst_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2940_: usize = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_unused_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_a_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_a_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_a_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v___y_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: usize = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: usize = 0;
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_a_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2903_ = lean_array_get_size(v_hyps_2895_);
                v___x_2904_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2905_ = lean_nat_dec_eq(v___x_2903_, v___x_2904_);
                if v___x_2905_ == 0 {
                    v_sz_2906_ = lean_array_size(v_args_2894_);
                    v___x_2907_ = 0usize;
                    v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_2906_, v___x_2907_, v_args_2894_, v_a_2899_);
                    if crate::leanh::lean_obj_tag(v___x_2908_) == 0 {
                        v_a_2909_ = crate::leanh::lean_ctor_get(v___x_2908_, 0);
                        crate::leanh::lean_inc(v_a_2909_);
                        crate::leanh::lean_dec_ref_known(v___x_2908_, 1);
                        v___x_2910_ = 1;
                        v___x_2996_ = l_Lean_MVarId_generalizeHyp___closed__0;
                        v___x_2997_ = lean_nat_dec_lt(v___x_2904_, v___x_2903_);
                        if v___x_2997_ == 0 {
                            v_a_2912_ = v___x_2996_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2998_ = lean_nat_dec_le(v___x_2903_, v___x_2903_);
                            if v___x_2998_ == 0 {
                                if v___x_2997_ == 0 {
                                    v_a_2912_ = v___x_2996_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2999_ = lean_usize_of_nat(v___x_2903_);
                                    v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_2897_, v_a_2909_, v___x_2903_, v_hyps_2895_, v___x_2907_, v___x_2999_, v___x_2996_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
                                    v___y_2986_ = v___x_3000_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                v___x_3001_ = lean_usize_of_nat(v___x_2903_);
                                v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_2897_, v_a_2909_, v___x_2903_, v_hyps_2895_, v___x_2907_, v___x_3001_, v___x_2996_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
                                v___y_2986_ = v___x_3002_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarSubst_2896_);
                        crate::leanh::lean_dec(v_mvarId_2893_);
                        v_a_3003_ = crate::leanh::lean_ctor_get(v___x_2908_, 0);
                        v_isSharedCheck_3010_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2908_)) as u8;
                        if v_isSharedCheck_3010_ == 0 {
                            v___x_3005_ = v___x_2908_;
                            v_isShared_3006_ = v_isSharedCheck_3010_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3003_);
                            crate::leanh::lean_dec(v___x_2908_);
                            v___x_3005_ = crate::leanh::lean_box(0);
                            v_isShared_3006_ = v_isSharedCheck_3010_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    v___x_3011_ =
                        l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(
                            v_mvarId_2893_,
                            v_args_2894_,
                            v_transparency_2897_,
                            v_a_2898_,
                            v_a_2899_,
                            v_a_2900_,
                            v_a_2901_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3011_) == 0 {
                        v_a_3012_ = crate::leanh::lean_ctor_get(v___x_3011_, 0);
                        v_isSharedCheck_3020_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3011_)) as u8;
                        if v_isSharedCheck_3020_ == 0 {
                            v___x_3014_ = v___x_3011_;
                            v_isShared_3015_ = v_isSharedCheck_3020_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3012_);
                            crate::leanh::lean_dec(v___x_3011_);
                            v___x_3014_ = crate::leanh::lean_box(0);
                            v_isShared_3015_ = v_isSharedCheck_3020_;
                            state = 21;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarSubst_2896_);
                        v_a_3021_ = crate::leanh::lean_ctor_get(v___x_3011_, 0);
                        v_isSharedCheck_3028_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3011_)) as u8;
                        if v_isSharedCheck_3028_ == 0 {
                            v___x_3023_ = v___x_3011_;
                            v_isShared_3024_ = v_isSharedCheck_3028_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3021_);
                            crate::leanh::lean_dec(v___x_3011_);
                            v___x_3023_ = crate::leanh::lean_box(0);
                            v_isShared_3024_ = v_isSharedCheck_3028_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2913_ = l_Lean_MVarId_revert(
                    v_mvarId_2893_,
                    v_a_2912_,
                    v___x_2910_,
                    v___x_2905_,
                    v_a_2898_,
                    v_a_2899_,
                    v_a_2900_,
                    v_a_2901_,
                );
                if crate::leanh::lean_obj_tag(v___x_2913_) == 0 {
                    v_a_2914_ = crate::leanh::lean_ctor_get(v___x_2913_, 0);
                    crate::leanh::lean_inc(v_a_2914_);
                    crate::leanh::lean_dec_ref_known(v___x_2913_, 1);
                    v_fst_2915_ = crate::leanh::lean_ctor_get(v_a_2914_, 0);
                    crate::leanh::lean_inc(v_fst_2915_);
                    v_snd_2916_ = crate::leanh::lean_ctor_get(v_a_2914_, 1);
                    crate::leanh::lean_inc(v_snd_2916_);
                    crate::leanh::lean_dec(v_a_2914_);
                    v___x_2917_ =
                        l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(
                            v_snd_2916_,
                            v_a_2909_,
                            v_transparency_2897_,
                            v_a_2898_,
                            v_a_2899_,
                            v_a_2900_,
                            v_a_2901_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2917_) == 0 {
                        v_a_2918_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                        crate::leanh::lean_inc(v_a_2918_);
                        crate::leanh::lean_dec_ref_known(v___x_2917_, 1);
                        v_fst_2919_ = crate::leanh::lean_ctor_get(v_a_2918_, 0);
                        v_snd_2920_ = crate::leanh::lean_ctor_get(v_a_2918_, 1);
                        v_isSharedCheck_2968_ = (!crate::leanh::lean_is_exclusive(v_a_2918_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v___x_2922_ = v_a_2918_;
                            v_isShared_2923_ = v_isSharedCheck_2968_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2920_);
                            crate::leanh::lean_inc(v_fst_2919_);
                            crate::leanh::lean_dec(v_a_2918_);
                            v___x_2922_ = crate::leanh::lean_box(0);
                            v_isShared_2923_ = v_isSharedCheck_2968_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_2915_);
                        crate::leanh::lean_dec(v_fvarSubst_2896_);
                        v_a_2969_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                        v_isSharedCheck_2976_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2917_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2971_ = v___x_2917_;
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2969_);
                            crate::leanh::lean_dec(v___x_2917_);
                            v___x_2971_ = crate::leanh::lean_box(0);
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2909_);
                    crate::leanh::lean_dec(v_fvarSubst_2896_);
                    v_a_2977_ = crate::leanh::lean_ctor_get(v___x_2913_, 0);
                    v_isSharedCheck_2984_ = (!crate::leanh::lean_is_exclusive(v___x_2913_)) as u8;
                    if v_isSharedCheck_2984_ == 0 {
                        v___x_2979_ = v___x_2913_;
                        v_isShared_2980_ = v_isSharedCheck_2984_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2977_);
                        crate::leanh::lean_dec(v___x_2913_);
                        v___x_2979_ = crate::leanh::lean_box(0);
                        v_isShared_2980_ = v_isSharedCheck_2984_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2924_ = lean_array_get_size(v_fst_2915_);
                v___x_2925_ = crate::leanh::lean_box(0);
                v___x_2926_ = l_Lean_Meta_introNCore(
                    v_snd_2920_,
                    v___x_2924_,
                    v___x_2925_,
                    v___x_2905_,
                    v___x_2910_,
                    v_a_2898_,
                    v_a_2899_,
                    v_a_2900_,
                    v_a_2901_,
                );
                if crate::leanh::lean_obj_tag(v___x_2926_) == 0 {
                    v_a_2927_ = crate::leanh::lean_ctor_get(v___x_2926_, 0);
                    v_isSharedCheck_2959_ = (!crate::leanh::lean_is_exclusive(v___x_2926_)) as u8;
                    if v_isSharedCheck_2959_ == 0 {
                        v___x_2929_ = v___x_2926_;
                        v_isShared_2930_ = v_isSharedCheck_2959_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2927_);
                        crate::leanh::lean_dec(v___x_2926_);
                        v___x_2929_ = crate::leanh::lean_box(0);
                        v_isShared_2930_ = v_isSharedCheck_2959_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2922_);
                    crate::leanh::lean_dec(v_fst_2919_);
                    crate::leanh::lean_dec(v_fst_2915_);
                    crate::leanh::lean_dec(v_fvarSubst_2896_);
                    v_a_2960_ = crate::leanh::lean_ctor_get(v___x_2926_, 0);
                    v_isSharedCheck_2967_ = (!crate::leanh::lean_is_exclusive(v___x_2926_)) as u8;
                    if v_isSharedCheck_2967_ == 0 {
                        v___x_2962_ = v___x_2926_;
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2960_);
                        crate::leanh::lean_dec(v___x_2926_);
                        v___x_2962_ = crate::leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_2931_ = crate::leanh::lean_ctor_get(v_a_2927_, 0);
                v_snd_2932_ = crate::leanh::lean_ctor_get(v_a_2927_, 1);
                v_isSharedCheck_2958_ = (!crate::leanh::lean_is_exclusive(v_a_2927_)) as u8;
                if v_isSharedCheck_2958_ == 0 {
                    v___x_2934_ = v_a_2927_;
                    v_isShared_2935_ = v_isSharedCheck_2958_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2932_);
                    crate::leanh::lean_inc(v_fst_2931_);
                    crate::leanh::lean_dec(v_a_2927_);
                    v___x_2934_ = crate::leanh::lean_box(0);
                    v_isShared_2935_ = v_isSharedCheck_2958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2936_ = lean_array_get_size(v_fst_2931_);
                v___x_2937_ = l_Array_toSubarray___redArg(v_fst_2931_, v___x_2904_, v___x_2936_);
                if v_isShared_2935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2934_, 1, v___x_2937_);
                    crate::leanh::lean_ctor_set(v___x_2934_, 0, v_fvarSubst_2896_);
                    v___x_2939_ = v___x_2934_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_fvarSubst_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2937_);
                    v___x_2939_ = v_reuseFailAlloc_2957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_sz_2940_ = lean_array_size(v_fst_2915_);
                v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_2915_, v_sz_2940_, v___x_2907_, v___x_2939_);
                crate::leanh::lean_dec(v_fst_2915_);
                v_fst_2942_ = crate::leanh::lean_ctor_get(v___x_2941_, 0);
                v_isSharedCheck_2955_ = (!crate::leanh::lean_is_exclusive(v___x_2941_)) as u8;
                if v_isSharedCheck_2955_ == 0 {
                    v_unused_2956_ = crate::leanh::lean_ctor_get(v___x_2941_, 1);
                    crate::leanh::lean_dec(v_unused_2956_);
                    v___x_2944_ = v___x_2941_;
                    v_isShared_2945_ = v_isSharedCheck_2955_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2942_);
                    crate::leanh::lean_dec(v___x_2941_);
                    v___x_2944_ = crate::leanh::lean_box(0);
                    v_isShared_2945_ = v_isSharedCheck_2955_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2944_, 1, v_snd_2932_);
                    crate::leanh::lean_ctor_set(v___x_2944_, 0, v_fst_2919_);
                    v___x_2947_ = v___x_2944_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_fst_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_snd_2932_);
                    v___x_2947_ = v_reuseFailAlloc_2954_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2922_, 1, v___x_2947_);
                    crate::leanh::lean_ctor_set(v___x_2922_, 0, v_fst_2942_);
                    v___x_2949_ = v___x_2922_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_fst_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___x_2947_);
                    v___x_2949_ = v_reuseFailAlloc_2953_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2930_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2929_, 0, v___x_2949_);
                    v___x_2951_ = v___x_2929_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2949_);
                    v___x_2951_ = v_reuseFailAlloc_2952_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2951_;
            }
            10 => {
                if v_isShared_2963_ == 0 {
                    v___x_2965_ = v___x_2962_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2965_;
            }
            12 => {
                if v_isShared_2972_ == 0 {
                    v___x_2974_ = v___x_2971_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2974_;
            }
            14 => {
                if v_isShared_2980_ == 0 {
                    v___x_2982_ = v___x_2979_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2982_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_2986_) == 0 {
                    v_a_2987_ = crate::leanh::lean_ctor_get(v___y_2986_, 0);
                    crate::leanh::lean_inc(v_a_2987_);
                    crate::leanh::lean_dec_ref_known(v___y_2986_, 1);
                    v_a_2912_ = v_a_2987_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2909_);
                    crate::leanh::lean_dec(v_fvarSubst_2896_);
                    crate::leanh::lean_dec(v_mvarId_2893_);
                    v_a_2988_ = crate::leanh::lean_ctor_get(v___y_2986_, 0);
                    v_isSharedCheck_2995_ = (!crate::leanh::lean_is_exclusive(v___y_2986_)) as u8;
                    if v_isSharedCheck_2995_ == 0 {
                        v___x_2990_ = v___y_2986_;
                        v_isShared_2991_ = v_isSharedCheck_2995_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2988_);
                        crate::leanh::lean_dec(v___y_2986_);
                        v___x_2990_ = crate::leanh::lean_box(0);
                        v_isShared_2991_ = v_isSharedCheck_2995_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_2991_ == 0 {
                    v___x_2993_ = v___x_2990_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
                    v___x_2993_ = v_reuseFailAlloc_2994_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2993_;
            }
            19 => {
                if v_isShared_3006_ == 0 {
                    v___x_3008_ = v___x_3005_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
                    v___x_3008_ = v_reuseFailAlloc_3009_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3008_;
            }
            21 => {
                v___x_3016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3016_, 0, v_fvarSubst_2896_);
                crate::leanh::lean_ctor_set(v___x_3016_, 1, v_a_3012_);
                if v_isShared_3015_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3014_, 0, v___x_3016_);
                    v___x_3018_ = v___x_3014_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
                    v___x_3018_ = v_reuseFailAlloc_3019_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3018_;
            }
            23 => {
                if v_isShared_3024_ == 0 {
                    v___x_3026_ = v___x_3023_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_generalizeHyp___boxed(
    mut v_mvarId_3029_: *mut crate::leanh::LeanObject,
    mut v_args_3030_: *mut crate::leanh::LeanObject,
    mut v_hyps_3031_: *mut crate::leanh::LeanObject,
    mut v_fvarSubst_3032_: *mut crate::leanh::LeanObject,
    mut v_transparency_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_a_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_3039_: u8 = 0;
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_3039_ = (crate::leanh::lean_unbox(v_transparency_3033_) as u8);
    v_res_3040_ = l_Lean_MVarId_generalizeHyp(
        v_mvarId_3029_,
        v_args_3030_,
        v_hyps_3031_,
        v_fvarSubst_3032_,
        v_transparency_boxed_3039_,
        v_a_3034_,
        v_a_3035_,
        v_a_3036_,
        v_a_3037_,
    );
    crate::leanh::lean_dec(v_a_3037_);
    crate::leanh::lean_dec_ref(v_a_3036_);
    crate::leanh::lean_dec(v_a_3035_);
    crate::leanh::lean_dec_ref(v_a_3034_);
    crate::leanh::lean_dec_ref(v_hyps_3031_);
    return v_res_3040_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(
    mut v_sz_3041_: usize,
    mut v_i_3042_: usize,
    mut v_bs_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_3041_, v_i_3042_, v_bs_3043_, v___y_3045_);
    return v___x_3049_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(
    mut v_sz_3050_: *mut crate::leanh::LeanObject,
    mut v_i_3051_: *mut crate::leanh::LeanObject,
    mut v_bs_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
    mut v___y_3055_: *mut crate::leanh::LeanObject,
    mut v___y_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3058_: usize = 0;
    let mut v_i_boxed_3059_: usize = 0;
    let mut v_res_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3058_ = crate::leanh::lean_unbox_usize(v_sz_3050_);
    crate::leanh::lean_dec(v_sz_3050_);
    v_i_boxed_3059_ = crate::leanh::lean_unbox_usize(v_i_3051_);
    crate::leanh::lean_dec(v_i_3051_);
    v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_3058_, v_i_boxed_3059_, v_bs_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
    crate::leanh::lean_dec(v___y_3056_);
    crate::leanh::lean_dec_ref(v___y_3055_);
    crate::leanh::lean_dec(v___y_3054_);
    crate::leanh::lean_dec_ref(v___y_3053_);
    return v_res_3060_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Generalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_KAbstract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedGeneralizeArg_default =
        _init_l_Lean_Meta_instInhabitedGeneralizeArg_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default);
    l_Lean_Meta_instInhabitedGeneralizeArg = _init_l_Lean_Meta_instInhabitedGeneralizeArg();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Generalize(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Generalize(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_KAbstract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Generalize(builtin);
}
