// Lean compiler output
// Module: Lean.Meta.Match.CaseValues
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.FVarSubst Lean.Meta.Tactic.Subst
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_lt, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkForall,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkAppOptM, l_Lean_Meta_mkEq};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_normLitValue;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClearMany;
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{l_Lean_MVarId_intro1__, l_Lean_Meta_intro1Core};
use crate::r#gen::Lean::Meta::Tactic::Subst::{
    initialize_Lean_Meta_Tactic_Subst, l_Lean_Meta_introSubstEq,
    runtime_initialize_Lean_Meta_Tactic_Subst,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_appendTagSuffix, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
    l_Lean_Meta_throwTacticEx___redArg,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 97, 115, 101, 86, 97, 108, 117, 101, 0]};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,17243413823236116672 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16612019923665488825 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,8391571994004792969 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedCaseValuesSubgoal_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedCaseValuesSubgoal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0_value:
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
    m_data: [99, 97, 115, 101, 86, 97, 108, 117, 101, 115, 0],
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1_value:
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
            l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        3225505163679834053 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 105, 115, 116, 32, 111, 102, 32, 118, 97, 108, 117, 101, 115, 32, 109, 117, 115, 116,
        32, 110, 111, 116, 32, 98, 101, 32, 101, 109, 112, 116, 121, 0,
    ],
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 97, 115, 101, 0],
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7_value:
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
            l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        5050764861132020425 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(
    mut v_mvarId_666_: *mut crate::leanh::LeanObject,
    mut v_x_667_: *mut crate::leanh::LeanObject,
    mut v___y_668_: *mut crate::leanh::LeanObject,
    mut v___y_669_: *mut crate::leanh::LeanObject,
    mut v___y_670_: *mut crate::leanh::LeanObject,
    mut v___y_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut v_a_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_685_: u8 = 0;
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_673_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_666_,
                    v_x_667_,
                    v___y_668_,
                    v___y_669_,
                    v___y_670_,
                    v___y_671_,
                );
                if crate::leanh::lean_obj_tag(v___x_673_) == 0 {
                    v_a_674_ = crate::leanh::lean_ctor_get(v___x_673_, 0);
                    v_isSharedCheck_681_ = (!crate::leanh::lean_is_exclusive(v___x_673_)) as u8;
                    if v_isSharedCheck_681_ == 0 {
                        v___x_676_ = v___x_673_;
                        v_isShared_677_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_674_);
                        crate::leanh::lean_dec(v___x_673_);
                        v___x_676_ = crate::leanh::lean_box(0);
                        v_isShared_677_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_682_ = crate::leanh::lean_ctor_get(v___x_673_, 0);
                    v_isSharedCheck_689_ = (!crate::leanh::lean_is_exclusive(v___x_673_)) as u8;
                    if v_isSharedCheck_689_ == 0 {
                        v___x_684_ = v___x_673_;
                        v_isShared_685_ = v_isSharedCheck_689_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_682_);
                        crate::leanh::lean_dec(v___x_673_);
                        v___x_684_ = crate::leanh::lean_box(0);
                        v_isShared_685_ = v_isSharedCheck_689_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_677_ == 0 {
                    v___x_679_ = v___x_676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
                    v___x_679_ = v_reuseFailAlloc_680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_679_;
            }
            3 => {
                if v_isShared_685_ == 0 {
                    v___x_687_ = v___x_684_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
                    v___x_687_ = v_reuseFailAlloc_688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg___boxed(
    mut v_mvarId_690_: *mut crate::leanh::LeanObject,
    mut v_x_691_: *mut crate::leanh::LeanObject,
    mut v___y_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
    mut v___y_695_: *mut crate::leanh::LeanObject,
    mut v___y_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_690_, v_x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
    crate::leanh::lean_dec(v___y_695_);
    crate::leanh::lean_dec_ref(v___y_694_);
    crate::leanh::lean_dec(v___y_693_);
    crate::leanh::lean_dec_ref(v___y_692_);
    return v_res_697_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1(
    mut v_00_u03b1_698_: *mut crate::leanh::LeanObject,
    mut v_mvarId_699_: *mut crate::leanh::LeanObject,
    mut v_x_700_: *mut crate::leanh::LeanObject,
    mut v___y_701_: *mut crate::leanh::LeanObject,
    mut v___y_702_: *mut crate::leanh::LeanObject,
    mut v___y_703_: *mut crate::leanh::LeanObject,
    mut v___y_704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_699_, v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
    return v___x_706_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___boxed(
    mut v_00_u03b1_707_: *mut crate::leanh::LeanObject,
    mut v_mvarId_708_: *mut crate::leanh::LeanObject,
    mut v_x_709_: *mut crate::leanh::LeanObject,
    mut v___y_710_: *mut crate::leanh::LeanObject,
    mut v___y_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
    mut v___y_713_: *mut crate::leanh::LeanObject,
    mut v___y_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1(v_00_u03b1_707_, v_mvarId_708_, v_x_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
    crate::leanh::lean_dec(v___y_713_);
    crate::leanh::lean_dec_ref(v___y_712_);
    crate::leanh::lean_dec(v___y_711_);
    crate::leanh::lean_dec_ref(v___y_710_);
    return v_res_715_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_716_: *mut crate::leanh::LeanObject,
    mut v_x_717_: *mut crate::leanh::LeanObject,
    mut v_x_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_724_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: u8 = 0;
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_720_ = crate::leanh::lean_ctor_get(v_x_716_, 0);
                v_vs_721_ = crate::leanh::lean_ctor_get(v_x_716_, 1);
                v_isSharedCheck_745_ = (!crate::leanh::lean_is_exclusive(v_x_716_)) as u8;
                if v_isSharedCheck_745_ == 0 {
                    v___x_723_ = v_x_716_;
                    v_isShared_724_ = v_isSharedCheck_745_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_721_);
                    crate::leanh::lean_inc(v_ks_720_);
                    crate::leanh::lean_dec(v_x_716_);
                    v___x_723_ = crate::leanh::lean_box(0);
                    v_isShared_724_ = v_isSharedCheck_745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_725_ = lean_array_get_size(v_ks_720_);
                v___x_726_ = lean_nat_dec_lt(v_x_717_, v___x_725_);
                if v___x_726_ == 0 {
                    crate::leanh::lean_dec(v_x_717_);
                    v___x_727_ = lean_array_push(v_ks_720_, v_x_718_);
                    v___x_728_ = lean_array_push(v_vs_721_, v_x_719_);
                    if v_isShared_724_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_723_, 1, v___x_728_);
                        crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_727_);
                        v___x_730_ = v___x_723_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_731_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_727_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
                        v___x_730_ = v_reuseFailAlloc_731_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_732_ = lean_array_fget_borrowed(v_ks_720_, v_x_717_);
                    v___x_733_ = l_Lean_instBEqMVarId_beq(v_x_718_, v_k_x27_732_);
                    if v___x_733_ == 0 {
                        if v_isShared_724_ == 0 {
                            v___x_735_ = v___x_723_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_739_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v_ks_720_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v_vs_721_);
                            v___x_735_ = v_reuseFailAlloc_739_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_740_ = lean_array_fset(v_ks_720_, v_x_717_, v_x_718_);
                        v___x_741_ = lean_array_fset(v_vs_721_, v_x_717_, v_x_719_);
                        crate::leanh::lean_dec(v_x_717_);
                        if v_isShared_724_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_723_, 1, v___x_741_);
                            crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_740_);
                            v___x_743_ = v___x_723_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_744_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_740_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_741_);
                            v___x_743_ = v_reuseFailAlloc_744_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_730_;
            }
            3 => {
                v___x_736_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_737_ = lean_nat_add(v_x_717_, v___x_736_);
                crate::leanh::lean_dec(v_x_717_);
                v_x_716_ = v___x_735_;
                v_x_717_ = v___x_737_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_746_: *mut crate::leanh::LeanObject,
    mut v_k_747_: *mut crate::leanh::LeanObject,
    mut v_v_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_750_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_746_, v___x_749_, v_k_747_, v_v_748_);
    return v___x_750_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_751_: usize = 0;
    let mut v___x_752_: usize = 0;
    let mut v___x_753_: usize = 0;
    v___x_751_ = 5usize;
    v___x_752_ = 1usize;
    v___x_753_ = lean_usize_shift_left(v___x_752_, v___x_751_);
    return v___x_753_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_754_: usize = 0;
    let mut v___x_755_: usize = 0;
    let mut v___x_756_: usize = 0;
    v___x_754_ = 1usize;
    v___x_755_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_756_ = lean_usize_sub(v___x_755_, v___x_754_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_757_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(
    mut v_x_758_: *mut crate::leanh::LeanObject,
    mut v_x_759_: usize,
    mut v_x_760_: usize,
    mut v_x_761_: *mut crate::leanh::LeanObject,
    mut v_x_762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: usize = 0;
    let mut v___x_765_: usize = 0;
    let mut v___x_766_: usize = 0;
    let mut v___x_767_: usize = 0;
    let mut v_j_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: u8 = 0;
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v_v_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut v_node_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v___x_799_: usize = 0;
    let mut v___x_800_: usize = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_807_: u8 = 0;
    let mut v_unused_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_813_: u8 = 0;
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_818_: u8 = 0;
    let mut v_ks_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: usize = 0;
    let mut v___x_825_: u8 = 0;
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v_reuseFailAlloc_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_758_) == 0 {
                    v_es_763_ = crate::leanh::lean_ctor_get(v_x_758_, 0);
                    v___x_764_ = 5usize;
                    v___x_765_ = 1usize;
                    v___x_766_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_767_ = lean_usize_land(v_x_759_, v___x_766_);
                    v_j_768_ = lean_usize_to_nat(v___x_767_);
                    v___x_769_ = lean_array_get_size(v_es_763_);
                    v___x_770_ = lean_nat_dec_lt(v_j_768_, v___x_769_);
                    if v___x_770_ == 0 {
                        crate::leanh::lean_dec(v_j_768_);
                        crate::leanh::lean_dec(v_x_762_);
                        crate::leanh::lean_dec(v_x_761_);
                        return v_x_758_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_763_);
                        v_isSharedCheck_807_ = (!crate::leanh::lean_is_exclusive(v_x_758_)) as u8;
                        if v_isSharedCheck_807_ == 0 {
                            v_unused_808_ = crate::leanh::lean_ctor_get(v_x_758_, 0);
                            crate::leanh::lean_dec(v_unused_808_);
                            v___x_772_ = v_x_758_;
                            v_isShared_773_ = v_isSharedCheck_807_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_758_);
                            v___x_772_ = crate::leanh::lean_box(0);
                            v_isShared_773_ = v_isSharedCheck_807_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_809_ = crate::leanh::lean_ctor_get(v_x_758_, 0);
                    v_vs_810_ = crate::leanh::lean_ctor_get(v_x_758_, 1);
                    v_isSharedCheck_830_ = (!crate::leanh::lean_is_exclusive(v_x_758_)) as u8;
                    if v_isSharedCheck_830_ == 0 {
                        v___x_812_ = v_x_758_;
                        v_isShared_813_ = v_isSharedCheck_830_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_810_);
                        crate::leanh::lean_inc(v_ks_809_);
                        crate::leanh::lean_dec(v_x_758_);
                        v___x_812_ = crate::leanh::lean_box(0);
                        v_isShared_813_ = v_isSharedCheck_830_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_774_ = lean_array_fget(v_es_763_, v_j_768_);
                v___x_775_ = crate::leanh::lean_box(0);
                v_xs_x27_776_ = lean_array_fset(v_es_763_, v_j_768_, v___x_775_);
                match crate::leanh::lean_obj_tag(v_v_774_) {
                    0 => {
                        v_key_783_ = crate::leanh::lean_ctor_get(v_v_774_, 0);
                        v_val_784_ = crate::leanh::lean_ctor_get(v_v_774_, 1);
                        v_isSharedCheck_794_ = (!crate::leanh::lean_is_exclusive(v_v_774_)) as u8;
                        if v_isSharedCheck_794_ == 0 {
                            v___x_786_ = v_v_774_;
                            v_isShared_787_ = v_isSharedCheck_794_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_784_);
                            crate::leanh::lean_inc(v_key_783_);
                            crate::leanh::lean_dec(v_v_774_);
                            v___x_786_ = crate::leanh::lean_box(0);
                            v_isShared_787_ = v_isSharedCheck_794_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_795_ = crate::leanh::lean_ctor_get(v_v_774_, 0);
                        v_isSharedCheck_805_ = (!crate::leanh::lean_is_exclusive(v_v_774_)) as u8;
                        if v_isSharedCheck_805_ == 0 {
                            v___x_797_ = v_v_774_;
                            v_isShared_798_ = v_isSharedCheck_805_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_795_);
                            crate::leanh::lean_dec(v_v_774_);
                            v___x_797_ = crate::leanh::lean_box(0);
                            v_isShared_798_ = v_isSharedCheck_805_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_806_, 0, v_x_761_);
                        crate::leanh::lean_ctor_set(v___x_806_, 1, v_x_762_);
                        v___y_778_ = v___x_806_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_779_ = lean_array_fset(v_xs_x27_776_, v_j_768_, v___y_778_);
                crate::leanh::lean_dec(v_j_768_);
                if v_isShared_773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_779_);
                    v___x_781_ = v___x_772_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                    v___x_781_ = v_reuseFailAlloc_782_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_781_;
            }
            4 => {
                v___x_788_ = l_Lean_instBEqMVarId_beq(v_x_761_, v_key_783_);
                if v___x_788_ == 0 {
                    crate::leanh::lean_del_object(v___x_786_);
                    v___x_789_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_783_, v_val_784_, v_x_761_, v_x_762_,
                    );
                    v___x_790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_790_, 0, v___x_789_);
                    v___y_778_ = v___x_790_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_784_);
                    crate::leanh::lean_dec(v_key_783_);
                    if v_isShared_787_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_786_, 1, v_x_762_);
                        crate::leanh::lean_ctor_set(v___x_786_, 0, v_x_761_);
                        v___x_792_ = v___x_786_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_793_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_x_761_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_793_, 1, v_x_762_);
                        v___x_792_ = v_reuseFailAlloc_793_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_778_ = v___x_792_;
                state = 2;
                continue;
            }
            6 => {
                v___x_799_ = lean_usize_shift_right(v_x_759_, v___x_764_);
                v___x_800_ = lean_usize_add(v_x_760_, v___x_765_);
                v___x_801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_node_795_, v___x_799_, v___x_800_, v_x_761_, v_x_762_);
                if v_isShared_798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_801_);
                    v___x_803_ = v___x_797_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
                    v___x_803_ = v_reuseFailAlloc_804_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_778_ = v___x_803_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_813_ == 0 {
                    v___x_815_ = v___x_812_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_829_, 0, v_ks_809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_829_, 1, v_vs_810_);
                    v___x_815_ = v_reuseFailAlloc_829_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(v___x_815_, v_x_761_, v_x_762_);
                v___x_824_ = 7usize;
                v___x_825_ = lean_usize_dec_le(v___x_824_, v_x_760_);
                if v___x_825_ == 0 {
                    v___x_826_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_816_);
                    v___x_827_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_828_ = lean_nat_dec_lt(v___x_826_, v___x_827_);
                    crate::leanh::lean_dec(v___x_826_);
                    v___y_818_ = v___x_828_;
                    state = 10;
                    continue;
                } else {
                    v___y_818_ = v___x_825_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_818_ == 0 {
                    v_ks_819_ = crate::leanh::lean_ctor_get(v_newNode_816_, 0);
                    crate::leanh::lean_inc_ref(v_ks_819_);
                    v_vs_820_ = crate::leanh::lean_ctor_get(v_newNode_816_, 1);
                    crate::leanh::lean_inc_ref(v_vs_820_);
                    crate::leanh::lean_dec_ref(v_newNode_816_);
                    v___x_821_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_x_760_, v_ks_819_, v_vs_820_, v___x_821_, v___x_822_);
                    crate::leanh::lean_dec_ref(v_vs_820_);
                    crate::leanh::lean_dec_ref(v_ks_819_);
                    return v___x_823_;
                } else {
                    return v_newNode_816_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_831_: usize,
    mut v_keys_832_: *mut crate::leanh::LeanObject,
    mut v_vals_833_: *mut crate::leanh::LeanObject,
    mut v_i_834_: *mut crate::leanh::LeanObject,
    mut v_entries_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v_k_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u64 = 0;
    let mut v_h_841_: usize = 0;
    let mut v___x_842_: usize = 0;
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: usize = 0;
    let mut v___x_845_: usize = 0;
    let mut v___x_846_: usize = 0;
    let mut v_h_847_: usize = 0;
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_836_ = lean_array_get_size(v_keys_832_);
                v___x_837_ = lean_nat_dec_lt(v_i_834_, v___x_836_);
                if v___x_837_ == 0 {
                    crate::leanh::lean_dec(v_i_834_);
                    return v_entries_835_;
                } else {
                    v_k_838_ = lean_array_fget_borrowed(v_keys_832_, v_i_834_);
                    v_v_839_ = lean_array_fget_borrowed(v_vals_833_, v_i_834_);
                    v___x_840_ = l_Lean_instHashableMVarId_hash(v_k_838_);
                    v_h_841_ = lean_uint64_to_usize(v___x_840_);
                    v___x_842_ = 5usize;
                    v___x_843_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_844_ = 1usize;
                    v___x_845_ = lean_usize_sub(v_depth_831_, v___x_844_);
                    v___x_846_ = lean_usize_mul(v___x_842_, v___x_845_);
                    v_h_847_ = lean_usize_shift_right(v_h_841_, v___x_846_);
                    v___x_848_ = lean_nat_add(v_i_834_, v___x_843_);
                    crate::leanh::lean_dec(v_i_834_);
                    crate::leanh::lean_inc(v_v_839_);
                    crate::leanh::lean_inc(v_k_838_);
                    v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_entries_835_, v_h_847_, v_depth_831_, v_k_838_, v_v_839_);
                    v_i_834_ = v___x_848_;
                    v_entries_835_ = v___x_849_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_851_: *mut crate::leanh::LeanObject,
    mut v_keys_852_: *mut crate::leanh::LeanObject,
    mut v_vals_853_: *mut crate::leanh::LeanObject,
    mut v_i_854_: *mut crate::leanh::LeanObject,
    mut v_entries_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_856_: usize = 0;
    let mut v_res_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_856_ = crate::leanh::lean_unbox_usize(v_depth_851_);
    crate::leanh::lean_dec(v_depth_851_);
    v_res_857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_856_, v_keys_852_, v_vals_853_, v_i_854_, v_entries_855_);
    crate::leanh::lean_dec_ref(v_vals_853_);
    crate::leanh::lean_dec_ref(v_keys_852_);
    return v_res_857_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_858_: *mut crate::leanh::LeanObject,
    mut v_x_859_: *mut crate::leanh::LeanObject,
    mut v_x_860_: *mut crate::leanh::LeanObject,
    mut v_x_861_: *mut crate::leanh::LeanObject,
    mut v_x_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2110__boxed_863_: usize = 0;
    let mut v_x_2111__boxed_864_: usize = 0;
    let mut v_res_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2110__boxed_863_ = crate::leanh::lean_unbox_usize(v_x_859_);
    crate::leanh::lean_dec(v_x_859_);
    v_x_2111__boxed_864_ = crate::leanh::lean_unbox_usize(v_x_860_);
    crate::leanh::lean_dec(v_x_860_);
    v_res_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_858_, v_x_2110__boxed_863_, v_x_2111__boxed_864_, v_x_861_, v_x_862_);
    return v_res_865_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(
    mut v_x_866_: *mut crate::leanh::LeanObject,
    mut v_x_867_: *mut crate::leanh::LeanObject,
    mut v_x_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_869_: u64 = 0;
    let mut v___x_870_: usize = 0;
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_instHashableMVarId_hash(v_x_867_);
    v___x_870_ = lean_uint64_to_usize(v___x_869_);
    v___x_871_ = 1usize;
    v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_866_, v___x_870_, v___x_871_, v_x_867_, v_x_868_);
    return v___x_872_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(
    mut v_mvarId_873_: *mut crate::leanh::LeanObject,
    mut v_val_874_: *mut crate::leanh::LeanObject,
    mut v___y_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_885_: u8 = 0;
    let mut v_depth_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_877_ = lean_st_ref_take(v___y_875_);
                v_mctx_878_ = crate::leanh::lean_ctor_get(v___x_877_, 0);
                v_cache_879_ = crate::leanh::lean_ctor_get(v___x_877_, 1);
                v_zetaDeltaFVarIds_880_ = crate::leanh::lean_ctor_get(v___x_877_, 2);
                v_postponed_881_ = crate::leanh::lean_ctor_get(v___x_877_, 3);
                v_diag_882_ = crate::leanh::lean_ctor_get(v___x_877_, 4);
                v_isSharedCheck_910_ = (!crate::leanh::lean_is_exclusive(v___x_877_)) as u8;
                if v_isSharedCheck_910_ == 0 {
                    v___x_884_ = v___x_877_;
                    v_isShared_885_ = v_isSharedCheck_910_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_882_);
                    crate::leanh::lean_inc(v_postponed_881_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_880_);
                    crate::leanh::lean_inc(v_cache_879_);
                    crate::leanh::lean_inc(v_mctx_878_);
                    crate::leanh::lean_dec(v___x_877_);
                    v___x_884_ = crate::leanh::lean_box(0);
                    v_isShared_885_ = v_isSharedCheck_910_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_886_ = crate::leanh::lean_ctor_get(v_mctx_878_, 0);
                v_levelAssignDepth_887_ = crate::leanh::lean_ctor_get(v_mctx_878_, 1);
                v_lmvarCounter_888_ = crate::leanh::lean_ctor_get(v_mctx_878_, 2);
                v_mvarCounter_889_ = crate::leanh::lean_ctor_get(v_mctx_878_, 3);
                v_lDecls_890_ = crate::leanh::lean_ctor_get(v_mctx_878_, 4);
                v_decls_891_ = crate::leanh::lean_ctor_get(v_mctx_878_, 5);
                v_userNames_892_ = crate::leanh::lean_ctor_get(v_mctx_878_, 6);
                v_lAssignment_893_ = crate::leanh::lean_ctor_get(v_mctx_878_, 7);
                v_eAssignment_894_ = crate::leanh::lean_ctor_get(v_mctx_878_, 8);
                v_dAssignment_895_ = crate::leanh::lean_ctor_get(v_mctx_878_, 9);
                v_isSharedCheck_909_ = (!crate::leanh::lean_is_exclusive(v_mctx_878_)) as u8;
                if v_isSharedCheck_909_ == 0 {
                    v___x_897_ = v_mctx_878_;
                    v_isShared_898_ = v_isSharedCheck_909_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_895_);
                    crate::leanh::lean_inc(v_eAssignment_894_);
                    crate::leanh::lean_inc(v_lAssignment_893_);
                    crate::leanh::lean_inc(v_userNames_892_);
                    crate::leanh::lean_inc(v_decls_891_);
                    crate::leanh::lean_inc(v_lDecls_890_);
                    crate::leanh::lean_inc(v_mvarCounter_889_);
                    crate::leanh::lean_inc(v_lmvarCounter_888_);
                    crate::leanh::lean_inc(v_levelAssignDepth_887_);
                    crate::leanh::lean_inc(v_depth_886_);
                    crate::leanh::lean_dec(v_mctx_878_);
                    v___x_897_ = crate::leanh::lean_box(0);
                    v_isShared_898_ = v_isSharedCheck_909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_899_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(v_eAssignment_894_, v_mvarId_873_, v_val_874_);
                if v_isShared_898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_897_, 8, v___x_899_);
                    v___x_901_ = v___x_897_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v_depth_886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 1, v_levelAssignDepth_887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 2, v_lmvarCounter_888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 3, v_mvarCounter_889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 4, v_lDecls_890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 5, v_decls_891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 6, v_userNames_892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 7, v_lAssignment_893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 8, v___x_899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 9, v_dAssignment_895_);
                    v___x_901_ = v_reuseFailAlloc_908_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_885_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_884_, 0, v___x_901_);
                    v___x_903_ = v___x_884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 1, v_cache_879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 2, v_zetaDeltaFVarIds_880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 3, v_postponed_881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 4, v_diag_882_);
                    v___x_903_ = v_reuseFailAlloc_907_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_904_ = lean_st_ref_set(v___y_875_, v___x_903_);
                v___x_905_ = crate::leanh::lean_box(0);
                v___x_906_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_906_, 0, v___x_905_);
                return v___x_906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg___boxed(
    mut v_mvarId_911_: *mut crate::leanh::LeanObject,
    mut v_val_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_915_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_911_, v_val_912_, v___y_913_);
    crate::leanh::lean_dec(v___y_913_);
    return v_res_915_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_922_ = crate::leanh::lean_box(0);
    v___x_923_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3;
    v___x_924_ = l_Lean_mkConst(v___x_923_, v___x_922_);
    return v___x_924_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ = crate::leanh::lean_box(0);
    v___x_929_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
    v___x_931_ = lean_array_push(v___x_930_, v___x_928_);
    return v___x_931_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(
    mut v_mvarId_932_: *mut crate::leanh::LeanObject,
    mut v_value_933_: *mut crate::leanh::LeanObject,
    mut v_fvarId_934_: *mut crate::leanh::LeanObject,
    mut v_hName_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_983_: u8 = 0;
    let mut v_unused_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_988_: u8 = 0;
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_992_: u8 = 0;
    let mut v_a_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut v_a_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1004_: u8 = 0;
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1012_: u8 = 0;
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1016_: u8 = 0;
    let mut v_a_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1020_: u8 = 0;
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1024_: u8 = 0;
    let mut v_a_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1028_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut v_a_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v_a_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1044_: u8 = 0;
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_932_);
                v___x_941_ = l_Lean_MVarId_getTag(
                    v_mvarId_932_,
                    v___y_936_,
                    v___y_937_,
                    v___y_938_,
                    v___y_939_,
                );
                if crate::leanh::lean_obj_tag(v___x_941_) == 0 {
                    v_a_942_ = crate::leanh::lean_ctor_get(v___x_941_, 0);
                    crate::leanh::lean_inc(v_a_942_);
                    crate::leanh::lean_dec_ref_known(v___x_941_, 1);
                    v___x_943_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1;
                    crate::leanh::lean_inc(v_mvarId_932_);
                    v___x_944_ = l_Lean_MVarId_checkNotAssigned(
                        v_mvarId_932_,
                        v___x_943_,
                        v___y_936_,
                        v___y_937_,
                        v___y_938_,
                        v___y_939_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_944_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_944_, 1);
                        crate::leanh::lean_inc(v_mvarId_932_);
                        v___x_945_ = l_Lean_MVarId_getType(
                            v_mvarId_932_,
                            v___y_936_,
                            v___y_937_,
                            v___y_938_,
                            v___y_939_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_945_) == 0 {
                            v_a_946_ = crate::leanh::lean_ctor_get(v___x_945_, 0);
                            crate::leanh::lean_inc(v_a_946_);
                            crate::leanh::lean_dec_ref_known(v___x_945_, 1);
                            v___x_947_ = l_Lean_Meta_normLitValue(
                                v_value_933_,
                                v___y_936_,
                                v___y_937_,
                                v___y_938_,
                                v___y_939_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_947_) == 0 {
                                v_a_948_ = crate::leanh::lean_ctor_get(v___x_947_, 0);
                                crate::leanh::lean_inc(v_a_948_);
                                crate::leanh::lean_dec_ref_known(v___x_947_, 1);
                                v___x_949_ = l_Lean_mkFVar(v_fvarId_934_);
                                v___x_950_ = l_Lean_Meta_mkEq(
                                    v___x_949_, v_a_948_, v___y_936_, v___y_937_, v___y_938_,
                                    v___y_939_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_950_) == 0 {
                                    v_a_951_ = crate::leanh::lean_ctor_get(v___x_950_, 0);
                                    crate::leanh::lean_inc_n(v_a_951_, 3);
                                    crate::leanh::lean_dec_ref_known(v___x_950_, 1);
                                    v___x_952_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4_once), _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4);
                                    v___x_953_ = l_Lean_Expr_app___override(v___x_952_, v_a_951_);
                                    v___x_954_ = 0;
                                    crate::leanh::lean_inc(v_a_946_);
                                    crate::leanh::lean_inc(v_hName_935_);
                                    v___x_955_ = l_Lean_mkForall(
                                        v_hName_935_,
                                        v___x_954_,
                                        v_a_951_,
                                        v_a_946_,
                                    );
                                    crate::leanh::lean_inc(v_a_942_);
                                    v___x_956_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                        v___x_955_, v_a_942_, v___y_936_, v___y_937_, v___y_938_,
                                        v___y_939_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_956_) == 0 {
                                        v_a_957_ = crate::leanh::lean_ctor_get(v___x_956_, 0);
                                        crate::leanh::lean_inc(v_a_957_);
                                        crate::leanh::lean_dec_ref_known(v___x_956_, 1);
                                        v___x_958_ = l_Lean_mkForall(
                                            v_hName_935_,
                                            v___x_954_,
                                            v___x_953_,
                                            v_a_946_,
                                        );
                                        v___x_959_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                            v___x_958_, v_a_942_, v___y_936_, v___y_937_,
                                            v___y_938_, v___y_939_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_959_) == 0 {
                                            v_a_960_ = crate::leanh::lean_ctor_get(v___x_959_, 0);
                                            crate::leanh::lean_inc_n(v_a_960_, 2);
                                            crate::leanh::lean_dec_ref_known(v___x_959_, 1);
                                            v___x_961_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6;
                                            v___x_962_ = crate::leanh::lean_box(0);
                                            v___x_963_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_963_, 0, v_a_951_);
                                            crate::leanh::lean_inc(v_a_957_);
                                            v___x_964_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_964_, 0, v_a_957_);
                                            v___x_965_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_965_, 0, v_a_960_);
                                            v___x_966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7_once), _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7);
                                            v___x_967_ = lean_array_push(v___x_966_, v___x_963_);
                                            v___x_968_ = lean_array_push(v___x_967_, v___x_962_);
                                            v___x_969_ = lean_array_push(v___x_968_, v___x_964_);
                                            v___x_970_ = lean_array_push(v___x_969_, v___x_965_);
                                            v___x_971_ = l_Lean_Meta_mkAppOptM(
                                                v___x_961_, v___x_970_, v___y_936_, v___y_937_,
                                                v___y_938_, v___y_939_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_971_) == 0 {
                                                v_a_972_ =
                                                    crate::leanh::lean_ctor_get(v___x_971_, 0);
                                                crate::leanh::lean_inc(v_a_972_);
                                                crate::leanh::lean_dec_ref_known(v___x_971_, 1);
                                                v___x_973_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_932_, v_a_972_, v___y_937_);
                                                v_isSharedCheck_983_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_973_))
                                                        as u8;
                                                if v_isSharedCheck_983_ == 0 {
                                                    v_unused_984_ =
                                                        crate::leanh::lean_ctor_get(v___x_973_, 0);
                                                    crate::leanh::lean_dec(v_unused_984_);
                                                    v___x_975_ = v___x_973_;
                                                    v_isShared_976_ = v_isSharedCheck_983_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_973_);
                                                    v___x_975_ = crate::leanh::lean_box(0);
                                                    v_isShared_976_ = v_isSharedCheck_983_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_960_);
                                                crate::leanh::lean_dec(v_a_957_);
                                                crate::leanh::lean_dec(v_mvarId_932_);
                                                v_a_985_ =
                                                    crate::leanh::lean_ctor_get(v___x_971_, 0);
                                                v_isSharedCheck_992_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_971_))
                                                        as u8;
                                                if v_isSharedCheck_992_ == 0 {
                                                    v___x_987_ = v___x_971_;
                                                    v_isShared_988_ = v_isSharedCheck_992_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_985_);
                                                    crate::leanh::lean_dec(v___x_971_);
                                                    v___x_987_ = crate::leanh::lean_box(0);
                                                    v_isShared_988_ = v_isSharedCheck_992_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_957_);
                                            crate::leanh::lean_dec(v_a_951_);
                                            crate::leanh::lean_dec(v_mvarId_932_);
                                            v_a_993_ = crate::leanh::lean_ctor_get(v___x_959_, 0);
                                            v_isSharedCheck_1000_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_959_))
                                                    as u8;
                                            if v_isSharedCheck_1000_ == 0 {
                                                v___x_995_ = v___x_959_;
                                                v_isShared_996_ = v_isSharedCheck_1000_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_993_);
                                                crate::leanh::lean_dec(v___x_959_);
                                                v___x_995_ = crate::leanh::lean_box(0);
                                                v_isShared_996_ = v_isSharedCheck_1000_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_953_);
                                        crate::leanh::lean_dec(v_a_951_);
                                        crate::leanh::lean_dec(v_a_946_);
                                        crate::leanh::lean_dec(v_a_942_);
                                        crate::leanh::lean_dec(v_hName_935_);
                                        crate::leanh::lean_dec(v_mvarId_932_);
                                        v_a_1001_ = crate::leanh::lean_ctor_get(v___x_956_, 0);
                                        v_isSharedCheck_1008_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_956_)) as u8;
                                        if v_isSharedCheck_1008_ == 0 {
                                            v___x_1003_ = v___x_956_;
                                            v_isShared_1004_ = v_isSharedCheck_1008_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1001_);
                                            crate::leanh::lean_dec(v___x_956_);
                                            v___x_1003_ = crate::leanh::lean_box(0);
                                            v_isShared_1004_ = v_isSharedCheck_1008_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_946_);
                                    crate::leanh::lean_dec(v_a_942_);
                                    crate::leanh::lean_dec(v_hName_935_);
                                    crate::leanh::lean_dec(v_mvarId_932_);
                                    v_a_1009_ = crate::leanh::lean_ctor_get(v___x_950_, 0);
                                    v_isSharedCheck_1016_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_950_)) as u8;
                                    if v_isSharedCheck_1016_ == 0 {
                                        v___x_1011_ = v___x_950_;
                                        v_isShared_1012_ = v_isSharedCheck_1016_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1009_);
                                        crate::leanh::lean_dec(v___x_950_);
                                        v___x_1011_ = crate::leanh::lean_box(0);
                                        v_isShared_1012_ = v_isSharedCheck_1016_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_946_);
                                crate::leanh::lean_dec(v_a_942_);
                                crate::leanh::lean_dec(v_hName_935_);
                                crate::leanh::lean_dec(v_fvarId_934_);
                                crate::leanh::lean_dec(v_mvarId_932_);
                                v_a_1017_ = crate::leanh::lean_ctor_get(v___x_947_, 0);
                                v_isSharedCheck_1024_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_947_)) as u8;
                                if v_isSharedCheck_1024_ == 0 {
                                    v___x_1019_ = v___x_947_;
                                    v_isShared_1020_ = v_isSharedCheck_1024_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1017_);
                                    crate::leanh::lean_dec(v___x_947_);
                                    v___x_1019_ = crate::leanh::lean_box(0);
                                    v_isShared_1020_ = v_isSharedCheck_1024_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_942_);
                            crate::leanh::lean_dec(v_hName_935_);
                            crate::leanh::lean_dec(v_fvarId_934_);
                            crate::leanh::lean_dec_ref(v_value_933_);
                            crate::leanh::lean_dec(v_mvarId_932_);
                            v_a_1025_ = crate::leanh::lean_ctor_get(v___x_945_, 0);
                            v_isSharedCheck_1032_ =
                                (!crate::leanh::lean_is_exclusive(v___x_945_)) as u8;
                            if v_isSharedCheck_1032_ == 0 {
                                v___x_1027_ = v___x_945_;
                                v_isShared_1028_ = v_isSharedCheck_1032_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1025_);
                                crate::leanh::lean_dec(v___x_945_);
                                v___x_1027_ = crate::leanh::lean_box(0);
                                v_isShared_1028_ = v_isSharedCheck_1032_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_942_);
                        crate::leanh::lean_dec(v_hName_935_);
                        crate::leanh::lean_dec(v_fvarId_934_);
                        crate::leanh::lean_dec_ref(v_value_933_);
                        crate::leanh::lean_dec(v_mvarId_932_);
                        v_a_1033_ = crate::leanh::lean_ctor_get(v___x_944_, 0);
                        v_isSharedCheck_1040_ =
                            (!crate::leanh::lean_is_exclusive(v___x_944_)) as u8;
                        if v_isSharedCheck_1040_ == 0 {
                            v___x_1035_ = v___x_944_;
                            v_isShared_1036_ = v_isSharedCheck_1040_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1033_);
                            crate::leanh::lean_dec(v___x_944_);
                            v___x_1035_ = crate::leanh::lean_box(0);
                            v_isShared_1036_ = v_isSharedCheck_1040_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_hName_935_);
                    crate::leanh::lean_dec(v_fvarId_934_);
                    crate::leanh::lean_dec_ref(v_value_933_);
                    crate::leanh::lean_dec(v_mvarId_932_);
                    v_a_1041_ = crate::leanh::lean_ctor_get(v___x_941_, 0);
                    v_isSharedCheck_1048_ = (!crate::leanh::lean_is_exclusive(v___x_941_)) as u8;
                    if v_isSharedCheck_1048_ == 0 {
                        v___x_1043_ = v___x_941_;
                        v_isShared_1044_ = v_isSharedCheck_1048_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1041_);
                        crate::leanh::lean_dec(v___x_941_);
                        v___x_1043_ = crate::leanh::lean_box(0);
                        v_isShared_1044_ = v_isSharedCheck_1048_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_977_ = l_Lean_Expr_mvarId_x21(v_a_957_);
                crate::leanh::lean_dec(v_a_957_);
                v___x_978_ = l_Lean_Expr_mvarId_x21(v_a_960_);
                crate::leanh::lean_dec(v_a_960_);
                v___x_979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_979_, 0, v___x_977_);
                crate::leanh::lean_ctor_set(v___x_979_, 1, v___x_978_);
                if v_isShared_976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_979_);
                    v___x_981_ = v___x_975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
                    v___x_981_ = v_reuseFailAlloc_982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_981_;
            }
            3 => {
                if v_isShared_988_ == 0 {
                    v___x_990_ = v___x_987_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
                    v___x_990_ = v_reuseFailAlloc_991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_990_;
            }
            5 => {
                if v_isShared_996_ == 0 {
                    v___x_998_ = v___x_995_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
                    v___x_998_ = v_reuseFailAlloc_999_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_998_;
            }
            7 => {
                if v_isShared_1004_ == 0 {
                    v___x_1006_ = v___x_1003_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
                    v___x_1006_ = v_reuseFailAlloc_1007_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1006_;
            }
            9 => {
                if v_isShared_1012_ == 0 {
                    v___x_1014_ = v___x_1011_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
                    v___x_1014_ = v_reuseFailAlloc_1015_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1014_;
            }
            11 => {
                if v_isShared_1020_ == 0 {
                    v___x_1022_ = v___x_1019_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1023_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
                    v___x_1022_ = v_reuseFailAlloc_1023_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1022_;
            }
            13 => {
                if v_isShared_1028_ == 0 {
                    v___x_1030_ = v___x_1027_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
                    v___x_1030_ = v_reuseFailAlloc_1031_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1030_;
            }
            15 => {
                if v_isShared_1036_ == 0 {
                    v___x_1038_ = v___x_1035_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
                    v___x_1038_ = v_reuseFailAlloc_1039_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1038_;
            }
            17 => {
                if v_isShared_1044_ == 0 {
                    v___x_1046_ = v___x_1043_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
                    v___x_1046_ = v_reuseFailAlloc_1047_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed(
    mut v_mvarId_1049_: *mut crate::leanh::LeanObject,
    mut v_value_1050_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1051_: *mut crate::leanh::LeanObject,
    mut v_hName_1052_: *mut crate::leanh::LeanObject,
    mut v___y_1053_: *mut crate::leanh::LeanObject,
    mut v___y_1054_: *mut crate::leanh::LeanObject,
    mut v___y_1055_: *mut crate::leanh::LeanObject,
    mut v___y_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1058_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(
        v_mvarId_1049_,
        v_value_1050_,
        v_fvarId_1051_,
        v_hName_1052_,
        v___y_1053_,
        v___y_1054_,
        v___y_1055_,
        v___y_1056_,
    );
    crate::leanh::lean_dec(v___y_1056_);
    crate::leanh::lean_dec_ref(v___y_1055_);
    crate::leanh::lean_dec(v___y_1054_);
    crate::leanh::lean_dec_ref(v___y_1053_);
    return v_res_1058_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(
    mut v_mvarId_1059_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1060_: *mut crate::leanh::LeanObject,
    mut v_value_1061_: *mut crate::leanh::LeanObject,
    mut v_hName_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_a_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_1059_);
    v___f_1068_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1068_, 0, v_mvarId_1059_);
    crate::leanh::lean_closure_set(v___f_1068_, 1, v_value_1061_);
    crate::leanh::lean_closure_set(v___f_1068_, 2, v_fvarId_1060_);
    crate::leanh::lean_closure_set(v___f_1068_, 3, v_hName_1062_);
    v___x_1069_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_1059_, v___f_1068_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
    return v___x_1069_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___boxed(
    mut v_mvarId_1070_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1071_: *mut crate::leanh::LeanObject,
    mut v_value_1072_: *mut crate::leanh::LeanObject,
    mut v_hName_1073_: *mut crate::leanh::LeanObject,
    mut v_a_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1079_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(
        v_mvarId_1070_,
        v_fvarId_1071_,
        v_value_1072_,
        v_hName_1073_,
        v_a_1074_,
        v_a_1075_,
        v_a_1076_,
        v_a_1077_,
    );
    crate::leanh::lean_dec(v_a_1077_);
    crate::leanh::lean_dec_ref(v_a_1076_);
    crate::leanh::lean_dec(v_a_1075_);
    crate::leanh::lean_dec_ref(v_a_1074_);
    return v_res_1079_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(
    mut v_mvarId_1080_: *mut crate::leanh::LeanObject,
    mut v_val_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_1080_, v_val_1081_, v___y_1083_);
    return v___x_1087_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___boxed(
    mut v_mvarId_1088_: *mut crate::leanh::LeanObject,
    mut v_val_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(v_mvarId_1088_, v_val_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
    crate::leanh::lean_dec(v___y_1093_);
    crate::leanh::lean_dec_ref(v___y_1092_);
    crate::leanh::lean_dec(v___y_1091_);
    crate::leanh::lean_dec_ref(v___y_1090_);
    return v_res_1095_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0(
    mut v_00_u03b2_1096_: *mut crate::leanh::LeanObject,
    mut v_x_1097_: *mut crate::leanh::LeanObject,
    mut v_x_1098_: *mut crate::leanh::LeanObject,
    mut v_x_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(v_x_1097_, v_x_1098_, v_x_1099_);
    return v___x_1100_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1101_: *mut crate::leanh::LeanObject,
    mut v_x_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: usize,
    mut v_x_1104_: usize,
    mut v_x_1105_: *mut crate::leanh::LeanObject,
    mut v_x_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_1102_, v_x_1103_, v_x_1104_, v_x_1105_, v_x_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
    mut v_x_1110_: *mut crate::leanh::LeanObject,
    mut v_x_1111_: *mut crate::leanh::LeanObject,
    mut v_x_1112_: *mut crate::leanh::LeanObject,
    mut v_x_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2644__boxed_1114_: usize = 0;
    let mut v_x_2645__boxed_1115_: usize = 0;
    let mut v_res_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2644__boxed_1114_ = crate::leanh::lean_unbox_usize(v_x_1110_);
    crate::leanh::lean_dec(v_x_1110_);
    v_x_2645__boxed_1115_ = crate::leanh::lean_unbox_usize(v_x_1111_);
    crate::leanh::lean_dec(v_x_1111_);
    v_res_1116_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(v_00_u03b2_1108_, v_x_1109_, v_x_2644__boxed_1114_, v_x_2645__boxed_1115_, v_x_1112_, v_x_1113_);
    return v_res_1116_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_1117_: *mut crate::leanh::LeanObject,
    mut v_n_1118_: *mut crate::leanh::LeanObject,
    mut v_k_1119_: *mut crate::leanh::LeanObject,
    mut v_v_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1118_, v_k_1119_, v_v_1120_);
    return v___x_1121_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1122_: *mut crate::leanh::LeanObject,
    mut v_depth_1123_: usize,
    mut v_keys_1124_: *mut crate::leanh::LeanObject,
    mut v_vals_1125_: *mut crate::leanh::LeanObject,
    mut v_heq_1126_: *mut crate::leanh::LeanObject,
    mut v_i_1127_: *mut crate::leanh::LeanObject,
    mut v_entries_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1123_, v_keys_1124_, v_vals_1125_, v_i_1127_, v_entries_1128_);
    return v___x_1129_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_1130_: *mut crate::leanh::LeanObject,
    mut v_depth_1131_: *mut crate::leanh::LeanObject,
    mut v_keys_1132_: *mut crate::leanh::LeanObject,
    mut v_vals_1133_: *mut crate::leanh::LeanObject,
    mut v_heq_1134_: *mut crate::leanh::LeanObject,
    mut v_i_1135_: *mut crate::leanh::LeanObject,
    mut v_entries_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1137_: usize = 0;
    let mut v_res_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1137_ = crate::leanh::lean_unbox_usize(v_depth_1131_);
    crate::leanh::lean_dec(v_depth_1131_);
    v_res_1138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1130_, v_depth_boxed_1137_, v_keys_1132_, v_vals_1133_, v_heq_1134_, v_i_1135_, v_entries_1136_);
    crate::leanh::lean_dec_ref(v_vals_1133_);
    crate::leanh::lean_dec_ref(v_keys_1132_);
    return v_res_1138_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
    mut v_x_1141_: *mut crate::leanh::LeanObject,
    mut v_x_1142_: *mut crate::leanh::LeanObject,
    mut v_x_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1140_, v_x_1141_, v_x_1142_, v_x_1143_);
    return v___x_1144_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3;
    v___x_1160_ = l_Lean_MessageData_ofFormat(v___x_1159_);
    return v___x_1160_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4_once
        ),
        _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4,
    );
    v___x_1162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
    return v___x_1162_;
}
pub unsafe fn l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(
    mut v_fvarId_1166_: *mut crate::leanh::LeanObject,
    mut v_hNamePrefix_1167_: *mut crate::leanh::LeanObject,
    mut v_needHyps_1168_: u8,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
    mut v_a_1173_: *mut crate::leanh::LeanObject,
    mut v_a_1174_: *mut crate::leanh::LeanObject,
    mut v_a_1175_: *mut crate::leanh::LeanObject,
    mut v_a_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1215_: u8 = 0;
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1222_: u8 = 0;
    let mut v_unused_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1257_: u8 = 0;
    let mut v_a_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1261_: u8 = 0;
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_a_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1273_: u8 = 0;
    let mut v_a_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1281_: u8 = 0;
    let mut v_a_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1171_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1173_);
                    crate::leanh::lean_dec_ref(v_a_1172_);
                    crate::leanh::lean_dec(v_a_1169_);
                    crate::leanh::lean_dec(v_hNamePrefix_1167_);
                    crate::leanh::lean_dec(v_fvarId_1166_);
                    v___x_1179_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1;
                    v___x_1180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5_once), _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5);
                    v___x_1181_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_1179_,
                        v_a_1170_,
                        v___x_1180_,
                        v_a_1174_,
                        v_a_1175_,
                        v_a_1176_,
                        v_a_1177_,
                    );
                    return v___x_1181_;
                } else {
                    v_head_1182_ = crate::leanh::lean_ctor_get(v_a_1171_, 0);
                    crate::leanh::lean_inc(v_head_1182_);
                    v_tail_1183_ = crate::leanh::lean_ctor_get(v_a_1171_, 1);
                    crate::leanh::lean_inc(v_tail_1183_);
                    crate::leanh::lean_dec_ref_known(v_a_1171_, 2);
                    crate::leanh::lean_inc(v_a_1169_);
                    crate::leanh::lean_inc(v_hNamePrefix_1167_);
                    v___x_1184_ = lean_name_append_index_after(v_hNamePrefix_1167_, v_a_1169_);
                    crate::leanh::lean_inc(v_fvarId_1166_);
                    v___x_1185_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(
                        v_a_1170_,
                        v_fvarId_1166_,
                        v_head_1182_,
                        v___x_1184_,
                        v_a_1174_,
                        v_a_1175_,
                        v_a_1176_,
                        v_a_1177_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1185_) == 0 {
                        v_a_1186_ = crate::leanh::lean_ctor_get(v___x_1185_, 0);
                        crate::leanh::lean_inc(v_a_1186_);
                        crate::leanh::lean_dec_ref_known(v___x_1185_, 1);
                        v_fst_1187_ = crate::leanh::lean_ctor_get(v_a_1186_, 0);
                        crate::leanh::lean_inc_n(v_fst_1187_, 2);
                        v_snd_1188_ = crate::leanh::lean_ctor_get(v_a_1186_, 1);
                        crate::leanh::lean_inc(v_snd_1188_);
                        crate::leanh::lean_dec(v_a_1186_);
                        v___x_1189_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7;
                        crate::leanh::lean_inc(v_a_1169_);
                        v___x_1190_ = lean_name_append_index_after(v___x_1189_, v_a_1169_);
                        v___x_1191_ = l_Lean_Meta_appendTagSuffix(
                            v_fst_1187_,
                            v___x_1190_,
                            v_a_1174_,
                            v_a_1175_,
                            v_a_1176_,
                            v_a_1177_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1191_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1191_, 1);
                            v___x_1192_ = l_Lean_MVarId_tryClearMany(
                                v_fst_1187_,
                                v_a_1172_,
                                v_a_1174_,
                                v_a_1175_,
                                v_a_1176_,
                                v_a_1177_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1192_) == 0 {
                                v_a_1193_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                                crate::leanh::lean_inc(v_a_1193_);
                                crate::leanh::lean_dec_ref_known(v___x_1192_, 1);
                                v___x_1194_ = 1;
                                v___x_1195_ = l_Lean_Meta_introSubstEq(
                                    v_a_1193_,
                                    v___x_1194_,
                                    v_a_1174_,
                                    v_a_1175_,
                                    v_a_1176_,
                                    v_a_1177_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1195_) == 0 {
                                    v_a_1196_ = crate::leanh::lean_ctor_get(v___x_1195_, 0);
                                    crate::leanh::lean_inc(v_a_1196_);
                                    crate::leanh::lean_dec_ref_known(v___x_1195_, 1);
                                    v_fst_1197_ = crate::leanh::lean_ctor_get(v_a_1196_, 0);
                                    crate::leanh::lean_inc(v_fst_1197_);
                                    v_snd_1198_ = crate::leanh::lean_ctor_get(v_a_1196_, 1);
                                    crate::leanh::lean_inc(v_snd_1198_);
                                    crate::leanh::lean_dec(v_a_1196_);
                                    v___x_1199_ = l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0;
                                    v___x_1200_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1200_, 0, v_snd_1198_);
                                    crate::leanh::lean_ctor_set(v___x_1200_, 1, v___x_1199_);
                                    crate::leanh::lean_ctor_set(v___x_1200_, 2, v_fst_1197_);
                                    v___x_1201_ = lean_array_push(v_a_1173_, v___x_1200_);
                                    if v_needHyps_1168_ == 0 {
                                        v___x_1235_ = l_Lean_MVarId_intro1__(
                                            v_snd_1188_,
                                            v_a_1174_,
                                            v_a_1175_,
                                            v_a_1176_,
                                            v_a_1177_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1235_) == 0 {
                                            v_a_1236_ = crate::leanh::lean_ctor_get(v___x_1235_, 0);
                                            crate::leanh::lean_inc(v_a_1236_);
                                            crate::leanh::lean_dec_ref_known(v___x_1235_, 1);
                                            v_fst_1203_ = v_a_1172_;
                                            v_snd_1204_ = v_a_1236_;
                                            v___y_1205_ = v_a_1174_;
                                            v___y_1206_ = v_a_1175_;
                                            v___y_1207_ = v_a_1176_;
                                            v___y_1208_ = v_a_1177_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1201_);
                                            crate::leanh::lean_dec(v_tail_1183_);
                                            crate::leanh::lean_dec_ref(v_a_1172_);
                                            crate::leanh::lean_dec(v_a_1169_);
                                            crate::leanh::lean_dec(v_hNamePrefix_1167_);
                                            crate::leanh::lean_dec(v_fvarId_1166_);
                                            v_a_1237_ = crate::leanh::lean_ctor_get(v___x_1235_, 0);
                                            v_isSharedCheck_1244_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1235_))
                                                    as u8;
                                            if v_isSharedCheck_1244_ == 0 {
                                                v___x_1239_ = v___x_1235_;
                                                v_isShared_1240_ = v_isSharedCheck_1244_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1237_);
                                                crate::leanh::lean_dec(v___x_1235_);
                                                v___x_1239_ = crate::leanh::lean_box(0);
                                                v_isShared_1240_ = v_isSharedCheck_1244_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_1245_ = l_Lean_Meta_intro1Core(
                                            v_snd_1188_,
                                            v___x_1194_,
                                            v_a_1174_,
                                            v_a_1175_,
                                            v_a_1176_,
                                            v_a_1177_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1245_) == 0 {
                                            v_a_1246_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                                            crate::leanh::lean_inc(v_a_1246_);
                                            crate::leanh::lean_dec_ref_known(v___x_1245_, 1);
                                            v_fst_1247_ = crate::leanh::lean_ctor_get(v_a_1246_, 0);
                                            crate::leanh::lean_inc(v_fst_1247_);
                                            v_snd_1248_ = crate::leanh::lean_ctor_get(v_a_1246_, 1);
                                            crate::leanh::lean_inc(v_snd_1248_);
                                            crate::leanh::lean_dec(v_a_1246_);
                                            v___x_1249_ = lean_array_push(v_a_1172_, v_fst_1247_);
                                            v_fst_1203_ = v___x_1249_;
                                            v_snd_1204_ = v_snd_1248_;
                                            v___y_1205_ = v_a_1174_;
                                            v___y_1206_ = v_a_1175_;
                                            v___y_1207_ = v_a_1176_;
                                            v___y_1208_ = v_a_1177_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1201_);
                                            crate::leanh::lean_dec(v_tail_1183_);
                                            crate::leanh::lean_dec_ref(v_a_1172_);
                                            crate::leanh::lean_dec(v_a_1169_);
                                            crate::leanh::lean_dec(v_hNamePrefix_1167_);
                                            crate::leanh::lean_dec(v_fvarId_1166_);
                                            v_a_1250_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                                            v_isSharedCheck_1257_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1245_))
                                                    as u8;
                                            if v_isSharedCheck_1257_ == 0 {
                                                v___x_1252_ = v___x_1245_;
                                                v_isShared_1253_ = v_isSharedCheck_1257_;
                                                state = 8;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1250_);
                                                crate::leanh::lean_dec(v___x_1245_);
                                                v___x_1252_ = crate::leanh::lean_box(0);
                                                v_isShared_1253_ = v_isSharedCheck_1257_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_snd_1188_);
                                    crate::leanh::lean_dec(v_tail_1183_);
                                    crate::leanh::lean_dec_ref(v_a_1173_);
                                    crate::leanh::lean_dec_ref(v_a_1172_);
                                    crate::leanh::lean_dec(v_a_1169_);
                                    crate::leanh::lean_dec(v_hNamePrefix_1167_);
                                    crate::leanh::lean_dec(v_fvarId_1166_);
                                    v_a_1258_ = crate::leanh::lean_ctor_get(v___x_1195_, 0);
                                    v_isSharedCheck_1265_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1195_)) as u8;
                                    if v_isSharedCheck_1265_ == 0 {
                                        v___x_1260_ = v___x_1195_;
                                        v_isShared_1261_ = v_isSharedCheck_1265_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1258_);
                                        crate::leanh::lean_dec(v___x_1195_);
                                        v___x_1260_ = crate::leanh::lean_box(0);
                                        v_isShared_1261_ = v_isSharedCheck_1265_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_1188_);
                                crate::leanh::lean_dec(v_tail_1183_);
                                crate::leanh::lean_dec_ref(v_a_1173_);
                                crate::leanh::lean_dec_ref(v_a_1172_);
                                crate::leanh::lean_dec(v_a_1169_);
                                crate::leanh::lean_dec(v_hNamePrefix_1167_);
                                crate::leanh::lean_dec(v_fvarId_1166_);
                                v_a_1266_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                                v_isSharedCheck_1273_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1192_)) as u8;
                                if v_isSharedCheck_1273_ == 0 {
                                    v___x_1268_ = v___x_1192_;
                                    v_isShared_1269_ = v_isSharedCheck_1273_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1266_);
                                    crate::leanh::lean_dec(v___x_1192_);
                                    v___x_1268_ = crate::leanh::lean_box(0);
                                    v_isShared_1269_ = v_isSharedCheck_1273_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_1188_);
                            crate::leanh::lean_dec(v_fst_1187_);
                            crate::leanh::lean_dec(v_tail_1183_);
                            crate::leanh::lean_dec_ref(v_a_1173_);
                            crate::leanh::lean_dec_ref(v_a_1172_);
                            crate::leanh::lean_dec(v_a_1169_);
                            crate::leanh::lean_dec(v_hNamePrefix_1167_);
                            crate::leanh::lean_dec(v_fvarId_1166_);
                            v_a_1274_ = crate::leanh::lean_ctor_get(v___x_1191_, 0);
                            v_isSharedCheck_1281_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1191_)) as u8;
                            if v_isSharedCheck_1281_ == 0 {
                                v___x_1276_ = v___x_1191_;
                                v_isShared_1277_ = v_isSharedCheck_1281_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1274_);
                                crate::leanh::lean_dec(v___x_1191_);
                                v___x_1276_ = crate::leanh::lean_box(0);
                                v_isShared_1277_ = v_isSharedCheck_1281_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_1183_);
                        crate::leanh::lean_dec_ref(v_a_1173_);
                        crate::leanh::lean_dec_ref(v_a_1172_);
                        crate::leanh::lean_dec(v_a_1169_);
                        crate::leanh::lean_dec(v_hNamePrefix_1167_);
                        crate::leanh::lean_dec(v_fvarId_1166_);
                        v_a_1282_ = crate::leanh::lean_ctor_get(v___x_1185_, 0);
                        v_isSharedCheck_1289_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1185_)) as u8;
                        if v_isSharedCheck_1289_ == 0 {
                            v___x_1284_ = v___x_1185_;
                            v_isShared_1285_ = v_isSharedCheck_1289_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1282_);
                            crate::leanh::lean_dec(v___x_1185_);
                            v___x_1284_ = crate::leanh::lean_box(0);
                            v_isShared_1285_ = v_isSharedCheck_1289_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_tail_1183_) == 0 {
                    crate::leanh::lean_dec(v_hNamePrefix_1167_);
                    crate::leanh::lean_dec(v_fvarId_1166_);
                    v___x_1209_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1210_ = lean_nat_add(v_a_1169_, v___x_1209_);
                    crate::leanh::lean_dec(v_a_1169_);
                    v___x_1211_ = lean_name_append_index_after(v___x_1189_, v___x_1210_);
                    crate::leanh::lean_inc(v_snd_1204_);
                    v___x_1212_ = l_Lean_Meta_appendTagSuffix(
                        v_snd_1204_,
                        v___x_1211_,
                        v___y_1205_,
                        v___y_1206_,
                        v___y_1207_,
                        v___y_1208_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1212_) == 0 {
                        v_isSharedCheck_1222_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1212_)) as u8;
                        if v_isSharedCheck_1222_ == 0 {
                            v_unused_1223_ = crate::leanh::lean_ctor_get(v___x_1212_, 0);
                            crate::leanh::lean_dec(v_unused_1223_);
                            v___x_1214_ = v___x_1212_;
                            v_isShared_1215_ = v_isSharedCheck_1222_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1212_);
                            v___x_1214_ = crate::leanh::lean_box(0);
                            v_isShared_1215_ = v_isSharedCheck_1222_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1204_);
                        crate::leanh::lean_dec_ref(v_fst_1203_);
                        crate::leanh::lean_dec_ref(v___x_1201_);
                        v_a_1224_ = crate::leanh::lean_ctor_get(v___x_1212_, 0);
                        v_isSharedCheck_1231_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1212_)) as u8;
                        if v_isSharedCheck_1231_ == 0 {
                            v___x_1226_ = v___x_1212_;
                            v_isShared_1227_ = v_isSharedCheck_1231_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1224_);
                            crate::leanh::lean_dec(v___x_1212_);
                            v___x_1226_ = crate::leanh::lean_box(0);
                            v_isShared_1227_ = v_isSharedCheck_1231_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_1232_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1233_ = lean_nat_add(v_a_1169_, v___x_1232_);
                    crate::leanh::lean_dec(v_a_1169_);
                    v_a_1169_ = v___x_1233_;
                    v_a_1170_ = v_snd_1204_;
                    v_a_1171_ = v_tail_1183_;
                    v_a_1172_ = v_fst_1203_;
                    v_a_1173_ = v___x_1201_;
                    v_a_1174_ = v___y_1205_;
                    v_a_1175_ = v___y_1206_;
                    v_a_1176_ = v___y_1207_;
                    v_a_1177_ = v___y_1208_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1216_ = crate::leanh::lean_box(0);
                v___x_1217_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1217_, 0, v_snd_1204_);
                crate::leanh::lean_ctor_set(v___x_1217_, 1, v_fst_1203_);
                crate::leanh::lean_ctor_set(v___x_1217_, 2, v___x_1216_);
                v___x_1218_ = lean_array_push(v___x_1201_, v___x_1217_);
                if v_isShared_1215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1214_, 0, v___x_1218_);
                    v___x_1220_ = v___x_1214_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
                    v___x_1220_ = v_reuseFailAlloc_1221_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1220_;
            }
            4 => {
                if v_isShared_1227_ == 0 {
                    v___x_1229_ = v___x_1226_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
                    v___x_1229_ = v_reuseFailAlloc_1230_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1229_;
            }
            6 => {
                if v_isShared_1240_ == 0 {
                    v___x_1242_ = v___x_1239_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
                    v___x_1242_ = v_reuseFailAlloc_1243_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1242_;
            }
            8 => {
                if v_isShared_1253_ == 0 {
                    v___x_1255_ = v___x_1252_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
                    v___x_1255_ = v_reuseFailAlloc_1256_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1255_;
            }
            10 => {
                if v_isShared_1261_ == 0 {
                    v___x_1263_ = v___x_1260_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
                    v___x_1263_ = v_reuseFailAlloc_1264_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1263_;
            }
            12 => {
                if v_isShared_1269_ == 0 {
                    v___x_1271_ = v___x_1268_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
                    v___x_1271_ = v_reuseFailAlloc_1272_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1271_;
            }
            14 => {
                if v_isShared_1277_ == 0 {
                    v___x_1279_ = v___x_1276_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
                    v___x_1279_ = v_reuseFailAlloc_1280_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1279_;
            }
            16 => {
                if v_isShared_1285_ == 0 {
                    v___x_1287_ = v___x_1284_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
                    v___x_1287_ = v_reuseFailAlloc_1288_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___boxed(
    mut v_fvarId_1290_: *mut crate::leanh::LeanObject,
    mut v_hNamePrefix_1291_: *mut crate::leanh::LeanObject,
    mut v_needHyps_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_needHyps_boxed_1303_: u8 = 0;
    let mut v_res_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_needHyps_boxed_1303_ = (crate::leanh::lean_unbox(v_needHyps_1292_) as u8);
    v_res_1304_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(
        v_fvarId_1290_,
        v_hNamePrefix_1291_,
        v_needHyps_boxed_1303_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        v_a_1298_,
        v_a_1299_,
        v_a_1300_,
        v_a_1301_,
    );
    crate::leanh::lean_dec(v_a_1301_);
    crate::leanh::lean_dec_ref(v_a_1300_);
    crate::leanh::lean_dec(v_a_1299_);
    crate::leanh::lean_dec_ref(v_a_1298_);
    return v_res_1304_;
}
pub unsafe fn l_Lean_Meta_caseValues(
    mut v_mvarId_1305_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1306_: *mut crate::leanh::LeanObject,
    mut v_values_1307_: *mut crate::leanh::LeanObject,
    mut v_hNamePrefix_1308_: *mut crate::leanh::LeanObject,
    mut v_needHyps_1309_: u8,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_a_1312_: *mut crate::leanh::LeanObject,
    mut v_a_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1316_ = lean_array_to_list(v_values_1307_);
    v___x_1317_ = l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0;
    v___x_1318_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(
        v_fvarId_1306_,
        v_hNamePrefix_1308_,
        v_needHyps_1309_,
        v___x_1315_,
        v_mvarId_1305_,
        v___x_1316_,
        v___x_1317_,
        v___x_1317_,
        v_a_1310_,
        v_a_1311_,
        v_a_1312_,
        v_a_1313_,
    );
    return v___x_1318_;
}
pub unsafe fn l_Lean_Meta_caseValues___boxed(
    mut v_mvarId_1319_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1320_: *mut crate::leanh::LeanObject,
    mut v_values_1321_: *mut crate::leanh::LeanObject,
    mut v_hNamePrefix_1322_: *mut crate::leanh::LeanObject,
    mut v_needHyps_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_needHyps_boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_needHyps_boxed_1329_ = (crate::leanh::lean_unbox(v_needHyps_1323_) as u8);
    v_res_1330_ = l_Lean_Meta_caseValues(
        v_mvarId_1319_,
        v_fvarId_1320_,
        v_values_1321_,
        v_hNamePrefix_1322_,
        v_needHyps_boxed_1329_,
        v_a_1324_,
        v_a_1325_,
        v_a_1326_,
        v_a_1327_,
    );
    crate::leanh::lean_dec(v_a_1327_);
    crate::leanh::lean_dec_ref(v_a_1326_);
    crate::leanh::lean_dec(v_a_1325_);
    crate::leanh::lean_dec_ref(v_a_1324_);
    return v_res_1330_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_CaseValues(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_CaseValues(
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
pub unsafe fn initialize_Lean_Meta_Match_CaseValues(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Subst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_CaseValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_CaseValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_CaseValues(builtin);
}
