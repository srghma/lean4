// Lean compiler output
// Module: Lean.Meta.Match.Basic
// Imports: Lean.Meta.Tactic.FVarSubst Lean.Meta.CollectFVars Lean.Meta.Match.Value Lean.Meta.AppBuilder Lean.Meta.Match.NamedPatterns
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_infer_type, lean_mk_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_memcmp, lean_string_utf8_byte_size, lean_usize_add,
    lean_usize_dec_lt, lean_whnf,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_isNat;
use crate::r#gen::Init::Prelude::l_Array_extract___redArg;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_const___override,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_hasExprMVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar,
    l_Lean_Expr_replaceFVarId, l_Lean_Expr_sort___override, l_Lean_inaccessible_x3f,
    l_Lean_instBEqFVarId_beq, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkInaccessible,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_replaceFVarId, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_joinSep, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkArrayLit,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
};
use crate::r#gen::Lean::Meta::CollectFVars::{
    initialize_Lean_Meta_CollectFVars, l_Lean_Expr_collectFVars, l_Lean_LocalDecl_collectFVars,
    runtime_initialize_Lean_Meta_CollectFVars,
};
use crate::r#gen::Lean::Meta::Match::NamedPatterns::{
    initialize_Lean_Meta_Match_NamedPatterns, l_Lean_Meta_Match_isNamedPattern_x3f,
    l_Lean_Meta_Match_mkNamedPattern, runtime_initialize_Lean_Meta_Match_NamedPatterns,
};
use crate::r#gen::Lean::Meta::Match::Value::{
    initialize_Lean_Meta_Match_Value, l_Lean_Meta_isMatchValue,
    runtime_initialize_Lean_Meta_Match_Value,
};
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, l_Lean_LocalDecl_applyFVarSubst,
    l_Lean_Meta_FVarSubst_apply, l_Lean_Meta_FVarSubst_find_x3f, l_Lean_Meta_FVarSubst_get,
    l_Lean_Meta_FVarSubst_insert, runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::CollectFVars::l_Lean_CollectFVars_State_add;
use crate::r#gen::Lean::Util::Recognizers::l_Lean_Expr_arrayLit_x3f;
pub static l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instInhabitedPattern_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedPattern_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedPattern: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__0_value:
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
    m_data: [46, 40, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1_value
) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__7_value:
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
    m_data: [35, 91, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value:
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
    m_data: [44, 32, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__12_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__14_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [64, 0],
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltLHS_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltLHS: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_instInhabitedAlt_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Match_instInhabitedAlt_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedAlt_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedAlt_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedAlt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [10, 32, 32, 124, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 137, 139, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 40, 0]};
static mut l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0_value
) as *mut leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__0_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [124, 45, 32, 0],
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__2_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 61, 62, 32, 0],
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__4_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__6_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Example_toMessageData___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [95, 0],
};
static mut l_Lean_Meta_Match_Example_toMessageData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_Example_toMessageData___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_Example_toMessageData___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Example_toMessageData___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Example_toMessageData___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Example_toMessageData___closed__3_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_Lean_Meta_Match_Example_toMessageData___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_Example_toMessageData___closed__4_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_Example_toMessageData___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Example_toMessageData___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Example_toMessageData___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instInhabitedProblem_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedProblem_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedProblem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        114, 101, 109, 97, 105, 110, 105, 110, 103, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115,
        58, 32, 0,
    ],
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        10, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 58, 0,
    ],
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [10, 101, 120, 97, 109, 112, 108, 101, 115, 58, 0],
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_toPattern___closed__0_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 112, 97, 116, 116, 101, 114, 110, 0,
        ],
    };
static mut l_Lean_Meta_Match_toPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_toPattern___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_toPattern___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_toPattern___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_toPattern___closed__2_value: leanh::LeanStringObject<62> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 99, 99, 117, 114, 114, 101,
            110, 99, 101, 32, 111, 102, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100,
            101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 110, 97, 109, 101, 100, 80, 97,
            116, 116, 101, 114, 110, 39, 0,
        ],
    };
static mut l_Lean_Meta_Match_toPattern___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_toPattern___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_toPattern___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_toPattern___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_toPattern___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_toPattern___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 110, 103, 114, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_congrEqnThmSuffixBase: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [99, 111, 110, 103, 114, 95, 101, 113, 95, 0],
};
static mut l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 111, 110, 103, 114, 95, 101, 113, 95, 49, 0],
};
static mut l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Match_congrEqn1ThmSuffix: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorIdx(
    mut v_x_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2475_) {
        0 => {
            let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2476_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2476_;
        }
        1 => {
            let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2477_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2477_;
        }
        2 => {
            let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2478_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2478_;
        }
        3 => {
            let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2479_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2479_;
        }
        4 => {
            let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2480_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2480_;
        }
        _ => {
            let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2481_ = leanh::lean_unsigned_to_nat(5);
            return v___x_2481_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorIdx___boxed(
    mut v_x_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l_Lean_Meta_Match_Pattern_ctorIdx(v_x_2482_);
    leanh::lean_dec_ref(v_x_2482_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorElim___redArg(
    mut v_t_2484_: *mut leanh::LeanObject,
    mut v_k_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2484_) {
        1 => {
            let mut v_fvarId_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_2486_ = leanh::lean_ctor_get(v_t_2484_, 0);
            leanh::lean_inc(v_fvarId_2486_);
            leanh::lean_dec_ref_known(v_t_2484_, 1);
            v___x_2487_ = leanh::lean_apply_1(v_k_2485_, v_fvarId_2486_);
            return v___x_2487_;
        }
        2 => {
            let mut v_ctorName_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_params_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fields_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ctorName_2488_ = leanh::lean_ctor_get(v_t_2484_, 0);
            leanh::lean_inc(v_ctorName_2488_);
            v_us_2489_ = leanh::lean_ctor_get(v_t_2484_, 1);
            leanh::lean_inc(v_us_2489_);
            v_params_2490_ = leanh::lean_ctor_get(v_t_2484_, 2);
            leanh::lean_inc(v_params_2490_);
            v_fields_2491_ = leanh::lean_ctor_get(v_t_2484_, 3);
            leanh::lean_inc(v_fields_2491_);
            leanh::lean_dec_ref_known(v_t_2484_, 4);
            v___x_2492_ = leanh::lean_apply_4(
                v_k_2485_,
                v_ctorName_2488_,
                v_us_2489_,
                v_params_2490_,
                v_fields_2491_,
            );
            return v___x_2492_;
        }
        4 => {
            let mut v_type_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_xs_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_type_2493_ = leanh::lean_ctor_get(v_t_2484_, 0);
            leanh::lean_inc_ref(v_type_2493_);
            v_xs_2494_ = leanh::lean_ctor_get(v_t_2484_, 1);
            leanh::lean_inc(v_xs_2494_);
            leanh::lean_dec_ref_known(v_t_2484_, 2);
            v___x_2495_ = leanh::lean_apply_2(v_k_2485_, v_type_2493_, v_xs_2494_);
            return v___x_2495_;
        }
        5 => {
            let mut v_varId_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hId_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_varId_2496_ = leanh::lean_ctor_get(v_t_2484_, 0);
            leanh::lean_inc(v_varId_2496_);
            v_p_2497_ = leanh::lean_ctor_get(v_t_2484_, 1);
            leanh::lean_inc_ref(v_p_2497_);
            v_hId_2498_ = leanh::lean_ctor_get(v_t_2484_, 2);
            leanh::lean_inc(v_hId_2498_);
            leanh::lean_dec_ref_known(v_t_2484_, 3);
            v___x_2499_ =
                leanh::lean_apply_3(v_k_2485_, v_varId_2496_, v_p_2497_, v_hId_2498_);
            return v___x_2499_;
        }
        _ => {
            let mut v_e_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_2500_ = leanh::lean_ctor_get(v_t_2484_, 0);
            leanh::lean_inc_ref(v_e_2500_);
            leanh::lean_dec_ref(v_t_2484_);
            v___x_2501_ = leanh::lean_apply_1(v_k_2485_, v_e_2500_);
            return v___x_2501_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorElim(
    mut v_motive__1_2502_: *mut leanh::LeanObject,
    mut v_ctorIdx_2503_: *mut leanh::LeanObject,
    mut v_t_2504_: *mut leanh::LeanObject,
    mut v_h_2505_: *mut leanh::LeanObject,
    mut v_k_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2504_, v_k_2506_);
    return v___x_2507_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorElim___boxed(
    mut v_motive__1_2508_: *mut leanh::LeanObject,
    mut v_ctorIdx_2509_: *mut leanh::LeanObject,
    mut v_t_2510_: *mut leanh::LeanObject,
    mut v_h_2511_: *mut leanh::LeanObject,
    mut v_k_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Lean_Meta_Match_Pattern_ctorElim(
        v_motive__1_2508_,
        v_ctorIdx_2509_,
        v_t_2510_,
        v_h_2511_,
        v_k_2512_,
    );
    leanh::lean_dec(v_ctorIdx_2509_);
    return v_res_2513_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(
    mut v_t_2514_: *mut leanh::LeanObject,
    mut v_inaccessible_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2514_, v_inaccessible_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_inaccessible_elim(
    mut v_motive__1_2517_: *mut leanh::LeanObject,
    mut v_t_2518_: *mut leanh::LeanObject,
    mut v_h_2519_: *mut leanh::LeanObject,
    mut v_inaccessible_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2518_, v_inaccessible_2520_);
    return v___x_2521_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_var_elim___redArg(
    mut v_t_2522_: *mut leanh::LeanObject,
    mut v_var_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2522_, v_var_2523_);
    return v___x_2524_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_var_elim(
    mut v_motive__1_2525_: *mut leanh::LeanObject,
    mut v_t_2526_: *mut leanh::LeanObject,
    mut v_h_2527_: *mut leanh::LeanObject,
    mut v_var_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2526_, v_var_2528_);
    return v___x_2529_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctor_elim___redArg(
    mut v_t_2530_: *mut leanh::LeanObject,
    mut v_ctor_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2530_, v_ctor_2531_);
    return v___x_2532_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctor_elim(
    mut v_motive__1_2533_: *mut leanh::LeanObject,
    mut v_t_2534_: *mut leanh::LeanObject,
    mut v_h_2535_: *mut leanh::LeanObject,
    mut v_ctor_2536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2534_, v_ctor_2536_);
    return v___x_2537_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_val_elim___redArg(
    mut v_t_2538_: *mut leanh::LeanObject,
    mut v_val_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2538_, v_val_2539_);
    return v___x_2540_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_val_elim(
    mut v_motive__1_2541_: *mut leanh::LeanObject,
    mut v_t_2542_: *mut leanh::LeanObject,
    mut v_h_2543_: *mut leanh::LeanObject,
    mut v_val_2544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2545_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2542_, v_val_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(
    mut v_t_2546_: *mut leanh::LeanObject,
    mut v_arrayLit_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2548_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2546_, v_arrayLit_2547_);
    return v___x_2548_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_arrayLit_elim(
    mut v_motive__1_2549_: *mut leanh::LeanObject,
    mut v_t_2550_: *mut leanh::LeanObject,
    mut v_h_2551_: *mut leanh::LeanObject,
    mut v_arrayLit_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2550_, v_arrayLit_2552_);
    return v___x_2553_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_as_elim___redArg(
    mut v_t_2554_: *mut leanh::LeanObject,
    mut v_as_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2556_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2554_, v_as_2555_);
    return v___x_2556_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_as_elim(
    mut v_motive__1_2557_: *mut leanh::LeanObject,
    mut v_t_2558_: *mut leanh::LeanObject,
    mut v_h_2559_: *mut leanh::LeanObject,
    mut v_as_2560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2561_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2558_, v_as_2560_);
    return v___x_2561_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2565_ = leanh::lean_box(0);
    v___x_2566_ = l_Lean_Meta_Match_instInhabitedPattern_default___closed__1;
    v___x_2567_ = l_Lean_Expr_const___override(v___x_2566_, v___x_2565_);
    return v___x_2567_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2568_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once),
        _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2,
    );
    v___x_2569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2569_, 0, v___x_2568_);
    return v___x_2569_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern_default() -> *mut leanh::LeanObject
{
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once),
        _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3,
    );
    return v___x_2570_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern() -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2571_ = l_Lean_Meta_Match_instInhabitedPattern_default;
    return v___x_2571_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__0;
    v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
    return v___x_2574_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__2;
    v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
    return v___x_2577_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2579_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
    v___x_2580_ = l_Lean_stringToMessageData(v___x_2579_);
    return v___x_2580_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2581_ = leanh::lean_box(0);
    v___x_2582_ = l_Lean_MessageData_ofFormat(v___x_2581_);
    return v___x_2582_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1;
    v___x_2587_ = l_Lean_MessageData_ofFormat(v___x_2586_);
    return v___x_2587_;
}
pub unsafe fn l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(
    mut v_x_2588_: *mut leanh::LeanObject,
    mut v_x_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2589_) == 0 {
                    return v_x_2588_;
                } else {
                    v_head_2590_ = leanh::lean_ctor_get(v_x_2589_, 0);
                    v_tail_2591_ = leanh::lean_ctor_get(v_x_2589_, 1);
                    v_isSharedCheck_2602_ = (!leanh::lean_is_exclusive(v_x_2589_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2593_ = v_x_2589_;
                        v_isShared_2594_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2591_);
                        leanh::lean_inc(v_head_2590_);
                        leanh::lean_dec(v_x_2589_);
                        v___x_2593_ = leanh::lean_box(0);
                        v_isShared_2594_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once), _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2);
                if v_isShared_2594_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2593_, 7);
                    leanh::lean_ctor_set(v___x_2593_, 1, v___x_2595_);
                    leanh::lean_ctor_set(v___x_2593_, 0, v_x_2588_);
                    v___x_2597_ = v___x_2593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_x_2588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2595_);
                    v___x_2597_ = v_reuseFailAlloc_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2598_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_2590_);
                v___x_2599_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2599_, 0, v___x_2597_);
                leanh::lean_ctor_set(v___x_2599_, 1, v___x_2598_);
                v_x_2588_ = v___x_2599_;
                v_x_2589_ = v_tail_2591_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__7;
    v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
    return v___x_2605_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__10;
    v___x_2610_ = l_Lean_MessageData_ofFormat(v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__12;
    v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2615_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
    v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
    return v___x_2616_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_toMessageData(
    mut v_x_2617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_unused_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varId_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2617_) {
                0 => {
                    v_e_2618_ = leanh::lean_ctor_get(v_x_2617_, 0);
                    leanh::lean_inc_ref(v_e_2618_);
                    leanh::lean_dec_ref_known(v_x_2617_, 1);
                    v___x_2619_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1,
                    );
                    v___x_2620_ = l_Lean_MessageData_ofExpr(v_e_2618_);
                    v___x_2621_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2621_, 0, v___x_2619_);
                    leanh::lean_ctor_set(v___x_2621_, 1, v___x_2620_);
                    v___x_2622_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                    );
                    v___x_2623_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2623_, 0, v___x_2621_);
                    leanh::lean_ctor_set(v___x_2623_, 1, v___x_2622_);
                    return v___x_2623_;
                }
                1 => {
                    v_fvarId_2624_ = leanh::lean_ctor_get(v_x_2617_, 0);
                    leanh::lean_inc(v_fvarId_2624_);
                    leanh::lean_dec_ref_known(v_x_2617_, 1);
                    v___x_2625_ = l_Lean_mkFVar(v_fvarId_2624_);
                    v___x_2626_ = l_Lean_MessageData_ofExpr(v___x_2625_);
                    return v___x_2626_;
                }
                2 => {
                    v_fields_2627_ = leanh::lean_ctor_get(v_x_2617_, 3);
                    if leanh::lean_obj_tag(v_fields_2627_) == 0 {
                        v_ctorName_2628_ = leanh::lean_ctor_get(v_x_2617_, 0);
                        leanh::lean_inc(v_ctorName_2628_);
                        leanh::lean_dec_ref_known(v_x_2617_, 4);
                        v___x_2629_ = l_Lean_MessageData_ofName(v_ctorName_2628_);
                        return v___x_2629_;
                    } else {
                        leanh::lean_inc(v_fields_2627_);
                        v_ctorName_2630_ = leanh::lean_ctor_get(v_x_2617_, 0);
                        leanh::lean_inc(v_ctorName_2630_);
                        leanh::lean_dec_ref_known(v_x_2617_, 4);
                        v___x_2631_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once
                            ),
                            _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5,
                        );
                        v___x_2632_ = l_Lean_MessageData_ofName(v_ctorName_2630_);
                        v___x_2633_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2633_, 0, v___x_2631_);
                        leanh::lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                        v___x_2634_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once
                            ),
                            _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6,
                        );
                        v___x_2635_ =
                            l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(
                                v___x_2634_,
                                v_fields_2627_,
                            );
                        v___x_2636_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2636_, 0, v___x_2633_);
                        leanh::lean_ctor_set(v___x_2636_, 1, v___x_2635_);
                        v___x_2637_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                            ),
                            _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                        );
                        v___x_2638_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2638_, 0, v___x_2636_);
                        leanh::lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                        return v___x_2638_;
                    }
                }
                3 => {
                    v_e_2639_ = leanh::lean_ctor_get(v_x_2617_, 0);
                    leanh::lean_inc_ref(v_e_2639_);
                    leanh::lean_dec_ref_known(v_x_2617_, 1);
                    v___x_2640_ = l_Lean_MessageData_ofExpr(v_e_2639_);
                    return v___x_2640_;
                }
                4 => {
                    v_xs_2641_ = leanh::lean_ctor_get(v_x_2617_, 1);
                    v_isSharedCheck_2655_ = (!leanh::lean_is_exclusive(v_x_2617_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v_unused_2656_ = leanh::lean_ctor_get(v_x_2617_, 0);
                        leanh::lean_dec(v_unused_2656_);
                        v___x_2643_ = v_x_2617_;
                        v_isShared_2644_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_2641_);
                        leanh::lean_dec(v_x_2617_);
                        v___x_2643_ = leanh::lean_box(0);
                        v_isShared_2644_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_varId_2657_ = leanh::lean_ctor_get(v_x_2617_, 0);
                    leanh::lean_inc(v_varId_2657_);
                    v_p_2658_ = leanh::lean_ctor_get(v_x_2617_, 1);
                    leanh::lean_inc_ref(v_p_2658_);
                    leanh::lean_dec_ref_known(v_x_2617_, 3);
                    v___x_2659_ = l_Lean_mkFVar(v_varId_2657_);
                    v___x_2660_ = l_Lean_MessageData_ofExpr(v___x_2659_);
                    v___x_2661_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15,
                    );
                    v___x_2662_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2662_, 0, v___x_2660_);
                    leanh::lean_ctor_set(v___x_2662_, 1, v___x_2661_);
                    v___x_2663_ = l_Lean_Meta_Match_Pattern_toMessageData(v_p_2658_);
                    v___x_2664_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2664_, 0, v___x_2662_);
                    leanh::lean_ctor_set(v___x_2664_, 1, v___x_2663_);
                    return v___x_2664_;
                }
            },
            1 => {
                v___x_2645_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8,
                );
                v___x_2646_ = leanh::lean_box(0);
                v___x_2647_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(
                        v_xs_2641_,
                        v___x_2646_,
                    );
                v___x_2648_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11,
                );
                v___x_2649_ = l_Lean_MessageData_joinSep(v___x_2647_, v___x_2648_);
                if v_isShared_2644_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2643_, 7);
                    leanh::lean_ctor_set(v___x_2643_, 1, v___x_2649_);
                    leanh::lean_ctor_set(v___x_2643_, 0, v___x_2645_);
                    v___x_2651_ = v___x_2643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2649_);
                    v___x_2651_ = v_reuseFailAlloc_2654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2652_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13,
                );
                v___x_2653_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2653_, 0, v___x_2651_);
                leanh::lean_ctor_set(v___x_2653_, 1, v___x_2652_);
                return v___x_2653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(
    mut v_a_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2665_) == 0 {
                    v___x_2667_ = l_List_reverse___redArg(v_a_2666_);
                    return v___x_2667_;
                } else {
                    v_head_2668_ = leanh::lean_ctor_get(v_a_2665_, 0);
                    v_tail_2669_ = leanh::lean_ctor_get(v_a_2665_, 1);
                    v_isSharedCheck_2678_ = (!leanh::lean_is_exclusive(v_a_2665_)) as u8;
                    if v_isSharedCheck_2678_ == 0 {
                        v___x_2671_ = v_a_2665_;
                        v_isShared_2672_ = v_isSharedCheck_2678_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2669_);
                        leanh::lean_inc(v_head_2668_);
                        leanh::lean_dec(v_a_2665_);
                        v___x_2671_ = leanh::lean_box(0);
                        v_isShared_2672_ = v_isSharedCheck_2678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2673_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_2668_);
                if v_isShared_2672_ == 0 {
                    leanh::lean_ctor_set(v___x_2671_, 1, v_a_2666_);
                    leanh::lean_ctor_set(v___x_2671_, 0, v___x_2673_);
                    v___x_2675_ = v___x_2671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2666_);
                    v___x_2675_ = v_reuseFailAlloc_2677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2665_ = v_tail_2669_;
                v_a_2666_ = v___x_2675_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
    mut v_annotate_2679_: u8,
    mut v_p_2680_: *mut leanh::LeanObject,
    mut v_a_2681_: *mut leanh::LeanObject,
    mut v_a_2682_: *mut leanh::LeanObject,
    mut v_a_2683_: *mut leanh::LeanObject,
    mut v_a_2684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_e_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_fvarId_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v_ctorName_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_a_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_e_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_type_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_p_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varId_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hId_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_p_2680_) {
                0 => {
                    if v_annotate_2679_ == 0 {
                        v_e_2686_ = leanh::lean_ctor_get(v_p_2680_, 0);
                        v_isSharedCheck_2693_ = (!leanh::lean_is_exclusive(v_p_2680_)) as u8;
                        if v_isSharedCheck_2693_ == 0 {
                            v___x_2688_ = v_p_2680_;
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_e_2686_);
                            leanh::lean_dec(v_p_2680_);
                            v___x_2688_ = leanh::lean_box(0);
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_e_2694_ = leanh::lean_ctor_get(v_p_2680_, 0);
                        v_isSharedCheck_2702_ = (!leanh::lean_is_exclusive(v_p_2680_)) as u8;
                        if v_isSharedCheck_2702_ == 0 {
                            v___x_2696_ = v_p_2680_;
                            v_isShared_2697_ = v_isSharedCheck_2702_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_e_2694_);
                            leanh::lean_dec(v_p_2680_);
                            v___x_2696_ = leanh::lean_box(0);
                            v_isShared_2697_ = v_isSharedCheck_2702_;
                            state = 3;
                            continue;
                        }
                    }
                }
                1 => {
                    v_fvarId_2703_ = leanh::lean_ctor_get(v_p_2680_, 0);
                    v_isSharedCheck_2711_ = (!leanh::lean_is_exclusive(v_p_2680_)) as u8;
                    if v_isSharedCheck_2711_ == 0 {
                        v___x_2705_ = v_p_2680_;
                        v_isShared_2706_ = v_isSharedCheck_2711_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_2703_);
                        leanh::lean_dec(v_p_2680_);
                        v___x_2705_ = leanh::lean_box(0);
                        v_isShared_2706_ = v_isSharedCheck_2711_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_ctorName_2712_ = leanh::lean_ctor_get(v_p_2680_, 0);
                    leanh::lean_inc(v_ctorName_2712_);
                    v_us_2713_ = leanh::lean_ctor_get(v_p_2680_, 1);
                    leanh::lean_inc(v_us_2713_);
                    v_params_2714_ = leanh::lean_ctor_get(v_p_2680_, 2);
                    leanh::lean_inc(v_params_2714_);
                    v_fields_2715_ = leanh::lean_ctor_get(v_p_2680_, 3);
                    leanh::lean_inc(v_fields_2715_);
                    leanh::lean_dec_ref_known(v_p_2680_, 4);
                    v___x_2716_ = leanh::lean_box(0);
                    v___x_2717_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_2679_, v_fields_2715_, v___x_2716_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
                    if leanh::lean_obj_tag(v___x_2717_) == 0 {
                        v_a_2718_ = leanh::lean_ctor_get(v___x_2717_, 0);
                        v_isSharedCheck_2729_ =
                            (!leanh::lean_is_exclusive(v___x_2717_)) as u8;
                        if v_isSharedCheck_2729_ == 0 {
                            v___x_2720_ = v___x_2717_;
                            v_isShared_2721_ = v_isSharedCheck_2729_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2718_);
                            leanh::lean_dec(v___x_2717_);
                            v___x_2720_ = leanh::lean_box(0);
                            v_isShared_2721_ = v_isSharedCheck_2729_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_params_2714_);
                        leanh::lean_dec(v_us_2713_);
                        leanh::lean_dec(v_ctorName_2712_);
                        v_a_2730_ = leanh::lean_ctor_get(v___x_2717_, 0);
                        v_isSharedCheck_2737_ =
                            (!leanh::lean_is_exclusive(v___x_2717_)) as u8;
                        if v_isSharedCheck_2737_ == 0 {
                            v___x_2732_ = v___x_2717_;
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2730_);
                            leanh::lean_dec(v___x_2717_);
                            v___x_2732_ = leanh::lean_box(0);
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 9;
                            continue;
                        }
                    }
                }
                3 => {
                    v_e_2738_ = leanh::lean_ctor_get(v_p_2680_, 0);
                    v_isSharedCheck_2745_ = (!leanh::lean_is_exclusive(v_p_2680_)) as u8;
                    if v_isSharedCheck_2745_ == 0 {
                        v___x_2740_ = v_p_2680_;
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_e_2738_);
                        leanh::lean_dec(v_p_2680_);
                        v___x_2740_ = leanh::lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 11;
                        continue;
                    }
                }
                4 => {
                    v_type_2746_ = leanh::lean_ctor_get(v_p_2680_, 0);
                    leanh::lean_inc_ref(v_type_2746_);
                    v_xs_2747_ = leanh::lean_ctor_get(v_p_2680_, 1);
                    leanh::lean_inc(v_xs_2747_);
                    leanh::lean_dec_ref_known(v_p_2680_, 2);
                    v___x_2748_ = leanh::lean_box(0);
                    v___x_2749_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_2679_, v_xs_2747_, v___x_2748_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
                    if leanh::lean_obj_tag(v___x_2749_) == 0 {
                        v_a_2750_ = leanh::lean_ctor_get(v___x_2749_, 0);
                        leanh::lean_inc(v_a_2750_);
                        leanh::lean_dec_ref_known(v___x_2749_, 1);
                        v___x_2751_ = l_Lean_Meta_mkArrayLit(
                            v_type_2746_,
                            v_a_2750_,
                            v_a_2681_,
                            v_a_2682_,
                            v_a_2683_,
                            v_a_2684_,
                        );
                        return v___x_2751_;
                    } else {
                        leanh::lean_dec_ref(v_type_2746_);
                        v_a_2752_ = leanh::lean_ctor_get(v___x_2749_, 0);
                        v_isSharedCheck_2759_ =
                            (!leanh::lean_is_exclusive(v___x_2749_)) as u8;
                        if v_isSharedCheck_2759_ == 0 {
                            v___x_2754_ = v___x_2749_;
                            v_isShared_2755_ = v_isSharedCheck_2759_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2752_);
                            leanh::lean_dec(v___x_2749_);
                            v___x_2754_ = leanh::lean_box(0);
                            v_isShared_2755_ = v_isSharedCheck_2759_;
                            state = 13;
                            continue;
                        }
                    }
                }
                _ => {
                    if v_annotate_2679_ == 0 {
                        v_p_2760_ = leanh::lean_ctor_get(v_p_2680_, 1);
                        leanh::lean_inc_ref(v_p_2760_);
                        leanh::lean_dec_ref_known(v_p_2680_, 3);
                        v_p_2680_ = v_p_2760_;
                        state = 0;
                        continue;
                    } else {
                        v_varId_2762_ = leanh::lean_ctor_get(v_p_2680_, 0);
                        leanh::lean_inc(v_varId_2762_);
                        v_p_2763_ = leanh::lean_ctor_get(v_p_2680_, 1);
                        leanh::lean_inc_ref(v_p_2763_);
                        v_hId_2764_ = leanh::lean_ctor_get(v_p_2680_, 2);
                        leanh::lean_inc(v_hId_2764_);
                        leanh::lean_dec_ref_known(v_p_2680_, 3);
                        v___x_2765_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_2679_, v_p_2763_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
                        if leanh::lean_obj_tag(v___x_2765_) == 0 {
                            v_a_2766_ = leanh::lean_ctor_get(v___x_2765_, 0);
                            leanh::lean_inc(v_a_2766_);
                            leanh::lean_dec_ref_known(v___x_2765_, 1);
                            v___x_2767_ = l_Lean_mkFVar(v_varId_2762_);
                            v___x_2768_ = l_Lean_mkFVar(v_hId_2764_);
                            v___x_2769_ = l_Lean_Meta_Match_mkNamedPattern(
                                v___x_2767_,
                                v___x_2768_,
                                v_a_2766_,
                                v_a_2681_,
                                v_a_2682_,
                                v_a_2683_,
                                v_a_2684_,
                            );
                            return v___x_2769_;
                        } else {
                            leanh::lean_dec(v_hId_2764_);
                            leanh::lean_dec(v_varId_2762_);
                            return v___x_2765_;
                        }
                    }
                }
            },
            1 => {
                if v_isShared_2689_ == 0 {
                    v___x_2691_ = v___x_2688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_e_2686_);
                    v___x_2691_ = v_reuseFailAlloc_2692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2691_;
            }
            3 => {
                v___x_2698_ = l_Lean_mkInaccessible(v_e_2694_);
                if v_isShared_2697_ == 0 {
                    leanh::lean_ctor_set(v___x_2696_, 0, v___x_2698_);
                    v___x_2700_ = v___x_2696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
                    v___x_2700_ = v_reuseFailAlloc_2701_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2700_;
            }
            5 => {
                v___x_2707_ = l_Lean_mkFVar(v_fvarId_2703_);
                if v_isShared_2706_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2705_, 0);
                    leanh::lean_ctor_set(v___x_2705_, 0, v___x_2707_);
                    v___x_2709_ = v___x_2705_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2709_;
            }
            7 => {
                v___x_2722_ = l_Lean_mkConst(v_ctorName_2712_, v_us_2713_);
                v___x_2723_ = l_List_appendTR___redArg(v_params_2714_, v_a_2718_);
                v___x_2724_ = lean_array_mk(v___x_2723_);
                v___x_2725_ = l_Lean_mkAppN(v___x_2722_, v___x_2724_);
                leanh::lean_dec_ref(v___x_2724_);
                if v_isShared_2721_ == 0 {
                    leanh::lean_ctor_set(v___x_2720_, 0, v___x_2725_);
                    v___x_2727_ = v___x_2720_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
                    v___x_2727_ = v_reuseFailAlloc_2728_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2727_;
            }
            9 => {
                if v_isShared_2733_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2735_;
            }
            11 => {
                if v_isShared_2741_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2740_, 0);
                    v___x_2743_ = v___x_2740_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_e_2738_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2743_;
            }
            13 => {
                if v_isShared_2755_ == 0 {
                    v___x_2757_ = v___x_2754_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
                    v___x_2757_ = v_reuseFailAlloc_2758_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(
    mut v_annotate_2770_: u8,
    mut v_x_2771_: *mut leanh::LeanObject,
    mut v_x_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
    mut v___y_2774_: *mut leanh::LeanObject,
    mut v___y_2775_: *mut leanh::LeanObject,
    mut v___y_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2771_) == 0 {
                    v___x_2778_ = l_List_reverse___redArg(v_x_2772_);
                    v___x_2779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2779_, 0, v___x_2778_);
                    return v___x_2779_;
                } else {
                    v_head_2780_ = leanh::lean_ctor_get(v_x_2771_, 0);
                    v_tail_2781_ = leanh::lean_ctor_get(v_x_2771_, 1);
                    v_isSharedCheck_2799_ = (!leanh::lean_is_exclusive(v_x_2771_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2783_ = v_x_2771_;
                        v_isShared_2784_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2781_);
                        leanh::lean_inc(v_head_2780_);
                        leanh::lean_dec(v_x_2771_);
                        v___x_2783_ = leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2785_ =
                    l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
                        v_annotate_2770_,
                        v_head_2780_,
                        v___y_2773_,
                        v___y_2774_,
                        v___y_2775_,
                        v___y_2776_,
                    );
                if leanh::lean_obj_tag(v___x_2785_) == 0 {
                    v_a_2786_ = leanh::lean_ctor_get(v___x_2785_, 0);
                    leanh::lean_inc(v_a_2786_);
                    leanh::lean_dec_ref_known(v___x_2785_, 1);
                    if v_isShared_2784_ == 0 {
                        leanh::lean_ctor_set(v___x_2783_, 1, v_x_2772_);
                        leanh::lean_ctor_set(v___x_2783_, 0, v_a_2786_);
                        v___x_2788_ = v___x_2783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2790_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2786_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_x_2772_);
                        v___x_2788_ = v_reuseFailAlloc_2790_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2783_);
                    leanh::lean_dec(v_tail_2781_);
                    leanh::lean_dec(v_x_2772_);
                    v_a_2791_ = leanh::lean_ctor_get(v___x_2785_, 0);
                    v_isSharedCheck_2798_ = (!leanh::lean_is_exclusive(v___x_2785_)) as u8;
                    if v_isSharedCheck_2798_ == 0 {
                        v___x_2793_ = v___x_2785_;
                        v_isShared_2794_ = v_isSharedCheck_2798_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2791_);
                        leanh::lean_dec(v___x_2785_);
                        v___x_2793_ = leanh::lean_box(0);
                        v_isShared_2794_ = v_isSharedCheck_2798_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_2771_ = v_tail_2781_;
                v_x_2772_ = v___x_2788_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2794_ == 0 {
                    v___x_2796_ = v___x_2793_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(
    mut v_annotate_2800_: *mut leanh::LeanObject,
    mut v_x_2801_: *mut leanh::LeanObject,
    mut v_x_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_annotate_boxed_2808_: u8 = 0;
    let mut v_res_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_annotate_boxed_2808_ = (leanh::lean_unbox(v_annotate_2800_) as u8);
    v_res_2809_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_boxed_2808_, v_x_2801_, v_x_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
    leanh::lean_dec(v___y_2806_);
    leanh::lean_dec_ref(v___y_2805_);
    leanh::lean_dec(v___y_2804_);
    leanh::lean_dec_ref(v___y_2803_);
    return v_res_2809_;
}
pub unsafe fn l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(
    mut v_annotate_2810_: *mut leanh::LeanObject,
    mut v_p_2811_: *mut leanh::LeanObject,
    mut v_a_2812_: *mut leanh::LeanObject,
    mut v_a_2813_: *mut leanh::LeanObject,
    mut v_a_2814_: *mut leanh::LeanObject,
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_a_2816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_annotate_boxed_2817_: u8 = 0;
    let mut v_res_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_annotate_boxed_2817_ = (leanh::lean_unbox(v_annotate_2810_) as u8);
    v_res_2818_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
        v_annotate_boxed_2817_,
        v_p_2811_,
        v_a_2812_,
        v_a_2813_,
        v_a_2814_,
        v_a_2815_,
    );
    leanh::lean_dec(v_a_2815_);
    leanh::lean_dec_ref(v_a_2814_);
    leanh::lean_dec(v_a_2813_);
    leanh::lean_dec_ref(v_a_2812_);
    return v_res_2818_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_toExpr(
    mut v_p_2819_: *mut leanh::LeanObject,
    mut v_annotate_2820_: u8,
    mut v_a_2821_: *mut leanh::LeanObject,
    mut v_a_2822_: *mut leanh::LeanObject,
    mut v_a_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2826_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
        v_annotate_2820_,
        v_p_2819_,
        v_a_2821_,
        v_a_2822_,
        v_a_2823_,
        v_a_2824_,
    );
    return v___x_2826_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_toExpr___boxed(
    mut v_p_2827_: *mut leanh::LeanObject,
    mut v_annotate_2828_: *mut leanh::LeanObject,
    mut v_a_2829_: *mut leanh::LeanObject,
    mut v_a_2830_: *mut leanh::LeanObject,
    mut v_a_2831_: *mut leanh::LeanObject,
    mut v_a_2832_: *mut leanh::LeanObject,
    mut v_a_2833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_annotate_boxed_2834_: u8 = 0;
    let mut v_res_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_annotate_boxed_2834_ = (leanh::lean_unbox(v_annotate_2828_) as u8);
    v_res_2835_ = l_Lean_Meta_Match_Pattern_toExpr(
        v_p_2827_,
        v_annotate_boxed_2834_,
        v_a_2829_,
        v_a_2830_,
        v_a_2831_,
        v_a_2832_,
    );
    leanh::lean_dec(v_a_2832_);
    leanh::lean_dec_ref(v_a_2831_);
    leanh::lean_dec(v_a_2830_);
    leanh::lean_dec_ref(v_a_2829_);
    return v_res_2835_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(
    mut v_s_2836_: *mut leanh::LeanObject,
    mut v_a_2837_: *mut leanh::LeanObject,
    mut v_a_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2837_) == 0 {
                    leanh::lean_dec(v_s_2836_);
                    v___x_2839_ = l_List_reverse___redArg(v_a_2838_);
                    return v___x_2839_;
                } else {
                    v_head_2840_ = leanh::lean_ctor_get(v_a_2837_, 0);
                    v_tail_2841_ = leanh::lean_ctor_get(v_a_2837_, 1);
                    v_isSharedCheck_2850_ = (!leanh::lean_is_exclusive(v_a_2837_)) as u8;
                    if v_isSharedCheck_2850_ == 0 {
                        v___x_2843_ = v_a_2837_;
                        v_isShared_2844_ = v_isSharedCheck_2850_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2841_);
                        leanh::lean_inc(v_head_2840_);
                        leanh::lean_dec(v_a_2837_);
                        v___x_2843_ = leanh::lean_box(0);
                        v_isShared_2844_ = v_isSharedCheck_2850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_s_2836_);
                v___x_2845_ = l_Lean_Meta_FVarSubst_apply(v_s_2836_, v_head_2840_);
                leanh::lean_dec(v_head_2840_);
                if v_isShared_2844_ == 0 {
                    leanh::lean_ctor_set(v___x_2843_, 1, v_a_2838_);
                    leanh::lean_ctor_set(v___x_2843_, 0, v___x_2845_);
                    v___x_2847_ = v___x_2843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_a_2838_);
                    v___x_2847_ = v_reuseFailAlloc_2849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2837_ = v_tail_2841_;
                v_a_2838_ = v___x_2847_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_applyFVarSubst(
    mut v_s_2851_: *mut leanh::LeanObject,
    mut v_x_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_fvarId_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v_val_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_unused_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_e_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v_type_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v_varId_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hId_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2852_) {
                0 => {
                    v_e_2853_ = leanh::lean_ctor_get(v_x_2852_, 0);
                    v_isSharedCheck_2861_ = (!leanh::lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2855_ = v_x_2852_;
                        v_isShared_2856_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_e_2853_);
                        leanh::lean_dec(v_x_2852_);
                        v___x_2855_ = leanh::lean_box(0);
                        v_isShared_2856_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_fvarId_2862_ = leanh::lean_ctor_get(v_x_2852_, 0);
                    v___x_2863_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2851_, v_fvarId_2862_);
                    leanh::lean_dec(v_s_2851_);
                    if leanh::lean_obj_tag(v___x_2863_) == 0 {
                        return v_x_2852_;
                    } else {
                        v_isSharedCheck_2871_ = (!leanh::lean_is_exclusive(v_x_2852_)) as u8;
                        if v_isSharedCheck_2871_ == 0 {
                            v_unused_2872_ = leanh::lean_ctor_get(v_x_2852_, 0);
                            leanh::lean_dec(v_unused_2872_);
                            v___x_2865_ = v_x_2852_;
                            v_isShared_2866_ = v_isSharedCheck_2871_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2852_);
                            v___x_2865_ = leanh::lean_box(0);
                            v_isShared_2866_ = v_isSharedCheck_2871_;
                            state = 3;
                            continue;
                        }
                    }
                }
                2 => {
                    v_ctorName_2873_ = leanh::lean_ctor_get(v_x_2852_, 0);
                    v_us_2874_ = leanh::lean_ctor_get(v_x_2852_, 1);
                    v_params_2875_ = leanh::lean_ctor_get(v_x_2852_, 2);
                    v_fields_2876_ = leanh::lean_ctor_get(v_x_2852_, 3);
                    v_isSharedCheck_2886_ = (!leanh::lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2878_ = v_x_2852_;
                        v_isShared_2879_ = v_isSharedCheck_2886_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_fields_2876_);
                        leanh::lean_inc(v_params_2875_);
                        leanh::lean_inc(v_us_2874_);
                        leanh::lean_inc(v_ctorName_2873_);
                        leanh::lean_dec(v_x_2852_);
                        v___x_2878_ = leanh::lean_box(0);
                        v_isShared_2879_ = v_isSharedCheck_2886_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_e_2887_ = leanh::lean_ctor_get(v_x_2852_, 0);
                    v_isSharedCheck_2895_ = (!leanh::lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2889_ = v_x_2852_;
                        v_isShared_2890_ = v_isSharedCheck_2895_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_e_2887_);
                        leanh::lean_dec(v_x_2852_);
                        v___x_2889_ = leanh::lean_box(0);
                        v_isShared_2890_ = v_isSharedCheck_2895_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_type_2896_ = leanh::lean_ctor_get(v_x_2852_, 0);
                    v_xs_2897_ = leanh::lean_ctor_get(v_x_2852_, 1);
                    v_isSharedCheck_2907_ = (!leanh::lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2907_ == 0 {
                        v___x_2899_ = v_x_2852_;
                        v_isShared_2900_ = v_isSharedCheck_2907_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_2897_);
                        leanh::lean_inc(v_type_2896_);
                        leanh::lean_dec(v_x_2852_);
                        v___x_2899_ = leanh::lean_box(0);
                        v_isShared_2900_ = v_isSharedCheck_2907_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    v_varId_2908_ = leanh::lean_ctor_get(v_x_2852_, 0);
                    v_p_2909_ = leanh::lean_ctor_get(v_x_2852_, 1);
                    v_hId_2910_ = leanh::lean_ctor_get(v_x_2852_, 2);
                    v_isSharedCheck_2920_ = (!leanh::lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2920_ == 0 {
                        v___x_2912_ = v_x_2852_;
                        v_isShared_2913_ = v_isSharedCheck_2920_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_hId_2910_);
                        leanh::lean_inc(v_p_2909_);
                        leanh::lean_inc(v_varId_2908_);
                        leanh::lean_dec(v_x_2852_);
                        v___x_2912_ = leanh::lean_box(0);
                        v_isShared_2913_ = v_isSharedCheck_2920_;
                        state = 11;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2857_ = l_Lean_Meta_FVarSubst_apply(v_s_2851_, v_e_2853_);
                leanh::lean_dec_ref(v_e_2853_);
                if v_isShared_2856_ == 0 {
                    leanh::lean_ctor_set(v___x_2855_, 0, v___x_2857_);
                    v___x_2859_ = v___x_2855_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
                    v___x_2859_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2859_;
            }
            3 => {
                v_val_2867_ = leanh::lean_ctor_get(v___x_2863_, 0);
                leanh::lean_inc(v_val_2867_);
                leanh::lean_dec_ref_known(v___x_2863_, 1);
                if v_isShared_2866_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2865_, 0);
                    leanh::lean_ctor_set(v___x_2865_, 0, v_val_2867_);
                    v___x_2869_ = v___x_2865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_val_2867_);
                    v___x_2869_ = v_reuseFailAlloc_2870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2869_;
            }
            5 => {
                v___x_2880_ = leanh::lean_box(0);
                leanh::lean_inc(v_s_2851_);
                v___x_2881_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(
                        v_s_2851_,
                        v_params_2875_,
                        v___x_2880_,
                    );
                v___x_2882_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(
                        v_s_2851_,
                        v_fields_2876_,
                        v___x_2880_,
                    );
                if v_isShared_2879_ == 0 {
                    leanh::lean_ctor_set(v___x_2878_, 3, v___x_2882_);
                    leanh::lean_ctor_set(v___x_2878_, 2, v___x_2881_);
                    v___x_2884_ = v___x_2878_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_ctorName_2873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_us_2874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 2, v___x_2881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 3, v___x_2882_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2884_;
            }
            7 => {
                v___x_2891_ = l_Lean_Meta_FVarSubst_apply(v_s_2851_, v_e_2887_);
                leanh::lean_dec_ref(v_e_2887_);
                if v_isShared_2890_ == 0 {
                    leanh::lean_ctor_set(v___x_2889_, 0, v___x_2891_);
                    v___x_2893_ = v___x_2889_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2893_;
            }
            9 => {
                leanh::lean_inc(v_s_2851_);
                v___x_2901_ = l_Lean_Meta_FVarSubst_apply(v_s_2851_, v_type_2896_);
                leanh::lean_dec_ref(v_type_2896_);
                v___x_2902_ = leanh::lean_box(0);
                v___x_2903_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(
                        v_s_2851_,
                        v_xs_2897_,
                        v___x_2902_,
                    );
                if v_isShared_2900_ == 0 {
                    leanh::lean_ctor_set(v___x_2899_, 1, v___x_2903_);
                    leanh::lean_ctor_set(v___x_2899_, 0, v___x_2901_);
                    v___x_2905_ = v___x_2899_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2906_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 1, v___x_2903_);
                    v___x_2905_ = v_reuseFailAlloc_2906_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2905_;
            }
            11 => {
                v___x_2914_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2851_, v_varId_2908_);
                if leanh::lean_obj_tag(v___x_2914_) == 0 {
                    v___x_2915_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_2851_, v_p_2909_);
                    if v_isShared_2913_ == 0 {
                        leanh::lean_ctor_set(v___x_2912_, 1, v___x_2915_);
                        v___x_2917_ = v___x_2912_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2918_ = leanh::lean_alloc_ctor(5, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_varId_2908_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2915_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_hId_2910_);
                        v___x_2917_ = v_reuseFailAlloc_2918_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2914_, 1);
                    leanh::lean_del_object(v___x_2912_);
                    leanh::lean_dec(v_hId_2910_);
                    leanh::lean_dec(v_varId_2908_);
                    v_x_2852_ = v_p_2909_;
                    state = 0;
                    continue;
                }
            }
            12 => {
                return v___x_2917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(
    mut v_s_2921_: *mut leanh::LeanObject,
    mut v_a_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2922_) == 0 {
                    leanh::lean_dec(v_s_2921_);
                    v___x_2924_ = l_List_reverse___redArg(v_a_2923_);
                    return v___x_2924_;
                } else {
                    v_head_2925_ = leanh::lean_ctor_get(v_a_2922_, 0);
                    v_tail_2926_ = leanh::lean_ctor_get(v_a_2922_, 1);
                    v_isSharedCheck_2935_ = (!leanh::lean_is_exclusive(v_a_2922_)) as u8;
                    if v_isSharedCheck_2935_ == 0 {
                        v___x_2928_ = v_a_2922_;
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2926_);
                        leanh::lean_inc(v_head_2925_);
                        leanh::lean_dec(v_a_2922_);
                        v___x_2928_ = leanh::lean_box(0);
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_s_2921_);
                v___x_2930_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_2921_, v_head_2925_);
                if v_isShared_2929_ == 0 {
                    leanh::lean_ctor_set(v___x_2928_, 1, v_a_2923_);
                    leanh::lean_ctor_set(v___x_2928_, 0, v___x_2930_);
                    v___x_2932_ = v___x_2928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_a_2923_);
                    v___x_2932_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2922_ = v_tail_2926_;
                v_a_2923_ = v___x_2932_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_replaceFVarId(
    mut v_fvarId_2936_: *mut leanh::LeanObject,
    mut v_v_2937_: *mut leanh::LeanObject,
    mut v_p_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_2939_ = leanh::lean_box(0);
    v___x_2940_ = l_Lean_Meta_FVarSubst_insert(v_s_2939_, v_fvarId_2936_, v_v_2937_);
    v___x_2941_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v___x_2940_, v_p_2938_);
    return v___x_2941_;
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(
    mut v_x_2942_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2943_: u8 = 0;
    let mut v_head_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2942_) == 0 {
                    v___x_2943_ = 0;
                    return v___x_2943_;
                } else {
                    v_head_2944_ = leanh::lean_ctor_get(v_x_2942_, 0);
                    v_tail_2945_ = leanh::lean_ctor_get(v_x_2942_, 1);
                    v___x_2946_ = l_Lean_Expr_hasExprMVar(v_head_2944_);
                    if v___x_2946_ == 0 {
                        v_x_2942_ = v_tail_2945_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2946_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0___boxed(
    mut v_x_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2949_: u8 = 0;
    let mut v_r_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_x_2948_);
    leanh::lean_dec(v_x_2948_);
    v_r_2950_ = leanh::lean_box((v_res_2949_) as usize);
    return v_r_2950_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_hasExprMVar(
    mut v_x_2951_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_e_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: u8 = 0;
    let mut v_params_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: u8 = 0;
    let mut v_e_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v_p_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2951_) {
                0 => {
                    v_e_2952_ = leanh::lean_ctor_get(v_x_2951_, 0);
                    v___x_2953_ = l_Lean_Expr_hasExprMVar(v_e_2952_);
                    return v___x_2953_;
                }
                2 => {
                    v_params_2954_ = leanh::lean_ctor_get(v_x_2951_, 2);
                    v_fields_2955_ = leanh::lean_ctor_get(v_x_2951_, 3);
                    v___x_2956_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(
                        v_params_2954_,
                    );
                    if v___x_2956_ == 0 {
                        v___x_2957_ =
                            l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(
                                v_fields_2955_,
                            );
                        return v___x_2957_;
                    } else {
                        return v___x_2956_;
                    }
                }
                3 => {
                    v_e_2958_ = leanh::lean_ctor_get(v_x_2951_, 0);
                    v___x_2959_ = l_Lean_Expr_hasExprMVar(v_e_2958_);
                    return v___x_2959_;
                }
                5 => {
                    v_p_2960_ = leanh::lean_ctor_get(v_x_2951_, 1);
                    v_x_2951_ = v_p_2960_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_type_2962_ = leanh::lean_ctor_get(v_x_2951_, 0);
                    v_xs_2963_ = leanh::lean_ctor_get(v_x_2951_, 1);
                    v___x_2964_ = l_Lean_Expr_hasExprMVar(v_type_2962_);
                    if v___x_2964_ == 0 {
                        v___x_2965_ =
                            l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(
                                v_xs_2963_,
                            );
                        return v___x_2965_;
                    } else {
                        return v___x_2964_;
                    }
                }
                _ => {
                    v___x_2966_ = 0;
                    return v___x_2966_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(
    mut v_x_2967_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2968_: u8 = 0;
    let mut v_head_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2967_) == 0 {
                    v___x_2968_ = 0;
                    return v___x_2968_;
                } else {
                    v_head_2969_ = leanh::lean_ctor_get(v_x_2967_, 0);
                    v_tail_2970_ = leanh::lean_ctor_get(v_x_2967_, 1);
                    v___x_2971_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_head_2969_);
                    if v___x_2971_ == 0 {
                        v_x_2967_ = v_tail_2970_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2971_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1___boxed(
    mut v_x_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2974_: u8 = 0;
    let mut v_r_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_x_2973_);
    leanh::lean_dec(v_x_2973_);
    v_r_2975_ = leanh::lean_box((v_res_2974_) as usize);
    return v_r_2975_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(
    mut v_x_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2977_: u8 = 0;
    let mut v_r_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_2976_);
    leanh::lean_dec_ref(v_x_2976_);
    v_r_2978_ = leanh::lean_box((v_res_2977_) as usize);
    return v_r_2978_;
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(
    mut v_as_2979_: *mut leanh::LeanObject,
    mut v___y_2980_: *mut leanh::LeanObject,
    mut v___y_2981_: *mut leanh::LeanObject,
    mut v___y_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_2979_) == 0 {
                    v___x_2986_ = leanh::lean_box(0);
                    v___x_2987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2987_, 0, v___x_2986_);
                    return v___x_2987_;
                } else {
                    v_head_2988_ = leanh::lean_ctor_get(v_as_2979_, 0);
                    leanh::lean_inc(v_head_2988_);
                    v_tail_2989_ = leanh::lean_ctor_get(v_as_2979_, 1);
                    leanh::lean_inc(v_tail_2989_);
                    leanh::lean_dec_ref_known(v_as_2979_, 2);
                    v___x_2990_ = l_Lean_Expr_collectFVars(
                        v_head_2988_,
                        v___y_2980_,
                        v___y_2981_,
                        v___y_2982_,
                        v___y_2983_,
                        v___y_2984_,
                    );
                    if leanh::lean_obj_tag(v___x_2990_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2990_, 1);
                        v_as_2979_ = v_tail_2989_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_2989_);
                        return v___x_2990_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(
    mut v_as_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
    mut v___y_2994_: *mut leanh::LeanObject,
    mut v___y_2995_: *mut leanh::LeanObject,
    mut v___y_2996_: *mut leanh::LeanObject,
    mut v___y_2997_: *mut leanh::LeanObject,
    mut v___y_2998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(
        v_as_2992_,
        v___y_2993_,
        v___y_2994_,
        v___y_2995_,
        v___y_2996_,
        v___y_2997_,
    );
    leanh::lean_dec(v___y_2997_);
    leanh::lean_dec_ref(v___y_2996_);
    leanh::lean_dec(v___y_2995_);
    leanh::lean_dec_ref(v___y_2994_);
    leanh::lean_dec(v___y_2993_);
    return v_res_2999_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_collectFVars(
    mut v_p_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
    mut v_a_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_params_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varId_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hId_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_p_3000_) {
                1 => {
                    v_fvarId_3007_ = leanh::lean_ctor_get(v_p_3000_, 0);
                    v_isSharedCheck_3018_ = (!leanh::lean_is_exclusive(v_p_3000_)) as u8;
                    if v_isSharedCheck_3018_ == 0 {
                        v___x_3009_ = v_p_3000_;
                        v_isShared_3010_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_3007_);
                        leanh::lean_dec(v_p_3000_);
                        v___x_3009_ = leanh::lean_box(0);
                        v_isShared_3010_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_params_3019_ = leanh::lean_ctor_get(v_p_3000_, 2);
                    leanh::lean_inc(v_params_3019_);
                    v_fields_3020_ = leanh::lean_ctor_get(v_p_3000_, 3);
                    leanh::lean_inc(v_fields_3020_);
                    leanh::lean_dec_ref_known(v_p_3000_, 4);
                    v___x_3021_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(
                        v_params_3019_,
                        v_a_3001_,
                        v_a_3002_,
                        v_a_3003_,
                        v_a_3004_,
                        v_a_3005_,
                    );
                    if leanh::lean_obj_tag(v___x_3021_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3021_, 1);
                        v___x_3022_ =
                            l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
                                v_fields_3020_,
                                v_a_3001_,
                                v_a_3002_,
                                v_a_3003_,
                                v_a_3004_,
                                v_a_3005_,
                            );
                        return v___x_3022_;
                    } else {
                        leanh::lean_dec(v_fields_3020_);
                        return v___x_3021_;
                    }
                }
                4 => {
                    v_type_3023_ = leanh::lean_ctor_get(v_p_3000_, 0);
                    leanh::lean_inc_ref(v_type_3023_);
                    v_xs_3024_ = leanh::lean_ctor_get(v_p_3000_, 1);
                    leanh::lean_inc(v_xs_3024_);
                    leanh::lean_dec_ref_known(v_p_3000_, 2);
                    v___x_3025_ = l_Lean_Expr_collectFVars(
                        v_type_3023_,
                        v_a_3001_,
                        v_a_3002_,
                        v_a_3003_,
                        v_a_3004_,
                        v_a_3005_,
                    );
                    if leanh::lean_obj_tag(v___x_3025_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3025_, 1);
                        v___x_3026_ =
                            l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
                                v_xs_3024_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_,
                            );
                        return v___x_3026_;
                    } else {
                        leanh::lean_dec(v_xs_3024_);
                        return v___x_3025_;
                    }
                }
                5 => {
                    v_varId_3027_ = leanh::lean_ctor_get(v_p_3000_, 0);
                    leanh::lean_inc(v_varId_3027_);
                    v_p_3028_ = leanh::lean_ctor_get(v_p_3000_, 1);
                    leanh::lean_inc_ref(v_p_3028_);
                    v_hId_3029_ = leanh::lean_ctor_get(v_p_3000_, 2);
                    leanh::lean_inc(v_hId_3029_);
                    leanh::lean_dec_ref_known(v_p_3000_, 3);
                    v___x_3030_ = lean_st_ref_take(v_a_3001_);
                    v___x_3031_ = l_Lean_CollectFVars_State_add(v___x_3030_, v_varId_3027_);
                    v___x_3032_ = l_Lean_CollectFVars_State_add(v___x_3031_, v_hId_3029_);
                    v___x_3033_ = lean_st_ref_set(v_a_3001_, v___x_3032_);
                    v_p_3000_ = v_p_3028_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_e_3035_ = leanh::lean_ctor_get(v_p_3000_, 0);
                    leanh::lean_inc_ref(v_e_3035_);
                    leanh::lean_dec_ref(v_p_3000_);
                    v___x_3036_ = l_Lean_Expr_collectFVars(
                        v_e_3035_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_,
                    );
                    return v___x_3036_;
                }
            },
            1 => {
                v___x_3011_ = lean_st_ref_take(v_a_3001_);
                v___x_3012_ = l_Lean_CollectFVars_State_add(v___x_3011_, v_fvarId_3007_);
                v___x_3013_ = lean_st_ref_set(v_a_3001_, v___x_3012_);
                v___x_3014_ = leanh::lean_box(0);
                if v_isShared_3010_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3009_, 0);
                    leanh::lean_ctor_set(v___x_3009_, 0, v___x_3014_);
                    v___x_3016_ = v___x_3009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
                    v___x_3016_ = v_reuseFailAlloc_3017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
    mut v_as_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
    mut v___y_3039_: *mut leanh::LeanObject,
    mut v___y_3040_: *mut leanh::LeanObject,
    mut v___y_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_3037_) == 0 {
                    v___x_3044_ = leanh::lean_box(0);
                    v___x_3045_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3045_, 0, v___x_3044_);
                    return v___x_3045_;
                } else {
                    v_head_3046_ = leanh::lean_ctor_get(v_as_3037_, 0);
                    leanh::lean_inc(v_head_3046_);
                    v_tail_3047_ = leanh::lean_ctor_get(v_as_3037_, 1);
                    leanh::lean_inc(v_tail_3047_);
                    leanh::lean_dec_ref_known(v_as_3037_, 2);
                    v___x_3048_ = l_Lean_Meta_Match_Pattern_collectFVars(
                        v_head_3046_,
                        v___y_3038_,
                        v___y_3039_,
                        v___y_3040_,
                        v___y_3041_,
                        v___y_3042_,
                    );
                    if leanh::lean_obj_tag(v___x_3048_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3048_, 1);
                        v_as_3037_ = v_tail_3047_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_3047_);
                        return v___x_3048_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(
    mut v_as_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
    mut v___y_3053_: *mut leanh::LeanObject,
    mut v___y_3054_: *mut leanh::LeanObject,
    mut v___y_3055_: *mut leanh::LeanObject,
    mut v___y_3056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
        v_as_3050_,
        v___y_3051_,
        v___y_3052_,
        v___y_3053_,
        v___y_3054_,
        v___y_3055_,
    );
    leanh::lean_dec(v___y_3055_);
    leanh::lean_dec_ref(v___y_3054_);
    leanh::lean_dec(v___y_3053_);
    leanh::lean_dec_ref(v___y_3052_);
    leanh::lean_dec(v___y_3051_);
    return v_res_3057_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_collectFVars___boxed(
    mut v_p_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
    mut v_a_3060_: *mut leanh::LeanObject,
    mut v_a_3061_: *mut leanh::LeanObject,
    mut v_a_3062_: *mut leanh::LeanObject,
    mut v_a_3063_: *mut leanh::LeanObject,
    mut v_a_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3065_ = l_Lean_Meta_Match_Pattern_collectFVars(
        v_p_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_,
    );
    leanh::lean_dec(v_a_3063_);
    leanh::lean_dec_ref(v_a_3062_);
    leanh::lean_dec(v_a_3061_);
    leanh::lean_dec_ref(v_a_3060_);
    leanh::lean_dec(v_a_3059_);
    return v_res_3065_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(
    mut v_e_3066_: *mut leanh::LeanObject,
    mut v___y_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_unused_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3069_ = l_Lean_Expr_hasMVar(v_e_3066_);
                if v___x_3069_ == 0 {
                    v___x_3070_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3070_, 0, v_e_3066_);
                    return v___x_3070_;
                } else {
                    v___x_3071_ = lean_st_ref_get(v___y_3067_);
                    v_mctx_3072_ = leanh::lean_ctor_get(v___x_3071_, 0);
                    leanh::lean_inc_ref(v_mctx_3072_);
                    leanh::lean_dec(v___x_3071_);
                    v___x_3073_ = l_Lean_instantiateMVarsCore(v_mctx_3072_, v_e_3066_);
                    v_fst_3074_ = leanh::lean_ctor_get(v___x_3073_, 0);
                    leanh::lean_inc(v_fst_3074_);
                    v_snd_3075_ = leanh::lean_ctor_get(v___x_3073_, 1);
                    leanh::lean_inc(v_snd_3075_);
                    leanh::lean_dec_ref(v___x_3073_);
                    v___x_3076_ = lean_st_ref_take(v___y_3067_);
                    v_cache_3077_ = leanh::lean_ctor_get(v___x_3076_, 1);
                    v_zetaDeltaFVarIds_3078_ = leanh::lean_ctor_get(v___x_3076_, 2);
                    v_postponed_3079_ = leanh::lean_ctor_get(v___x_3076_, 3);
                    v_diag_3080_ = leanh::lean_ctor_get(v___x_3076_, 4);
                    v_isSharedCheck_3089_ = (!leanh::lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3089_ == 0 {
                        v_unused_3090_ = leanh::lean_ctor_get(v___x_3076_, 0);
                        leanh::lean_dec(v_unused_3090_);
                        v___x_3082_ = v___x_3076_;
                        v_isShared_3083_ = v_isSharedCheck_3089_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3080_);
                        leanh::lean_inc(v_postponed_3079_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3078_);
                        leanh::lean_inc(v_cache_3077_);
                        leanh::lean_dec(v___x_3076_);
                        v___x_3082_ = leanh::lean_box(0);
                        v_isShared_3083_ = v_isSharedCheck_3089_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3083_ == 0 {
                    leanh::lean_ctor_set(v___x_3082_, 0, v_snd_3075_);
                    v___x_3085_ = v___x_3082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_snd_3075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_cache_3077_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3088_,
                        2,
                        v_zetaDeltaFVarIds_3078_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_postponed_3079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_diag_3080_);
                    v___x_3085_ = v_reuseFailAlloc_3088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3086_ = lean_st_ref_set(v___y_3067_, v___x_3085_);
                v___x_3087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3087_, 0, v_fst_3074_);
                return v___x_3087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(
    mut v_e_3091_: *mut leanh::LeanObject,
    mut v___y_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3094_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(
            v_e_3091_,
            v___y_3092_,
        );
    leanh::lean_dec(v___y_3092_);
    return v_res_3094_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(
    mut v_e_3095_: *mut leanh::LeanObject,
    mut v___y_3096_: *mut leanh::LeanObject,
    mut v___y_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(
            v_e_3095_,
            v___y_3097_,
        );
    return v___x_3101_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(
    mut v_e_3102_: *mut leanh::LeanObject,
    mut v___y_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(
        v_e_3102_,
        v___y_3103_,
        v___y_3104_,
        v___y_3105_,
        v___y_3106_,
    );
    leanh::lean_dec(v___y_3106_);
    leanh::lean_dec_ref(v___y_3105_);
    leanh::lean_dec(v___y_3104_);
    leanh::lean_dec_ref(v___y_3103_);
    return v_res_3108_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(
    mut v_x_3109_: *mut leanh::LeanObject,
    mut v_x_3110_: *mut leanh::LeanObject,
    mut v___y_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
    mut v___y_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3109_) == 0 {
                    v___x_3116_ = l_List_reverse___redArg(v_x_3110_);
                    v___x_3117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3117_, 0, v___x_3116_);
                    return v___x_3117_;
                } else {
                    v_head_3118_ = leanh::lean_ctor_get(v_x_3109_, 0);
                    v_tail_3119_ = leanh::lean_ctor_get(v_x_3109_, 1);
                    v_isSharedCheck_3129_ = (!leanh::lean_is_exclusive(v_x_3109_)) as u8;
                    if v_isSharedCheck_3129_ == 0 {
                        v___x_3121_ = v_x_3109_;
                        v_isShared_3122_ = v_isSharedCheck_3129_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3119_);
                        leanh::lean_inc(v_head_3118_);
                        leanh::lean_dec(v_x_3109_);
                        v___x_3121_ = leanh::lean_box(0);
                        v_isShared_3122_ = v_isSharedCheck_3129_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3123_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_3118_, v___y_3112_);
                v_a_3124_ = leanh::lean_ctor_get(v___x_3123_, 0);
                leanh::lean_inc(v_a_3124_);
                leanh::lean_dec_ref(v___x_3123_);
                if v_isShared_3122_ == 0 {
                    leanh::lean_ctor_set(v___x_3121_, 1, v_x_3110_);
                    leanh::lean_ctor_set(v___x_3121_, 0, v_a_3124_);
                    v___x_3126_ = v___x_3121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_x_3110_);
                    v___x_3126_ = v_reuseFailAlloc_3128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_3109_ = v_tail_3119_;
                v_x_3110_ = v___x_3126_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(
    mut v_x_3130_: *mut leanh::LeanObject,
    mut v_x_3131_: *mut leanh::LeanObject,
    mut v___y_3132_: *mut leanh::LeanObject,
    mut v___y_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3137_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(
        v_x_3130_,
        v_x_3131_,
        v___y_3132_,
        v___y_3133_,
        v___y_3134_,
        v___y_3135_,
    );
    leanh::lean_dec(v___y_3135_);
    leanh::lean_dec_ref(v___y_3134_);
    leanh::lean_dec(v___y_3133_);
    leanh::lean_dec_ref(v___y_3132_);
    return v_res_3137_;
}
pub unsafe fn l_Lean_Meta_Match_instantiatePatternMVars(
    mut v_x_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v_a_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_e_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v_a_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_ctorName_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v_a_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_a_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_varId_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hId_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_type_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v_a_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3279_: u8 = 0;
    let mut v_a_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3138_) {
                0 => {
                    v_e_3144_ = leanh::lean_ctor_get(v_x_3138_, 0);
                    v_isSharedCheck_3168_ = (!leanh::lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3146_ = v_x_3138_;
                        v_isShared_3147_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_e_3144_);
                        leanh::lean_dec(v_x_3138_);
                        v___x_3146_ = leanh::lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_e_3169_ = leanh::lean_ctor_get(v_x_3138_, 0);
                    v_isSharedCheck_3193_ = (!leanh::lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3193_ == 0 {
                        v___x_3171_ = v_x_3138_;
                        v_isShared_3172_ = v_isSharedCheck_3193_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_e_3169_);
                        leanh::lean_dec(v_x_3138_);
                        v___x_3171_ = leanh::lean_box(0);
                        v_isShared_3172_ = v_isSharedCheck_3193_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_ctorName_3194_ = leanh::lean_ctor_get(v_x_3138_, 0);
                    v_us_3195_ = leanh::lean_ctor_get(v_x_3138_, 1);
                    v_params_3196_ = leanh::lean_ctor_get(v_x_3138_, 2);
                    v_fields_3197_ = leanh::lean_ctor_get(v_x_3138_, 3);
                    v_isSharedCheck_3232_ = (!leanh::lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3199_ = v_x_3138_;
                        v_isShared_3200_ = v_isSharedCheck_3232_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_fields_3197_);
                        leanh::lean_inc(v_params_3196_);
                        leanh::lean_inc(v_us_3195_);
                        leanh::lean_inc(v_ctorName_3194_);
                        leanh::lean_dec(v_x_3138_);
                        v___x_3199_ = leanh::lean_box(0);
                        v_isShared_3200_ = v_isSharedCheck_3232_;
                        state = 13;
                        continue;
                    }
                }
                5 => {
                    v_varId_3233_ = leanh::lean_ctor_get(v_x_3138_, 0);
                    v_p_3234_ = leanh::lean_ctor_get(v_x_3138_, 1);
                    v_hId_3235_ = leanh::lean_ctor_get(v_x_3138_, 2);
                    v_isSharedCheck_3251_ = (!leanh::lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3251_ == 0 {
                        v___x_3237_ = v_x_3138_;
                        v_isShared_3238_ = v_isSharedCheck_3251_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_hId_3235_);
                        leanh::lean_inc(v_p_3234_);
                        leanh::lean_inc(v_varId_3233_);
                        leanh::lean_dec(v_x_3138_);
                        v___x_3237_ = leanh::lean_box(0);
                        v_isShared_3238_ = v_isSharedCheck_3251_;
                        state = 21;
                        continue;
                    }
                }
                4 => {
                    v_type_3252_ = leanh::lean_ctor_get(v_x_3138_, 0);
                    v_xs_3253_ = leanh::lean_ctor_get(v_x_3138_, 1);
                    v_isSharedCheck_3288_ = (!leanh::lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3288_ == 0 {
                        v___x_3255_ = v_x_3138_;
                        v_isShared_3256_ = v_isSharedCheck_3288_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_3253_);
                        leanh::lean_inc(v_type_3252_);
                        leanh::lean_dec(v_x_3138_);
                        v___x_3255_ = leanh::lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3288_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    v___x_3289_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3289_, 0, v_x_3138_);
                    return v___x_3289_;
                }
            },
            1 => {
                v___x_3148_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_3144_, v_a_3140_);
                if leanh::lean_obj_tag(v___x_3148_) == 0 {
                    v_a_3149_ = leanh::lean_ctor_get(v___x_3148_, 0);
                    v_isSharedCheck_3159_ = (!leanh::lean_is_exclusive(v___x_3148_)) as u8;
                    if v_isSharedCheck_3159_ == 0 {
                        v___x_3151_ = v___x_3148_;
                        v_isShared_3152_ = v_isSharedCheck_3159_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3149_);
                        leanh::lean_dec(v___x_3148_);
                        v___x_3151_ = leanh::lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3159_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3146_);
                    v_a_3160_ = leanh::lean_ctor_get(v___x_3148_, 0);
                    v_isSharedCheck_3167_ = (!leanh::lean_is_exclusive(v___x_3148_)) as u8;
                    if v_isSharedCheck_3167_ == 0 {
                        v___x_3162_ = v___x_3148_;
                        v_isShared_3163_ = v_isSharedCheck_3167_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3160_);
                        leanh::lean_dec(v___x_3148_);
                        v___x_3162_ = leanh::lean_box(0);
                        v_isShared_3163_ = v_isSharedCheck_3167_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3147_ == 0 {
                    leanh::lean_ctor_set(v___x_3146_, 0, v_a_3149_);
                    v___x_3154_ = v___x_3146_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3158_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3152_ == 0 {
                    leanh::lean_ctor_set(v___x_3151_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3156_;
            }
            5 => {
                if v_isShared_3163_ == 0 {
                    v___x_3165_ = v___x_3162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
                    v___x_3165_ = v_reuseFailAlloc_3166_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3165_;
            }
            7 => {
                v___x_3173_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_3169_, v_a_3140_);
                if leanh::lean_obj_tag(v___x_3173_) == 0 {
                    v_a_3174_ = leanh::lean_ctor_get(v___x_3173_, 0);
                    v_isSharedCheck_3184_ = (!leanh::lean_is_exclusive(v___x_3173_)) as u8;
                    if v_isSharedCheck_3184_ == 0 {
                        v___x_3176_ = v___x_3173_;
                        v_isShared_3177_ = v_isSharedCheck_3184_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3174_);
                        leanh::lean_dec(v___x_3173_);
                        v___x_3176_ = leanh::lean_box(0);
                        v_isShared_3177_ = v_isSharedCheck_3184_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3171_);
                    v_a_3185_ = leanh::lean_ctor_get(v___x_3173_, 0);
                    v_isSharedCheck_3192_ = (!leanh::lean_is_exclusive(v___x_3173_)) as u8;
                    if v_isSharedCheck_3192_ == 0 {
                        v___x_3187_ = v___x_3173_;
                        v_isShared_3188_ = v_isSharedCheck_3192_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3185_);
                        leanh::lean_dec(v___x_3173_);
                        v___x_3187_ = leanh::lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3192_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3172_ == 0 {
                    leanh::lean_ctor_set(v___x_3171_, 0, v_a_3174_);
                    v___x_3179_ = v___x_3171_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3183_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3177_ == 0 {
                    leanh::lean_ctor_set(v___x_3176_, 0, v___x_3179_);
                    v___x_3181_ = v___x_3176_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3181_;
            }
            11 => {
                if v_isShared_3188_ == 0 {
                    v___x_3190_ = v___x_3187_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
                    v___x_3190_ = v_reuseFailAlloc_3191_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3190_;
            }
            13 => {
                v___x_3201_ = leanh::lean_box(0);
                v___x_3202_ =
                    l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(
                        v_params_3196_,
                        v___x_3201_,
                        v_a_3139_,
                        v_a_3140_,
                        v_a_3141_,
                        v_a_3142_,
                    );
                if leanh::lean_obj_tag(v___x_3202_) == 0 {
                    v_a_3203_ = leanh::lean_ctor_get(v___x_3202_, 0);
                    leanh::lean_inc(v_a_3203_);
                    leanh::lean_dec_ref_known(v___x_3202_, 1);
                    v___x_3204_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
                            v_fields_3197_,
                            v___x_3201_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                        );
                    if leanh::lean_obj_tag(v___x_3204_) == 0 {
                        v_a_3205_ = leanh::lean_ctor_get(v___x_3204_, 0);
                        v_isSharedCheck_3215_ =
                            (!leanh::lean_is_exclusive(v___x_3204_)) as u8;
                        if v_isSharedCheck_3215_ == 0 {
                            v___x_3207_ = v___x_3204_;
                            v_isShared_3208_ = v_isSharedCheck_3215_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3205_);
                            leanh::lean_dec(v___x_3204_);
                            v___x_3207_ = leanh::lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3215_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3203_);
                        leanh::lean_del_object(v___x_3199_);
                        leanh::lean_dec(v_us_3195_);
                        leanh::lean_dec(v_ctorName_3194_);
                        v_a_3216_ = leanh::lean_ctor_get(v___x_3204_, 0);
                        v_isSharedCheck_3223_ =
                            (!leanh::lean_is_exclusive(v___x_3204_)) as u8;
                        if v_isSharedCheck_3223_ == 0 {
                            v___x_3218_ = v___x_3204_;
                            v_isShared_3219_ = v_isSharedCheck_3223_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3216_);
                            leanh::lean_dec(v___x_3204_);
                            v___x_3218_ = leanh::lean_box(0);
                            v_isShared_3219_ = v_isSharedCheck_3223_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3199_);
                    leanh::lean_dec(v_fields_3197_);
                    leanh::lean_dec(v_us_3195_);
                    leanh::lean_dec(v_ctorName_3194_);
                    v_a_3224_ = leanh::lean_ctor_get(v___x_3202_, 0);
                    v_isSharedCheck_3231_ = (!leanh::lean_is_exclusive(v___x_3202_)) as u8;
                    if v_isSharedCheck_3231_ == 0 {
                        v___x_3226_ = v___x_3202_;
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3224_);
                        leanh::lean_dec(v___x_3202_);
                        v___x_3226_ = leanh::lean_box(0);
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 19;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3200_ == 0 {
                    leanh::lean_ctor_set(v___x_3199_, 3, v_a_3205_);
                    leanh::lean_ctor_set(v___x_3199_, 2, v_a_3203_);
                    v___x_3210_ = v___x_3199_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_ctorName_3194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_us_3195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_a_3203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_a_3205_);
                    v___x_3210_ = v_reuseFailAlloc_3214_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3208_ == 0 {
                    leanh::lean_ctor_set(v___x_3207_, 0, v___x_3210_);
                    v___x_3212_ = v___x_3207_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
                    v___x_3212_ = v_reuseFailAlloc_3213_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3212_;
            }
            17 => {
                if v_isShared_3219_ == 0 {
                    v___x_3221_ = v___x_3218_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3221_;
            }
            19 => {
                if v_isShared_3227_ == 0 {
                    v___x_3229_ = v___x_3226_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
                    v___x_3229_ = v_reuseFailAlloc_3230_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3229_;
            }
            21 => {
                v___x_3239_ = l_Lean_Meta_Match_instantiatePatternMVars(
                    v_p_3234_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_,
                );
                if leanh::lean_obj_tag(v___x_3239_) == 0 {
                    v_a_3240_ = leanh::lean_ctor_get(v___x_3239_, 0);
                    v_isSharedCheck_3250_ = (!leanh::lean_is_exclusive(v___x_3239_)) as u8;
                    if v_isSharedCheck_3250_ == 0 {
                        v___x_3242_ = v___x_3239_;
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3240_);
                        leanh::lean_dec(v___x_3239_);
                        v___x_3242_ = leanh::lean_box(0);
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 22;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3237_);
                    leanh::lean_dec(v_hId_3235_);
                    leanh::lean_dec(v_varId_3233_);
                    return v___x_3239_;
                }
            }
            22 => {
                if v_isShared_3238_ == 0 {
                    leanh::lean_ctor_set(v___x_3237_, 1, v_a_3240_);
                    v___x_3245_ = v___x_3237_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3249_ = leanh::lean_alloc_ctor(5, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_varId_3233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_a_3240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_hId_3235_);
                    v___x_3245_ = v_reuseFailAlloc_3249_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3243_ == 0 {
                    leanh::lean_ctor_set(v___x_3242_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3242_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3247_;
            }
            25 => {
                v___x_3257_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_3252_, v_a_3140_);
                if leanh::lean_obj_tag(v___x_3257_) == 0 {
                    v_a_3258_ = leanh::lean_ctor_get(v___x_3257_, 0);
                    leanh::lean_inc(v_a_3258_);
                    leanh::lean_dec_ref_known(v___x_3257_, 1);
                    v___x_3259_ = leanh::lean_box(0);
                    v___x_3260_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
                            v_xs_3253_,
                            v___x_3259_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                        );
                    if leanh::lean_obj_tag(v___x_3260_) == 0 {
                        v_a_3261_ = leanh::lean_ctor_get(v___x_3260_, 0);
                        v_isSharedCheck_3271_ =
                            (!leanh::lean_is_exclusive(v___x_3260_)) as u8;
                        if v_isSharedCheck_3271_ == 0 {
                            v___x_3263_ = v___x_3260_;
                            v_isShared_3264_ = v_isSharedCheck_3271_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3261_);
                            leanh::lean_dec(v___x_3260_);
                            v___x_3263_ = leanh::lean_box(0);
                            v_isShared_3264_ = v_isSharedCheck_3271_;
                            state = 26;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3258_);
                        leanh::lean_del_object(v___x_3255_);
                        v_a_3272_ = leanh::lean_ctor_get(v___x_3260_, 0);
                        v_isSharedCheck_3279_ =
                            (!leanh::lean_is_exclusive(v___x_3260_)) as u8;
                        if v_isSharedCheck_3279_ == 0 {
                            v___x_3274_ = v___x_3260_;
                            v_isShared_3275_ = v_isSharedCheck_3279_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3272_);
                            leanh::lean_dec(v___x_3260_);
                            v___x_3274_ = leanh::lean_box(0);
                            v_isShared_3275_ = v_isSharedCheck_3279_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3255_);
                    leanh::lean_dec(v_xs_3253_);
                    v_a_3280_ = leanh::lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3287_ = (!leanh::lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3282_ = v___x_3257_;
                        v_isShared_3283_ = v_isSharedCheck_3287_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3280_);
                        leanh::lean_dec(v___x_3257_);
                        v___x_3282_ = leanh::lean_box(0);
                        v_isShared_3283_ = v_isSharedCheck_3287_;
                        state = 31;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_3256_ == 0 {
                    leanh::lean_ctor_set(v___x_3255_, 1, v_a_3261_);
                    leanh::lean_ctor_set(v___x_3255_, 0, v_a_3258_);
                    v___x_3266_ = v___x_3255_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_a_3261_);
                    v___x_3266_ = v_reuseFailAlloc_3270_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3264_ == 0 {
                    leanh::lean_ctor_set(v___x_3263_, 0, v___x_3266_);
                    v___x_3268_ = v___x_3263_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
                    v___x_3268_ = v_reuseFailAlloc_3269_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3268_;
            }
            29 => {
                if v_isShared_3275_ == 0 {
                    v___x_3277_ = v___x_3274_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3278_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
                    v___x_3277_ = v_reuseFailAlloc_3278_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3277_;
            }
            31 => {
                if v_isShared_3283_ == 0 {
                    v___x_3285_ = v___x_3282_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
                    v___x_3285_ = v_reuseFailAlloc_3286_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
    mut v_x_3290_: *mut leanh::LeanObject,
    mut v_x_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
    mut v___y_3293_: *mut leanh::LeanObject,
    mut v___y_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3303_: u8 = 0;
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3290_) == 0 {
                    v___x_3297_ = l_List_reverse___redArg(v_x_3291_);
                    v___x_3298_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3298_, 0, v___x_3297_);
                    return v___x_3298_;
                } else {
                    v_head_3299_ = leanh::lean_ctor_get(v_x_3290_, 0);
                    v_tail_3300_ = leanh::lean_ctor_get(v_x_3290_, 1);
                    v_isSharedCheck_3318_ = (!leanh::lean_is_exclusive(v_x_3290_)) as u8;
                    if v_isSharedCheck_3318_ == 0 {
                        v___x_3302_ = v_x_3290_;
                        v_isShared_3303_ = v_isSharedCheck_3318_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3300_);
                        leanh::lean_inc(v_head_3299_);
                        leanh::lean_dec(v_x_3290_);
                        v___x_3302_ = leanh::lean_box(0);
                        v_isShared_3303_ = v_isSharedCheck_3318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3304_ = l_Lean_Meta_Match_instantiatePatternMVars(
                    v_head_3299_,
                    v___y_3292_,
                    v___y_3293_,
                    v___y_3294_,
                    v___y_3295_,
                );
                if leanh::lean_obj_tag(v___x_3304_) == 0 {
                    v_a_3305_ = leanh::lean_ctor_get(v___x_3304_, 0);
                    leanh::lean_inc(v_a_3305_);
                    leanh::lean_dec_ref_known(v___x_3304_, 1);
                    if v_isShared_3303_ == 0 {
                        leanh::lean_ctor_set(v___x_3302_, 1, v_x_3291_);
                        leanh::lean_ctor_set(v___x_3302_, 0, v_a_3305_);
                        v___x_3307_ = v___x_3302_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3309_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3305_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_x_3291_);
                        v___x_3307_ = v_reuseFailAlloc_3309_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3302_);
                    leanh::lean_dec(v_tail_3300_);
                    leanh::lean_dec(v_x_3291_);
                    v_a_3310_ = leanh::lean_ctor_get(v___x_3304_, 0);
                    v_isSharedCheck_3317_ = (!leanh::lean_is_exclusive(v___x_3304_)) as u8;
                    if v_isSharedCheck_3317_ == 0 {
                        v___x_3312_ = v___x_3304_;
                        v_isShared_3313_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3310_);
                        leanh::lean_dec(v___x_3304_);
                        v___x_3312_ = leanh::lean_box(0);
                        v_isShared_3313_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3290_ = v_tail_3300_;
                v_x_3291_ = v___x_3307_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3313_ == 0 {
                    v___x_3315_ = v___x_3312_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
                    v___x_3315_ = v_reuseFailAlloc_3316_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(
    mut v_x_3319_: *mut leanh::LeanObject,
    mut v_x_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
    mut v___y_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3326_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
        v_x_3319_,
        v_x_3320_,
        v___y_3321_,
        v___y_3322_,
        v___y_3323_,
        v___y_3324_,
    );
    leanh::lean_dec(v___y_3324_);
    leanh::lean_dec_ref(v___y_3323_);
    leanh::lean_dec(v___y_3322_);
    leanh::lean_dec_ref(v___y_3321_);
    return v_res_3326_;
}
pub unsafe fn l_Lean_Meta_Match_instantiatePatternMVars___boxed(
    mut v_x_3327_: *mut leanh::LeanObject,
    mut v_a_3328_: *mut leanh::LeanObject,
    mut v_a_3329_: *mut leanh::LeanObject,
    mut v_a_3330_: *mut leanh::LeanObject,
    mut v_a_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Meta_Match_instantiatePatternMVars(
        v_x_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_,
    );
    leanh::lean_dec(v_a_3331_);
    leanh::lean_dec_ref(v_a_3330_);
    leanh::lean_dec(v_a_3329_);
    leanh::lean_dec_ref(v_a_3328_);
    return v_res_3333_;
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(
    mut v_as_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_3339_) == 0 {
                    v___x_3346_ = leanh::lean_box(0);
                    v___x_3347_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3347_, 0, v___x_3346_);
                    return v___x_3347_;
                } else {
                    v_head_3348_ = leanh::lean_ctor_get(v_as_3339_, 0);
                    leanh::lean_inc(v_head_3348_);
                    v_tail_3349_ = leanh::lean_ctor_get(v_as_3339_, 1);
                    leanh::lean_inc(v_tail_3349_);
                    leanh::lean_dec_ref_known(v_as_3339_, 2);
                    v___x_3350_ = l_Lean_LocalDecl_collectFVars(
                        v_head_3348_,
                        v___y_3340_,
                        v___y_3341_,
                        v___y_3342_,
                        v___y_3343_,
                        v___y_3344_,
                    );
                    if leanh::lean_obj_tag(v___x_3350_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3350_, 1);
                        v_as_3339_ = v_tail_3349_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_3349_);
                        return v___x_3350_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(
    mut v_as_3352_: *mut leanh::LeanObject,
    mut v___y_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
    mut v___y_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(
        v_as_3352_,
        v___y_3353_,
        v___y_3354_,
        v___y_3355_,
        v___y_3356_,
        v___y_3357_,
    );
    leanh::lean_dec(v___y_3357_);
    leanh::lean_dec_ref(v___y_3356_);
    leanh::lean_dec(v___y_3355_);
    leanh::lean_dec_ref(v___y_3354_);
    leanh::lean_dec(v___y_3353_);
    return v_res_3359_;
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(
    mut v_as_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_3360_) == 0 {
                    v___x_3367_ = leanh::lean_box(0);
                    v___x_3368_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3368_, 0, v___x_3367_);
                    return v___x_3368_;
                } else {
                    v_head_3369_ = leanh::lean_ctor_get(v_as_3360_, 0);
                    leanh::lean_inc(v_head_3369_);
                    v_tail_3370_ = leanh::lean_ctor_get(v_as_3360_, 1);
                    leanh::lean_inc(v_tail_3370_);
                    leanh::lean_dec_ref_known(v_as_3360_, 2);
                    v___x_3371_ = l_Lean_Meta_Match_Pattern_collectFVars(
                        v_head_3369_,
                        v___y_3361_,
                        v___y_3362_,
                        v___y_3363_,
                        v___y_3364_,
                        v___y_3365_,
                    );
                    if leanh::lean_obj_tag(v___x_3371_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3371_, 1);
                        v_as_3360_ = v_tail_3370_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_3370_);
                        return v___x_3371_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(
    mut v_as_3373_: *mut leanh::LeanObject,
    mut v___y_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3380_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(
        v_as_3373_,
        v___y_3374_,
        v___y_3375_,
        v___y_3376_,
        v___y_3377_,
        v___y_3378_,
    );
    leanh::lean_dec(v___y_3378_);
    leanh::lean_dec_ref(v___y_3377_);
    leanh::lean_dec(v___y_3376_);
    leanh::lean_dec_ref(v___y_3375_);
    leanh::lean_dec(v___y_3374_);
    return v_res_3380_;
}
pub unsafe fn l_Lean_Meta_Match_AltLHS_collectFVars(
    mut v_altLHS_3381_: *mut leanh::LeanObject,
    mut v_a_3382_: *mut leanh::LeanObject,
    mut v_a_3383_: *mut leanh::LeanObject,
    mut v_a_3384_: *mut leanh::LeanObject,
    mut v_a_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarDecls_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fvarDecls_3388_ = leanh::lean_ctor_get(v_altLHS_3381_, 1);
    leanh::lean_inc(v_fvarDecls_3388_);
    v_patterns_3389_ = leanh::lean_ctor_get(v_altLHS_3381_, 2);
    leanh::lean_inc(v_patterns_3389_);
    leanh::lean_dec_ref(v_altLHS_3381_);
    v___x_3390_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(
        v_fvarDecls_3388_,
        v_a_3382_,
        v_a_3383_,
        v_a_3384_,
        v_a_3385_,
        v_a_3386_,
    );
    if leanh::lean_obj_tag(v___x_3390_) == 0 {
        let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3390_, 1);
        v___x_3391_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(
            v_patterns_3389_,
            v_a_3382_,
            v_a_3383_,
            v_a_3384_,
            v_a_3385_,
            v_a_3386_,
        );
        return v___x_3391_;
    } else {
        leanh::lean_dec(v_patterns_3389_);
        return v___x_3390_;
    }
}
pub unsafe fn l_Lean_Meta_Match_AltLHS_collectFVars___boxed(
    mut v_altLHS_3392_: *mut leanh::LeanObject,
    mut v_a_3393_: *mut leanh::LeanObject,
    mut v_a_3394_: *mut leanh::LeanObject,
    mut v_a_3395_: *mut leanh::LeanObject,
    mut v_a_3396_: *mut leanh::LeanObject,
    mut v_a_3397_: *mut leanh::LeanObject,
    mut v_a_3398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3399_ = l_Lean_Meta_Match_AltLHS_collectFVars(
        v_altLHS_3392_,
        v_a_3393_,
        v_a_3394_,
        v_a_3395_,
        v_a_3396_,
        v_a_3397_,
    );
    leanh::lean_dec(v_a_3397_);
    leanh::lean_dec_ref(v_a_3396_);
    leanh::lean_dec(v_a_3395_);
    leanh::lean_dec_ref(v_a_3394_);
    leanh::lean_dec(v_a_3393_);
    return v_res_3399_;
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(
    mut v_localDecl_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_index_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_3407_: u8 = 0;
    let mut v_kind_3408_: u8 = 0;
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut v_index_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_3430_: u8 = 0;
    let mut v_kind_3431_: u8 = 0;
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v_isSharedCheck_3449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_localDecl_3400_) == 0 {
                    v_index_3403_ = leanh::lean_ctor_get(v_localDecl_3400_, 0);
                    v_fvarId_3404_ = leanh::lean_ctor_get(v_localDecl_3400_, 1);
                    v_userName_3405_ = leanh::lean_ctor_get(v_localDecl_3400_, 2);
                    v_type_3406_ = leanh::lean_ctor_get(v_localDecl_3400_, 3);
                    v_bi_3407_ = leanh::lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v_kind_3408_ = leanh::lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_3424_ =
                        (!leanh::lean_is_exclusive(v_localDecl_3400_)) as u8;
                    if v_isSharedCheck_3424_ == 0 {
                        v___x_3410_ = v_localDecl_3400_;
                        v_isShared_3411_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_type_3406_);
                        leanh::lean_inc(v_userName_3405_);
                        leanh::lean_inc(v_fvarId_3404_);
                        leanh::lean_inc(v_index_3403_);
                        leanh::lean_dec(v_localDecl_3400_);
                        v___x_3410_ = leanh::lean_box(0);
                        v_isShared_3411_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_index_3425_ = leanh::lean_ctor_get(v_localDecl_3400_, 0);
                    v_fvarId_3426_ = leanh::lean_ctor_get(v_localDecl_3400_, 1);
                    v_userName_3427_ = leanh::lean_ctor_get(v_localDecl_3400_, 2);
                    v_type_3428_ = leanh::lean_ctor_get(v_localDecl_3400_, 3);
                    v_value_3429_ = leanh::lean_ctor_get(v_localDecl_3400_, 4);
                    v_nondep_3430_ = leanh::lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v_kind_3431_ = leanh::lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_3449_ =
                        (!leanh::lean_is_exclusive(v_localDecl_3400_)) as u8;
                    if v_isSharedCheck_3449_ == 0 {
                        v___x_3433_ = v_localDecl_3400_;
                        v_isShared_3434_ = v_isSharedCheck_3449_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3429_);
                        leanh::lean_inc(v_type_3428_);
                        leanh::lean_inc(v_userName_3427_);
                        leanh::lean_inc(v_fvarId_3426_);
                        leanh::lean_inc(v_index_3425_);
                        leanh::lean_dec(v_localDecl_3400_);
                        v___x_3433_ = leanh::lean_box(0);
                        v_isShared_3434_ = v_isSharedCheck_3449_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3412_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_3406_, v___y_3401_);
                v_a_3413_ = leanh::lean_ctor_get(v___x_3412_, 0);
                v_isSharedCheck_3423_ = (!leanh::lean_is_exclusive(v___x_3412_)) as u8;
                if v_isSharedCheck_3423_ == 0 {
                    v___x_3415_ = v___x_3412_;
                    v_isShared_3416_ = v_isSharedCheck_3423_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3413_);
                    leanh::lean_dec(v___x_3412_);
                    v___x_3415_ = leanh::lean_box(0);
                    v_isShared_3416_ = v_isSharedCheck_3423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3411_ == 0 {
                    leanh::lean_ctor_set(v___x_3410_, 3, v_a_3413_);
                    v___x_3418_ = v___x_3410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3422_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_index_3403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_fvarId_3404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_userName_3405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 3, v_a_3413_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3422_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_bi_3407_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3422_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v_kind_3408_,
                    );
                    v___x_3418_ = v_reuseFailAlloc_3422_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3416_ == 0 {
                    leanh::lean_ctor_set(v___x_3415_, 0, v___x_3418_);
                    v___x_3420_ = v___x_3415_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
                    v___x_3420_ = v_reuseFailAlloc_3421_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3420_;
            }
            5 => {
                v___x_3435_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_3428_, v___y_3401_);
                v_a_3436_ = leanh::lean_ctor_get(v___x_3435_, 0);
                leanh::lean_inc(v_a_3436_);
                leanh::lean_dec_ref(v___x_3435_);
                v___x_3437_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_3429_, v___y_3401_);
                v_a_3438_ = leanh::lean_ctor_get(v___x_3437_, 0);
                v_isSharedCheck_3448_ = (!leanh::lean_is_exclusive(v___x_3437_)) as u8;
                if v_isSharedCheck_3448_ == 0 {
                    v___x_3440_ = v___x_3437_;
                    v_isShared_3441_ = v_isSharedCheck_3448_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3438_);
                    leanh::lean_dec(v___x_3437_);
                    v___x_3440_ = leanh::lean_box(0);
                    v_isShared_3441_ = v_isSharedCheck_3448_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3434_ == 0 {
                    leanh::lean_ctor_set(v___x_3433_, 4, v_a_3438_);
                    leanh::lean_ctor_set(v___x_3433_, 3, v_a_3436_);
                    v___x_3443_ = v___x_3433_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = leanh::lean_alloc_ctor(1, 5, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_index_3425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_fvarId_3426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_userName_3427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_a_3436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_a_3438_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3447_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v_nondep_3430_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3447_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v_kind_3431_,
                    );
                    v___x_3443_ = v_reuseFailAlloc_3447_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3441_ == 0 {
                    leanh::lean_ctor_set(v___x_3440_, 0, v___x_3443_);
                    v___x_3445_ = v___x_3440_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
                    v___x_3445_ = v_reuseFailAlloc_3446_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(
    mut v_localDecl_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3453_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_3450_, v___y_3451_);
    leanh::lean_dec(v___y_3451_);
    return v_res_3453_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(
    mut v_x_3454_: *mut leanh::LeanObject,
    mut v_x_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3454_) == 0 {
                    v___x_3461_ = l_List_reverse___redArg(v_x_3455_);
                    v___x_3462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3462_, 0, v___x_3461_);
                    return v___x_3462_;
                } else {
                    v_head_3463_ = leanh::lean_ctor_get(v_x_3454_, 0);
                    v_tail_3464_ = leanh::lean_ctor_get(v_x_3454_, 1);
                    v_isSharedCheck_3482_ = (!leanh::lean_is_exclusive(v_x_3454_)) as u8;
                    if v_isSharedCheck_3482_ == 0 {
                        v___x_3466_ = v_x_3454_;
                        v_isShared_3467_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3464_);
                        leanh::lean_inc(v_head_3463_);
                        leanh::lean_dec(v_x_3454_);
                        v___x_3466_ = leanh::lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3468_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_3463_, v___y_3457_);
                if leanh::lean_obj_tag(v___x_3468_) == 0 {
                    v_a_3469_ = leanh::lean_ctor_get(v___x_3468_, 0);
                    leanh::lean_inc(v_a_3469_);
                    leanh::lean_dec_ref_known(v___x_3468_, 1);
                    if v_isShared_3467_ == 0 {
                        leanh::lean_ctor_set(v___x_3466_, 1, v_x_3455_);
                        leanh::lean_ctor_set(v___x_3466_, 0, v_a_3469_);
                        v___x_3471_ = v___x_3466_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3473_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3469_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_x_3455_);
                        v___x_3471_ = v_reuseFailAlloc_3473_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3466_);
                    leanh::lean_dec(v_tail_3464_);
                    leanh::lean_dec(v_x_3455_);
                    v_a_3474_ = leanh::lean_ctor_get(v___x_3468_, 0);
                    v_isSharedCheck_3481_ = (!leanh::lean_is_exclusive(v___x_3468_)) as u8;
                    if v_isSharedCheck_3481_ == 0 {
                        v___x_3476_ = v___x_3468_;
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3474_);
                        leanh::lean_dec(v___x_3468_);
                        v___x_3476_ = leanh::lean_box(0);
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3454_ = v_tail_3464_;
                v_x_3455_ = v___x_3471_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3477_ == 0 {
                    v___x_3479_ = v___x_3476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3480_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
                    v___x_3479_ = v_reuseFailAlloc_3480_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(
    mut v_x_3483_: *mut leanh::LeanObject,
    mut v_x_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
    mut v___y_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3490_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(
        v_x_3483_,
        v_x_3484_,
        v___y_3485_,
        v___y_3486_,
        v___y_3487_,
        v___y_3488_,
    );
    leanh::lean_dec(v___y_3488_);
    leanh::lean_dec_ref(v___y_3487_);
    leanh::lean_dec(v___y_3486_);
    leanh::lean_dec_ref(v___y_3485_);
    return v_res_3490_;
}
pub unsafe fn l_Lean_Meta_Match_instantiateAltLHSMVars(
    mut v_altLHS_3491_: *mut leanh::LeanObject,
    mut v_a_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
    mut v_a_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3502_: u8 = 0;
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_a_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_a_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3529_: u8 = 0;
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3497_ = leanh::lean_ctor_get(v_altLHS_3491_, 0);
                v_fvarDecls_3498_ = leanh::lean_ctor_get(v_altLHS_3491_, 1);
                v_patterns_3499_ = leanh::lean_ctor_get(v_altLHS_3491_, 2);
                v_isSharedCheck_3534_ = (!leanh::lean_is_exclusive(v_altLHS_3491_)) as u8;
                if v_isSharedCheck_3534_ == 0 {
                    v___x_3501_ = v_altLHS_3491_;
                    v_isShared_3502_ = v_isSharedCheck_3534_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_patterns_3499_);
                    leanh::lean_inc(v_fvarDecls_3498_);
                    leanh::lean_inc(v_ref_3497_);
                    leanh::lean_dec(v_altLHS_3491_);
                    v___x_3501_ = leanh::lean_box(0);
                    v_isShared_3502_ = v_isSharedCheck_3534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3503_ = leanh::lean_box(0);
                v___x_3504_ =
                    l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(
                        v_fvarDecls_3498_,
                        v___x_3503_,
                        v_a_3492_,
                        v_a_3493_,
                        v_a_3494_,
                        v_a_3495_,
                    );
                if leanh::lean_obj_tag(v___x_3504_) == 0 {
                    v_a_3505_ = leanh::lean_ctor_get(v___x_3504_, 0);
                    leanh::lean_inc(v_a_3505_);
                    leanh::lean_dec_ref_known(v___x_3504_, 1);
                    v___x_3506_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
                            v_patterns_3499_,
                            v___x_3503_,
                            v_a_3492_,
                            v_a_3493_,
                            v_a_3494_,
                            v_a_3495_,
                        );
                    if leanh::lean_obj_tag(v___x_3506_) == 0 {
                        v_a_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                        v_isSharedCheck_3517_ =
                            (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                        if v_isSharedCheck_3517_ == 0 {
                            v___x_3509_ = v___x_3506_;
                            v_isShared_3510_ = v_isSharedCheck_3517_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3507_);
                            leanh::lean_dec(v___x_3506_);
                            v___x_3509_ = leanh::lean_box(0);
                            v_isShared_3510_ = v_isSharedCheck_3517_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3505_);
                        leanh::lean_del_object(v___x_3501_);
                        leanh::lean_dec(v_ref_3497_);
                        v_a_3518_ = leanh::lean_ctor_get(v___x_3506_, 0);
                        v_isSharedCheck_3525_ =
                            (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                        if v_isSharedCheck_3525_ == 0 {
                            v___x_3520_ = v___x_3506_;
                            v_isShared_3521_ = v_isSharedCheck_3525_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3518_);
                            leanh::lean_dec(v___x_3506_);
                            v___x_3520_ = leanh::lean_box(0);
                            v_isShared_3521_ = v_isSharedCheck_3525_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3501_);
                    leanh::lean_dec(v_patterns_3499_);
                    leanh::lean_dec(v_ref_3497_);
                    v_a_3526_ = leanh::lean_ctor_get(v___x_3504_, 0);
                    v_isSharedCheck_3533_ = (!leanh::lean_is_exclusive(v___x_3504_)) as u8;
                    if v_isSharedCheck_3533_ == 0 {
                        v___x_3528_ = v___x_3504_;
                        v_isShared_3529_ = v_isSharedCheck_3533_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3526_);
                        leanh::lean_dec(v___x_3504_);
                        v___x_3528_ = leanh::lean_box(0);
                        v_isShared_3529_ = v_isSharedCheck_3533_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3502_ == 0 {
                    leanh::lean_ctor_set(v___x_3501_, 2, v_a_3507_);
                    leanh::lean_ctor_set(v___x_3501_, 1, v_a_3505_);
                    v___x_3512_ = v___x_3501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_ref_3497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_a_3505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_a_3507_);
                    v___x_3512_ = v_reuseFailAlloc_3516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3510_ == 0 {
                    leanh::lean_ctor_set(v___x_3509_, 0, v___x_3512_);
                    v___x_3514_ = v___x_3509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
                    v___x_3514_ = v_reuseFailAlloc_3515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3514_;
            }
            5 => {
                if v_isShared_3521_ == 0 {
                    v___x_3523_ = v___x_3520_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3523_;
            }
            7 => {
                if v_isShared_3529_ == 0 {
                    v___x_3531_ = v___x_3528_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(
    mut v_altLHS_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
    mut v_a_3539_: *mut leanh::LeanObject,
    mut v_a_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lean_Meta_Match_instantiateAltLHSMVars(
        v_altLHS_3535_,
        v_a_3536_,
        v_a_3537_,
        v_a_3538_,
        v_a_3539_,
    );
    leanh::lean_dec(v_a_3539_);
    leanh::lean_dec_ref(v_a_3538_);
    leanh::lean_dec(v_a_3537_);
    leanh::lean_dec_ref(v_a_3536_);
    return v_res_3541_;
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(
    mut v_localDecl_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_3542_, v___y_3544_);
    return v___x_3548_;
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(
    mut v_localDecl_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ =
        l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(
            v_localDecl_3549_,
            v___y_3550_,
            v___y_3551_,
            v___y_3552_,
            v___y_3553_,
        );
    leanh::lean_dec(v___y_3553_);
    leanh::lean_dec_ref(v___y_3552_);
    leanh::lean_dec(v___y_3551_);
    leanh::lean_dec_ref(v___y_3550_);
    return v_res_3555_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_Meta_Match_instInhabitedAlt_default___closed__0;
    v___x_3559_ = leanh::lean_box(0);
    v___x_3560_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once),
        _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2,
    );
    v___x_3561_ = leanh::lean_unsigned_to_nat(0);
    v___x_3562_ = leanh::lean_box(0);
    v___x_3563_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
    leanh::lean_ctor_set(v___x_3563_, 0, v___x_3562_);
    leanh::lean_ctor_set(v___x_3563_, 1, v___x_3561_);
    leanh::lean_ctor_set(v___x_3563_, 2, v___x_3560_);
    leanh::lean_ctor_set(v___x_3563_, 3, v___x_3559_);
    leanh::lean_ctor_set(v___x_3563_, 4, v___x_3559_);
    leanh::lean_ctor_set(v___x_3563_, 5, v___x_3559_);
    leanh::lean_ctor_set(v___x_3563_, 6, v___x_3558_);
    return v___x_3563_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedAlt_default() -> *mut leanh::LeanObject {
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3564_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedAlt_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once),
        _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1,
    );
    return v___x_3564_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedAlt() -> *mut leanh::LeanObject {
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3565_ = l_Lean_Meta_Match_instInhabitedAlt_default;
    return v___x_3565_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
    mut v_msgData_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3572_ = lean_st_ref_get(v___y_3570_);
    v_env_3573_ = leanh::lean_ctor_get(v___x_3572_, 0);
    leanh::lean_inc_ref(v_env_3573_);
    leanh::lean_dec(v___x_3572_);
    v___x_3574_ = lean_st_ref_get(v___y_3568_);
    v_mctx_3575_ = leanh::lean_ctor_get(v___x_3574_, 0);
    leanh::lean_inc_ref(v_mctx_3575_);
    leanh::lean_dec(v___x_3574_);
    v_lctx_3576_ = leanh::lean_ctor_get(v___y_3567_, 2);
    v_options_3577_ = leanh::lean_ctor_get(v___y_3569_, 2);
    leanh::lean_inc_ref(v_options_3577_);
    leanh::lean_inc_ref(v_lctx_3576_);
    v___x_3578_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3578_, 0, v_env_3573_);
    leanh::lean_ctor_set(v___x_3578_, 1, v_mctx_3575_);
    leanh::lean_ctor_set(v___x_3578_, 2, v_lctx_3576_);
    leanh::lean_ctor_set(v___x_3578_, 3, v_options_3577_);
    v___x_3579_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
    leanh::lean_ctor_set(v___x_3579_, 1, v_msgData_3566_);
    v___x_3580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3580_, 0, v___x_3579_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(
    mut v_msgData_3581_: *mut leanh::LeanObject,
    mut v___y_3582_: *mut leanh::LeanObject,
    mut v___y_3583_: *mut leanh::LeanObject,
    mut v___y_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3587_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
        v_msgData_3581_,
        v___y_3582_,
        v___y_3583_,
        v___y_3584_,
        v___y_3585_,
    );
    leanh::lean_dec(v___y_3585_);
    leanh::lean_dec_ref(v___y_3584_);
    leanh::lean_dec(v___y_3583_);
    leanh::lean_dec_ref(v___y_3582_);
    return v_res_3587_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(
    mut v_decls_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut v_a_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3595_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(
                    leanh::lean_box(0),
                    v_decls_3588_,
                    v_x_3589_,
                    v___y_3590_,
                    v___y_3591_,
                    v___y_3592_,
                    v___y_3593_,
                );
                if leanh::lean_obj_tag(v___x_3595_) == 0 {
                    v_a_3596_ = leanh::lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3603_ = (!leanh::lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3603_ == 0 {
                        v___x_3598_ = v___x_3595_;
                        v_isShared_3599_ = v_isSharedCheck_3603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3596_);
                        leanh::lean_dec(v___x_3595_);
                        v___x_3598_ = leanh::lean_box(0);
                        v_isShared_3599_ = v_isSharedCheck_3603_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3604_ = leanh::lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3611_ = (!leanh::lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3611_ == 0 {
                        v___x_3606_ = v___x_3595_;
                        v_isShared_3607_ = v_isSharedCheck_3611_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3604_);
                        leanh::lean_dec(v___x_3595_);
                        v___x_3606_ = leanh::lean_box(0);
                        v_isShared_3607_ = v_isSharedCheck_3611_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3599_ == 0 {
                    v___x_3601_ = v___x_3598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
                    v___x_3601_ = v_reuseFailAlloc_3602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3601_;
            }
            3 => {
                if v_isShared_3607_ == 0 {
                    v___x_3609_ = v___x_3606_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
                    v___x_3609_ = v_reuseFailAlloc_3610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(
    mut v_decls_3612_: *mut leanh::LeanObject,
    mut v_x_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
    mut v___y_3616_: *mut leanh::LeanObject,
    mut v___y_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_3612_, v_x_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
    leanh::lean_dec(v___y_3617_);
    leanh::lean_dec_ref(v___y_3616_);
    leanh::lean_dec(v___y_3615_);
    leanh::lean_dec_ref(v___y_3614_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(
    mut v_00_u03b1_3620_: *mut leanh::LeanObject,
    mut v_decls_3621_: *mut leanh::LeanObject,
    mut v_x_3622_: *mut leanh::LeanObject,
    mut v___y_3623_: *mut leanh::LeanObject,
    mut v___y_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_3621_, v_x_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(
    mut v_00_u03b1_3629_: *mut leanh::LeanObject,
    mut v_decls_3630_: *mut leanh::LeanObject,
    mut v_x_3631_: *mut leanh::LeanObject,
    mut v___y_3632_: *mut leanh::LeanObject,
    mut v___y_3633_: *mut leanh::LeanObject,
    mut v___y_3634_: *mut leanh::LeanObject,
    mut v___y_3635_: *mut leanh::LeanObject,
    mut v___y_3636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3637_ =
        l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(
            v_00_u03b1_3629_,
            v_decls_3630_,
            v_x_3631_,
            v___y_3632_,
            v___y_3633_,
            v___y_3634_,
            v___y_3635_,
        );
    leanh::lean_dec(v___y_3635_);
    leanh::lean_dec_ref(v___y_3634_);
    leanh::lean_dec(v___y_3633_);
    leanh::lean_dec_ref(v___y_3632_);
    return v_res_3637_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3639_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0;
    v___x_3640_ = l_Lean_stringToMessageData(v___x_3639_);
    return v___x_3640_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3642_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2;
    v___x_3643_ = l_Lean_stringToMessageData(v___x_3642_);
    return v___x_3643_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
    mut v_as_x27_3644_: *mut leanh::LeanObject,
    mut v_b_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3644_) == 0 {
                    v___x_3647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3647_, 0, v_b_3645_);
                    return v___x_3647_;
                } else {
                    v_head_3648_ = leanh::lean_ctor_get(v_as_x27_3644_, 0);
                    v_tail_3649_ = leanh::lean_ctor_get(v_as_x27_3644_, 1);
                    v_fst_3650_ = leanh::lean_ctor_get(v_head_3648_, 0);
                    v_snd_3651_ = leanh::lean_ctor_get(v_head_3648_, 1);
                    v___x_3652_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
                    v___x_3653_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3653_, 0, v_b_3645_);
                    leanh::lean_ctor_set(v___x_3653_, 1, v___x_3652_);
                    leanh::lean_inc(v_fst_3650_);
                    v___x_3654_ = l_Lean_MessageData_ofExpr(v_fst_3650_);
                    v___x_3655_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3655_, 0, v___x_3653_);
                    leanh::lean_ctor_set(v___x_3655_, 1, v___x_3654_);
                    v___x_3656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
                    v___x_3657_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3657_, 0, v___x_3655_);
                    leanh::lean_ctor_set(v___x_3657_, 1, v___x_3656_);
                    leanh::lean_inc(v_snd_3651_);
                    v___x_3658_ = l_Lean_MessageData_ofExpr(v_snd_3651_);
                    v___x_3659_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3659_, 0, v___x_3657_);
                    leanh::lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                    v_as_x27_3644_ = v_tail_3649_;
                    v_b_3645_ = v___x_3659_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(
    mut v_as_x27_3661_: *mut leanh::LeanObject,
    mut v_b_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3664_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
        v_as_x27_3661_,
        v_b_3662_,
    );
    leanh::lean_dec(v_as_x27_3661_);
    return v_res_3664_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData___lam__0(
    mut v_cnstrs_3665_: *mut leanh::LeanObject,
    mut v_msg_3666_: *mut leanh::LeanObject,
    mut v___y_3667_: *mut leanh::LeanObject,
    mut v___y_3668_: *mut leanh::LeanObject,
    mut v___y_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
        v_cnstrs_3665_,
        v_msg_3666_,
    );
    v_a_3673_ = leanh::lean_ctor_get(v___x_3672_, 0);
    leanh::lean_inc(v_a_3673_);
    leanh::lean_dec_ref(v___x_3672_);
    v___x_3674_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
        v_a_3673_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
    );
    return v___x_3674_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(
    mut v_cnstrs_3675_: *mut leanh::LeanObject,
    mut v_msg_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3682_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(
        v_cnstrs_3675_,
        v_msg_3676_,
        v___y_3677_,
        v___y_3678_,
        v___y_3679_,
        v___y_3680_,
    );
    leanh::lean_dec(v___y_3680_);
    leanh::lean_dec_ref(v___y_3679_);
    leanh::lean_dec(v___y_3678_);
    leanh::lean_dec_ref(v___y_3677_);
    leanh::lean_dec(v_cnstrs_3675_);
    return v_res_3682_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(
    mut v_a_3683_: *mut leanh::LeanObject,
    mut v_a_3684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3683_) == 0 {
                    v___x_3685_ = l_List_reverse___redArg(v_a_3684_);
                    return v___x_3685_;
                } else {
                    v_head_3686_ = leanh::lean_ctor_get(v_a_3683_, 0);
                    v_tail_3687_ = leanh::lean_ctor_get(v_a_3683_, 1);
                    v_isSharedCheck_3695_ = (!leanh::lean_is_exclusive(v_a_3683_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3689_ = v_a_3683_;
                        v_isShared_3690_ = v_isSharedCheck_3695_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3687_);
                        leanh::lean_inc(v_head_3686_);
                        leanh::lean_dec(v_a_3683_);
                        v___x_3689_ = leanh::lean_box(0);
                        v_isShared_3690_ = v_isSharedCheck_3695_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3690_ == 0 {
                    leanh::lean_ctor_set(v___x_3689_, 1, v_a_3684_);
                    v___x_3692_ = v___x_3689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_head_3686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_a_3684_);
                    v___x_3692_ = v_reuseFailAlloc_3694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3683_ = v_tail_3687_;
                v_a_3684_ = v___x_3692_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_a_3700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3699_) == 0 {
                    v___x_3701_ = l_List_reverse___redArg(v_a_3700_);
                    return v___x_3701_;
                } else {
                    v_head_3702_ = leanh::lean_ctor_get(v_a_3699_, 0);
                    v_tail_3703_ = leanh::lean_ctor_get(v_a_3699_, 1);
                    v_isSharedCheck_3720_ = (!leanh::lean_is_exclusive(v_a_3699_)) as u8;
                    if v_isSharedCheck_3720_ == 0 {
                        v___x_3705_ = v_a_3699_;
                        v_isShared_3706_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3703_);
                        leanh::lean_inc(v_head_3702_);
                        leanh::lean_dec(v_a_3699_);
                        v___x_3705_ = leanh::lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_head_3702_);
                v___x_3707_ = l_Lean_LocalDecl_toExpr(v_head_3702_);
                v___x_3708_ = l_Lean_MessageData_ofExpr(v___x_3707_);
                v___x_3709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
                v___x_3710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3710_, 0, v___x_3708_);
                leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
                v___x_3711_ = l_Lean_LocalDecl_type(v_head_3702_);
                leanh::lean_dec(v_head_3702_);
                v___x_3712_ = l_Lean_MessageData_ofExpr(v___x_3711_);
                v___x_3713_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3713_, 0, v___x_3710_);
                leanh::lean_ctor_set(v___x_3713_, 1, v___x_3712_);
                v___x_3714_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                );
                v___x_3715_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3715_, 0, v___x_3713_);
                leanh::lean_ctor_set(v___x_3715_, 1, v___x_3714_);
                if v_isShared_3706_ == 0 {
                    leanh::lean_ctor_set(v___x_3705_, 1, v_a_3700_);
                    leanh::lean_ctor_set(v___x_3705_, 0, v___x_3715_);
                    v___x_3717_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_a_3700_);
                    v___x_3717_ = v_reuseFailAlloc_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3699_ = v_tail_3703_;
                v_a_3700_ = v___x_3717_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3722_ = l_Lean_Meta_Match_Alt_toMessageData___closed__0;
    v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
    return v___x_3723_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ = l_Lean_Meta_Match_Alt_toMessageData___closed__2;
    v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
    return v___x_3726_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = l_Lean_Meta_Match_Alt_toMessageData___closed__4;
    v___x_3729_ = l_Lean_stringToMessageData(v___x_3728_);
    return v___x_3729_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3731_ = l_Lean_Meta_Match_Alt_toMessageData___closed__6;
    v___x_3732_ = l_Lean_stringToMessageData(v___x_3731_);
    return v___x_3732_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData(
    mut v_alt_3733_: *mut leanh::LeanObject,
    mut v_a_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rhs_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cnstrs_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rhs_3739_ = leanh::lean_ctor_get(v_alt_3733_, 2);
                leanh::lean_inc_ref(v_rhs_3739_);
                v_fvarDecls_3740_ = leanh::lean_ctor_get(v_alt_3733_, 3);
                leanh::lean_inc(v_fvarDecls_3740_);
                v_patterns_3741_ = leanh::lean_ctor_get(v_alt_3733_, 4);
                leanh::lean_inc(v_patterns_3741_);
                v_cnstrs_3742_ = leanh::lean_ctor_get(v_alt_3733_, 5);
                leanh::lean_inc(v_cnstrs_3742_);
                leanh::lean_dec_ref(v_alt_3733_);
                v___x_3758_ = l_List_isEmpty___redArg(v_fvarDecls_3740_);
                if v___x_3758_ == 0 {
                    v___x_3759_ = leanh::lean_box(0);
                    leanh::lean_inc(v_fvarDecls_3740_);
                    v___x_3760_ =
                        l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(
                            v_fvarDecls_3740_,
                            v___x_3759_,
                        );
                    v___x_3761_ = l_Lean_MessageData_ofList(v___x_3760_);
                    v___x_3762_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Alt_toMessageData___closed__5_once
                        ),
                        _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5,
                    );
                    v___x_3763_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3763_, 0, v___x_3761_);
                    leanh::lean_ctor_set(v___x_3763_, 1, v___x_3762_);
                    v___y_3744_ = v___x_3763_;
                    state = 1;
                    continue;
                } else {
                    v___x_3764_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Alt_toMessageData___closed__7_once
                        ),
                        _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7,
                    );
                    v___y_3744_ = v___x_3764_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3745_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__1_once),
                    _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1,
                );
                v___x_3746_ = leanh::lean_box(0);
                v___x_3747_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(
                        v_patterns_3741_,
                        v___x_3746_,
                    );
                v___x_3748_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(
                    v___x_3747_,
                    v___x_3746_,
                );
                v___x_3749_ = l_Lean_MessageData_ofList(v___x_3748_);
                v___x_3750_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3750_, 0, v___x_3745_);
                leanh::lean_ctor_set(v___x_3750_, 1, v___x_3749_);
                v___x_3751_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__3_once),
                    _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3,
                );
                v___x_3752_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3752_, 0, v___x_3750_);
                leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
                v___x_3753_ = l_Lean_MessageData_ofExpr(v_rhs_3739_);
                v___x_3754_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3754_, 0, v___x_3752_);
                leanh::lean_ctor_set(v___x_3754_, 1, v___x_3753_);
                v_msg_3755_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msg_3755_, 0, v___y_3744_);
                leanh::lean_ctor_set(v_msg_3755_, 1, v___x_3754_);
                v___f_3756_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_3756_, 0, v_cnstrs_3742_);
                leanh::lean_closure_set(v___f_3756_, 1, v_msg_3755_);
                v___x_3757_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_fvarDecls_3740_, v___f_3756_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
                return v___x_3757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData___boxed(
    mut v_alt_3765_: *mut leanh::LeanObject,
    mut v_a_3766_: *mut leanh::LeanObject,
    mut v_a_3767_: *mut leanh::LeanObject,
    mut v_a_3768_: *mut leanh::LeanObject,
    mut v_a_3769_: *mut leanh::LeanObject,
    mut v_a_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l_Lean_Meta_Match_Alt_toMessageData(
        v_alt_3765_,
        v_a_3766_,
        v_a_3767_,
        v_a_3768_,
        v_a_3769_,
    );
    leanh::lean_dec(v_a_3769_);
    leanh::lean_dec_ref(v_a_3768_);
    leanh::lean_dec(v_a_3767_);
    leanh::lean_dec_ref(v_a_3766_);
    return v_res_3771_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(
    mut v_as_3772_: *mut leanh::LeanObject,
    mut v_as_x27_3773_: *mut leanh::LeanObject,
    mut v_b_3774_: *mut leanh::LeanObject,
    mut v_a_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3781_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
        v_as_x27_3773_,
        v_b_3774_,
    );
    return v___x_3781_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(
    mut v_as_3782_: *mut leanh::LeanObject,
    mut v_as_x27_3783_: *mut leanh::LeanObject,
    mut v_b_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
    mut v___y_3787_: *mut leanh::LeanObject,
    mut v___y_3788_: *mut leanh::LeanObject,
    mut v___y_3789_: *mut leanh::LeanObject,
    mut v___y_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(
        v_as_3782_,
        v_as_x27_3783_,
        v_b_3784_,
        v_a_3785_,
        v___y_3786_,
        v___y_3787_,
        v___y_3788_,
        v___y_3789_,
    );
    leanh::lean_dec(v___y_3789_);
    leanh::lean_dec_ref(v___y_3788_);
    leanh::lean_dec(v___y_3787_);
    leanh::lean_dec_ref(v___y_3786_);
    leanh::lean_dec(v_as_x27_3783_);
    leanh::lean_dec(v_as_3782_);
    return v_res_3791_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(
    mut v_s_3792_: *mut leanh::LeanObject,
    mut v_a_3793_: *mut leanh::LeanObject,
    mut v_a_3794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3793_) == 0 {
                    leanh::lean_dec(v_s_3792_);
                    v___x_3795_ = l_List_reverse___redArg(v_a_3794_);
                    return v___x_3795_;
                } else {
                    v_head_3796_ = leanh::lean_ctor_get(v_a_3793_, 0);
                    v_tail_3797_ = leanh::lean_ctor_get(v_a_3793_, 1);
                    v_isSharedCheck_3806_ = (!leanh::lean_is_exclusive(v_a_3793_)) as u8;
                    if v_isSharedCheck_3806_ == 0 {
                        v___x_3799_ = v_a_3793_;
                        v_isShared_3800_ = v_isSharedCheck_3806_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3797_);
                        leanh::lean_inc(v_head_3796_);
                        leanh::lean_dec(v_a_3793_);
                        v___x_3799_ = leanh::lean_box(0);
                        v_isShared_3800_ = v_isSharedCheck_3806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_s_3792_);
                v___x_3801_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_3792_, v_head_3796_);
                if v_isShared_3800_ == 0 {
                    leanh::lean_ctor_set(v___x_3799_, 1, v_a_3794_);
                    leanh::lean_ctor_set(v___x_3799_, 0, v___x_3801_);
                    v___x_3803_ = v___x_3799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_a_3794_);
                    v___x_3803_ = v_reuseFailAlloc_3805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3793_ = v_tail_3797_;
                v_a_3794_ = v___x_3803_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(
    mut v_s_3807_: *mut leanh::LeanObject,
    mut v_a_3808_: *mut leanh::LeanObject,
    mut v_a_3809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3815_: u8 = 0;
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3808_) == 0 {
                    leanh::lean_dec(v_s_3807_);
                    v___x_3810_ = l_List_reverse___redArg(v_a_3809_);
                    return v___x_3810_;
                } else {
                    v_head_3811_ = leanh::lean_ctor_get(v_a_3808_, 0);
                    v_tail_3812_ = leanh::lean_ctor_get(v_a_3808_, 1);
                    v_isSharedCheck_3821_ = (!leanh::lean_is_exclusive(v_a_3808_)) as u8;
                    if v_isSharedCheck_3821_ == 0 {
                        v___x_3814_ = v_a_3808_;
                        v_isShared_3815_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3812_);
                        leanh::lean_inc(v_head_3811_);
                        leanh::lean_dec(v_a_3808_);
                        v___x_3814_ = leanh::lean_box(0);
                        v_isShared_3815_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_s_3807_);
                v___x_3816_ = l_Lean_LocalDecl_applyFVarSubst(v_s_3807_, v_head_3811_);
                if v_isShared_3815_ == 0 {
                    leanh::lean_ctor_set(v___x_3814_, 1, v_a_3809_);
                    leanh::lean_ctor_set(v___x_3814_, 0, v___x_3816_);
                    v___x_3818_ = v___x_3814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3809_);
                    v___x_3818_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3808_ = v_tail_3812_;
                v_a_3809_ = v___x_3818_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(
    mut v_s_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_fst_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3823_) == 0 {
                    leanh::lean_dec(v_s_3822_);
                    v___x_3825_ = l_List_reverse___redArg(v_a_3824_);
                    return v___x_3825_;
                } else {
                    v_head_3826_ = leanh::lean_ctor_get(v_a_3823_, 0);
                    v_tail_3827_ = leanh::lean_ctor_get(v_a_3823_, 1);
                    v_isSharedCheck_3846_ = (!leanh::lean_is_exclusive(v_a_3823_)) as u8;
                    if v_isSharedCheck_3846_ == 0 {
                        v___x_3829_ = v_a_3823_;
                        v_isShared_3830_ = v_isSharedCheck_3846_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3827_);
                        leanh::lean_inc(v_head_3826_);
                        leanh::lean_dec(v_a_3823_);
                        v___x_3829_ = leanh::lean_box(0);
                        v_isShared_3830_ = v_isSharedCheck_3846_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3831_ = leanh::lean_ctor_get(v_head_3826_, 0);
                v_snd_3832_ = leanh::lean_ctor_get(v_head_3826_, 1);
                v_isSharedCheck_3845_ = (!leanh::lean_is_exclusive(v_head_3826_)) as u8;
                if v_isSharedCheck_3845_ == 0 {
                    v___x_3834_ = v_head_3826_;
                    v_isShared_3835_ = v_isSharedCheck_3845_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3832_);
                    leanh::lean_inc(v_fst_3831_);
                    leanh::lean_dec(v_head_3826_);
                    v___x_3834_ = leanh::lean_box(0);
                    v_isShared_3835_ = v_isSharedCheck_3845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_s_3822_, 2);
                v___x_3836_ = l_Lean_Meta_FVarSubst_apply(v_s_3822_, v_fst_3831_);
                leanh::lean_dec(v_fst_3831_);
                v___x_3837_ = l_Lean_Meta_FVarSubst_apply(v_s_3822_, v_snd_3832_);
                leanh::lean_dec(v_snd_3832_);
                if v_isShared_3835_ == 0 {
                    leanh::lean_ctor_set(v___x_3834_, 1, v___x_3837_);
                    leanh::lean_ctor_set(v___x_3834_, 0, v___x_3836_);
                    v___x_3839_ = v___x_3834_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3844_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3837_);
                    v___x_3839_ = v_reuseFailAlloc_3844_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3830_ == 0 {
                    leanh::lean_ctor_set(v___x_3829_, 1, v_a_3824_);
                    leanh::lean_ctor_set(v___x_3829_, 0, v___x_3839_);
                    v___x_3841_ = v___x_3829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_a_3824_);
                    v___x_3841_ = v_reuseFailAlloc_3843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3823_ = v_tail_3827_;
                v_a_3824_ = v___x_3841_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Alt_applyFVarSubst(
    mut v_s_3847_: *mut leanh::LeanObject,
    mut v_alt_3848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cnstrs_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_notAltIdxs_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3849_ = leanh::lean_ctor_get(v_alt_3848_, 0);
                v_idx_3850_ = leanh::lean_ctor_get(v_alt_3848_, 1);
                v_rhs_3851_ = leanh::lean_ctor_get(v_alt_3848_, 2);
                v_fvarDecls_3852_ = leanh::lean_ctor_get(v_alt_3848_, 3);
                v_patterns_3853_ = leanh::lean_ctor_get(v_alt_3848_, 4);
                v_cnstrs_3854_ = leanh::lean_ctor_get(v_alt_3848_, 5);
                v_notAltIdxs_3855_ = leanh::lean_ctor_get(v_alt_3848_, 6);
                v_isSharedCheck_3867_ = (!leanh::lean_is_exclusive(v_alt_3848_)) as u8;
                if v_isSharedCheck_3867_ == 0 {
                    v___x_3857_ = v_alt_3848_;
                    v_isShared_3858_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_notAltIdxs_3855_);
                    leanh::lean_inc(v_cnstrs_3854_);
                    leanh::lean_inc(v_patterns_3853_);
                    leanh::lean_inc(v_fvarDecls_3852_);
                    leanh::lean_inc(v_rhs_3851_);
                    leanh::lean_inc(v_idx_3850_);
                    leanh::lean_inc(v_ref_3849_);
                    leanh::lean_dec(v_alt_3848_);
                    v___x_3857_ = leanh::lean_box(0);
                    v_isShared_3858_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_n(v_s_3847_, 3);
                v___x_3859_ = l_Lean_Meta_FVarSubst_apply(v_s_3847_, v_rhs_3851_);
                leanh::lean_dec_ref(v_rhs_3851_);
                v___x_3860_ = leanh::lean_box(0);
                v___x_3861_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(
                    v_s_3847_,
                    v_fvarDecls_3852_,
                    v___x_3860_,
                );
                v___x_3862_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(
                    v_s_3847_,
                    v_patterns_3853_,
                    v___x_3860_,
                );
                v___x_3863_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(
                    v_s_3847_,
                    v_cnstrs_3854_,
                    v___x_3860_,
                );
                if v_isShared_3858_ == 0 {
                    leanh::lean_ctor_set(v___x_3857_, 5, v___x_3863_);
                    leanh::lean_ctor_set(v___x_3857_, 4, v___x_3862_);
                    leanh::lean_ctor_set(v___x_3857_, 3, v___x_3861_);
                    leanh::lean_ctor_set(v___x_3857_, 2, v___x_3859_);
                    v___x_3865_ = v___x_3857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3866_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_ref_3849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_idx_3850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 2, v___x_3859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 3, v___x_3861_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 4, v___x_3862_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 5, v___x_3863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 6, v_notAltIdxs_3855_);
                    v___x_3865_ = v_reuseFailAlloc_3866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(
    mut v_fvarId_3868_: *mut leanh::LeanObject,
    mut v_v_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
    mut v_a_3871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3877_: u8 = 0;
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3870_) == 0 {
                    leanh::lean_dec_ref(v_v_3869_);
                    leanh::lean_dec(v_fvarId_3868_);
                    v___x_3872_ = l_List_reverse___redArg(v_a_3871_);
                    return v___x_3872_;
                } else {
                    v_head_3873_ = leanh::lean_ctor_get(v_a_3870_, 0);
                    v_tail_3874_ = leanh::lean_ctor_get(v_a_3870_, 1);
                    v_isSharedCheck_3883_ = (!leanh::lean_is_exclusive(v_a_3870_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3876_ = v_a_3870_;
                        v_isShared_3877_ = v_isSharedCheck_3883_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3874_);
                        leanh::lean_inc(v_head_3873_);
                        leanh::lean_dec(v_a_3870_);
                        v___x_3876_ = leanh::lean_box(0);
                        v_isShared_3877_ = v_isSharedCheck_3883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_v_3869_);
                leanh::lean_inc(v_fvarId_3868_);
                v___x_3878_ = l_Lean_Meta_Match_Pattern_replaceFVarId(
                    v_fvarId_3868_,
                    v_v_3869_,
                    v_head_3873_,
                );
                if v_isShared_3877_ == 0 {
                    leanh::lean_ctor_set(v___x_3876_, 1, v_a_3871_);
                    leanh::lean_ctor_set(v___x_3876_, 0, v___x_3878_);
                    v___x_3880_ = v___x_3876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_a_3871_);
                    v___x_3880_ = v_reuseFailAlloc_3882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3870_ = v_tail_3874_;
                v_a_3871_ = v___x_3880_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(
    mut v_fvarId_3884_: *mut leanh::LeanObject,
    mut v_v_3885_: *mut leanh::LeanObject,
    mut v_a_3886_: *mut leanh::LeanObject,
    mut v_a_3887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3886_) == 0 {
                    leanh::lean_dec(v_fvarId_3884_);
                    v___x_3888_ = l_List_reverse___redArg(v_a_3887_);
                    return v___x_3888_;
                } else {
                    v_head_3889_ = leanh::lean_ctor_get(v_a_3886_, 0);
                    v_tail_3890_ = leanh::lean_ctor_get(v_a_3886_, 1);
                    v_isSharedCheck_3899_ = (!leanh::lean_is_exclusive(v_a_3886_)) as u8;
                    if v_isSharedCheck_3899_ == 0 {
                        v___x_3892_ = v_a_3886_;
                        v_isShared_3893_ = v_isSharedCheck_3899_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3890_);
                        leanh::lean_inc(v_head_3889_);
                        leanh::lean_dec(v_a_3886_);
                        v___x_3892_ = leanh::lean_box(0);
                        v_isShared_3893_ = v_isSharedCheck_3899_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_fvarId_3884_);
                v___x_3894_ =
                    l_Lean_LocalDecl_replaceFVarId(v_fvarId_3884_, v_v_3885_, v_head_3889_);
                if v_isShared_3893_ == 0 {
                    leanh::lean_ctor_set(v___x_3892_, 1, v_a_3887_);
                    leanh::lean_ctor_set(v___x_3892_, 0, v___x_3894_);
                    v___x_3896_ = v___x_3892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3898_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_a_3887_);
                    v___x_3896_ = v_reuseFailAlloc_3898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3886_ = v_tail_3890_;
                v_a_3887_ = v___x_3896_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(
    mut v_fvarId_3900_: *mut leanh::LeanObject,
    mut v_v_3901_: *mut leanh::LeanObject,
    mut v_a_3902_: *mut leanh::LeanObject,
    mut v_a_3903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(
        v_fvarId_3900_,
        v_v_3901_,
        v_a_3902_,
        v_a_3903_,
    );
    leanh::lean_dec_ref(v_v_3901_);
    return v_res_3904_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(
    mut v_fvarId_3905_: *mut leanh::LeanObject,
    mut v_v_3906_: *mut leanh::LeanObject,
    mut v_a_3907_: *mut leanh::LeanObject,
    mut v_a_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v_fst_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3907_) == 0 {
                    leanh::lean_dec(v_fvarId_3905_);
                    v___x_3909_ = l_List_reverse___redArg(v_a_3908_);
                    return v___x_3909_;
                } else {
                    v_head_3910_ = leanh::lean_ctor_get(v_a_3907_, 0);
                    v_tail_3911_ = leanh::lean_ctor_get(v_a_3907_, 1);
                    v_isSharedCheck_3930_ = (!leanh::lean_is_exclusive(v_a_3907_)) as u8;
                    if v_isSharedCheck_3930_ == 0 {
                        v___x_3913_ = v_a_3907_;
                        v_isShared_3914_ = v_isSharedCheck_3930_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3911_);
                        leanh::lean_inc(v_head_3910_);
                        leanh::lean_dec(v_a_3907_);
                        v___x_3913_ = leanh::lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3930_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3915_ = leanh::lean_ctor_get(v_head_3910_, 0);
                v_snd_3916_ = leanh::lean_ctor_get(v_head_3910_, 1);
                v_isSharedCheck_3929_ = (!leanh::lean_is_exclusive(v_head_3910_)) as u8;
                if v_isSharedCheck_3929_ == 0 {
                    v___x_3918_ = v_head_3910_;
                    v_isShared_3919_ = v_isSharedCheck_3929_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3916_);
                    leanh::lean_inc(v_fst_3915_);
                    leanh::lean_dec(v_head_3910_);
                    v___x_3918_ = leanh::lean_box(0);
                    v_isShared_3919_ = v_isSharedCheck_3929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_fvarId_3905_, 2);
                v___x_3920_ = l_Lean_Expr_replaceFVarId(v_fst_3915_, v_fvarId_3905_, v_v_3906_);
                leanh::lean_dec(v_fst_3915_);
                v___x_3921_ = l_Lean_Expr_replaceFVarId(v_snd_3916_, v_fvarId_3905_, v_v_3906_);
                leanh::lean_dec(v_snd_3916_);
                if v_isShared_3919_ == 0 {
                    leanh::lean_ctor_set(v___x_3918_, 1, v___x_3921_);
                    leanh::lean_ctor_set(v___x_3918_, 0, v___x_3920_);
                    v___x_3923_ = v___x_3918_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3928_, 1, v___x_3921_);
                    v___x_3923_ = v_reuseFailAlloc_3928_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3914_ == 0 {
                    leanh::lean_ctor_set(v___x_3913_, 1, v_a_3908_);
                    leanh::lean_ctor_set(v___x_3913_, 0, v___x_3923_);
                    v___x_3925_ = v___x_3913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_a_3908_);
                    v___x_3925_ = v_reuseFailAlloc_3927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3907_ = v_tail_3911_;
                v_a_3908_ = v___x_3925_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(
    mut v_fvarId_3931_: *mut leanh::LeanObject,
    mut v_v_3932_: *mut leanh::LeanObject,
    mut v_a_3933_: *mut leanh::LeanObject,
    mut v_a_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(
        v_fvarId_3931_,
        v_v_3932_,
        v_a_3933_,
        v_a_3934_,
    );
    leanh::lean_dec_ref(v_v_3932_);
    return v_res_3935_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(
    mut v_fvarId_3936_: *mut leanh::LeanObject,
    mut v_a_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3937_) == 0 {
                    v___x_3939_ = l_List_reverse___redArg(v_a_3938_);
                    return v___x_3939_;
                } else {
                    v_head_3940_ = leanh::lean_ctor_get(v_a_3937_, 0);
                    v_tail_3941_ = leanh::lean_ctor_get(v_a_3937_, 1);
                    v_isSharedCheck_3952_ = (!leanh::lean_is_exclusive(v_a_3937_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3943_ = v_a_3937_;
                        v_isShared_3944_ = v_isSharedCheck_3952_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3941_);
                        leanh::lean_inc(v_head_3940_);
                        leanh::lean_dec(v_a_3937_);
                        v___x_3943_ = leanh::lean_box(0);
                        v_isShared_3944_ = v_isSharedCheck_3952_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3945_ = l_Lean_LocalDecl_fvarId(v_head_3940_);
                v___x_3946_ = l_Lean_instBEqFVarId_beq(v___x_3945_, v_fvarId_3936_);
                leanh::lean_dec(v___x_3945_);
                if v___x_3946_ == 0 {
                    if v_isShared_3944_ == 0 {
                        leanh::lean_ctor_set(v___x_3943_, 1, v_a_3938_);
                        v___x_3948_ = v___x_3943_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3950_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_head_3940_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_a_3938_);
                        v___x_3948_ = v_reuseFailAlloc_3950_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3943_);
                    leanh::lean_dec(v_head_3940_);
                    v_a_3937_ = v_tail_3941_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_3937_ = v_tail_3941_;
                v_a_3938_ = v___x_3948_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(
    mut v_fvarId_3953_: *mut leanh::LeanObject,
    mut v_a_3954_: *mut leanh::LeanObject,
    mut v_a_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(
        v_fvarId_3953_,
        v_a_3954_,
        v_a_3955_,
    );
    leanh::lean_dec(v_fvarId_3953_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_replaceFVarId(
    mut v_fvarId_3957_: *mut leanh::LeanObject,
    mut v_v_3958_: *mut leanh::LeanObject,
    mut v_alt_3959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cnstrs_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_notAltIdxs_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3960_ = leanh::lean_ctor_get(v_alt_3959_, 0);
                v_idx_3961_ = leanh::lean_ctor_get(v_alt_3959_, 1);
                v_rhs_3962_ = leanh::lean_ctor_get(v_alt_3959_, 2);
                v_fvarDecls_3963_ = leanh::lean_ctor_get(v_alt_3959_, 3);
                v_patterns_3964_ = leanh::lean_ctor_get(v_alt_3959_, 4);
                v_cnstrs_3965_ = leanh::lean_ctor_get(v_alt_3959_, 5);
                v_notAltIdxs_3966_ = leanh::lean_ctor_get(v_alt_3959_, 6);
                v_isSharedCheck_3979_ = (!leanh::lean_is_exclusive(v_alt_3959_)) as u8;
                if v_isSharedCheck_3979_ == 0 {
                    v___x_3968_ = v_alt_3959_;
                    v_isShared_3969_ = v_isSharedCheck_3979_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_notAltIdxs_3966_);
                    leanh::lean_inc(v_cnstrs_3965_);
                    leanh::lean_inc(v_patterns_3964_);
                    leanh::lean_inc(v_fvarDecls_3963_);
                    leanh::lean_inc(v_rhs_3962_);
                    leanh::lean_inc(v_idx_3961_);
                    leanh::lean_inc(v_ref_3960_);
                    leanh::lean_dec(v_alt_3959_);
                    v___x_3968_ = leanh::lean_box(0);
                    v_isShared_3969_ = v_isSharedCheck_3979_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_n(v_fvarId_3957_, 3);
                v___x_3970_ = l_Lean_Expr_replaceFVarId(v_rhs_3962_, v_fvarId_3957_, v_v_3958_);
                leanh::lean_dec_ref(v_rhs_3962_);
                v___x_3971_ = leanh::lean_box(0);
                v_decls_3972_ =
                    l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(
                        v_fvarId_3957_,
                        v_fvarDecls_3963_,
                        v___x_3971_,
                    );
                v___x_3973_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(
                    v_fvarId_3957_,
                    v_v_3958_,
                    v_decls_3972_,
                    v___x_3971_,
                );
                leanh::lean_inc_ref(v_v_3958_);
                v___x_3974_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(
                    v_fvarId_3957_,
                    v_v_3958_,
                    v_patterns_3964_,
                    v___x_3971_,
                );
                v___x_3975_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(
                    v_fvarId_3957_,
                    v_v_3958_,
                    v_cnstrs_3965_,
                    v___x_3971_,
                );
                leanh::lean_dec_ref(v_v_3958_);
                if v_isShared_3969_ == 0 {
                    leanh::lean_ctor_set(v___x_3968_, 5, v___x_3975_);
                    leanh::lean_ctor_set(v___x_3968_, 4, v___x_3974_);
                    leanh::lean_ctor_set(v___x_3968_, 3, v___x_3973_);
                    leanh::lean_ctor_set(v___x_3968_, 2, v___x_3970_);
                    v___x_3977_ = v___x_3968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3978_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_ref_3960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_idx_3961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 2, v___x_3970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 3, v___x_3973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 4, v___x_3974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 5, v___x_3975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 6, v_notAltIdxs_3966_);
                    v___x_3977_ = v_reuseFailAlloc_3978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(
    mut v_fvarId_3980_: *mut leanh::LeanObject,
    mut v_x_3981_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3982_: u8 = 0;
    let mut v_head_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3981_) == 0 {
                    v___x_3982_ = 0;
                    return v___x_3982_;
                } else {
                    v_head_3983_ = leanh::lean_ctor_get(v_x_3981_, 0);
                    v_tail_3984_ = leanh::lean_ctor_get(v_x_3981_, 1);
                    v___x_3985_ = l_Lean_LocalDecl_fvarId(v_head_3983_);
                    v___x_3986_ = l_Lean_instBEqFVarId_beq(v___x_3985_, v_fvarId_3980_);
                    leanh::lean_dec(v___x_3985_);
                    if v___x_3986_ == 0 {
                        v_x_3981_ = v_tail_3984_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3986_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(
    mut v_fvarId_3988_: *mut leanh::LeanObject,
    mut v_x_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3990_: u8 = 0;
    let mut v_r_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ =
        l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_3988_, v_x_3989_);
    leanh::lean_dec(v_x_3989_);
    leanh::lean_dec(v_fvarId_3988_);
    v_r_3991_ = leanh::lean_box((v_res_3990_) as usize);
    return v_r_3991_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_isLocalDecl(
    mut v_fvarId_3992_: *mut leanh::LeanObject,
    mut v_alt_3993_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fvarDecls_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    v_fvarDecls_3994_ = leanh::lean_ctor_get(v_alt_3993_, 3);
    v___x_3995_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(
        v_fvarId_3992_,
        v_fvarDecls_3994_,
    );
    return v___x_3995_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_isLocalDecl___boxed(
    mut v_fvarId_3996_: *mut leanh::LeanObject,
    mut v_alt_3997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3998_: u8 = 0;
    let mut v_r_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_3996_, v_alt_3997_);
    leanh::lean_dec_ref(v_alt_3997_);
    leanh::lean_dec(v_fvarId_3996_);
    v_r_3999_ = leanh::lean_box((v_res_3998_) as usize);
    return v_r_3999_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorIdx(
    mut v_x_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4000_) {
        0 => {
            let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4001_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4001_;
        }
        1 => {
            let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4002_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4002_;
        }
        2 => {
            let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4003_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4003_;
        }
        3 => {
            let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4004_ = leanh::lean_unsigned_to_nat(3);
            return v___x_4004_;
        }
        _ => {
            let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4005_ = leanh::lean_unsigned_to_nat(4);
            return v___x_4005_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorIdx___boxed(
    mut v_x_4006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4007_ = l_Lean_Meta_Match_Example_ctorIdx(v_x_4006_);
    leanh::lean_dec(v_x_4006_);
    return v_res_4007_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorElim___redArg(
    mut v_t_4008_: *mut leanh::LeanObject,
    mut v_k_4009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_4008_) {
        1 => {
            return v_k_4009_;
        }
        2 => {
            let mut v_a_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_4010_ = leanh::lean_ctor_get(v_t_4008_, 0);
            leanh::lean_inc(v_a_4010_);
            v_a_4011_ = leanh::lean_ctor_get(v_t_4008_, 1);
            leanh::lean_inc(v_a_4011_);
            leanh::lean_dec_ref_known(v_t_4008_, 2);
            v___x_4012_ = leanh::lean_apply_2(v_k_4009_, v_a_4010_, v_a_4011_);
            return v___x_4012_;
        }
        3 => {
            let mut v_a_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_4013_ = leanh::lean_ctor_get(v_t_4008_, 0);
            leanh::lean_inc_ref(v_a_4013_);
            leanh::lean_dec_ref_known(v_t_4008_, 1);
            v___x_4014_ = leanh::lean_apply_1(v_k_4009_, v_a_4013_);
            return v___x_4014_;
        }
        _ => {
            let mut v_a_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_4015_ = leanh::lean_ctor_get(v_t_4008_, 0);
            leanh::lean_inc(v_a_4015_);
            leanh::lean_dec(v_t_4008_);
            v___x_4016_ = leanh::lean_apply_1(v_k_4009_, v_a_4015_);
            return v___x_4016_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorElim(
    mut v_motive__1_4017_: *mut leanh::LeanObject,
    mut v_ctorIdx_4018_: *mut leanh::LeanObject,
    mut v_t_4019_: *mut leanh::LeanObject,
    mut v_h_4020_: *mut leanh::LeanObject,
    mut v_k_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4022_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4019_, v_k_4021_);
    return v___x_4022_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorElim___boxed(
    mut v_motive__1_4023_: *mut leanh::LeanObject,
    mut v_ctorIdx_4024_: *mut leanh::LeanObject,
    mut v_t_4025_: *mut leanh::LeanObject,
    mut v_h_4026_: *mut leanh::LeanObject,
    mut v_k_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4028_ = l_Lean_Meta_Match_Example_ctorElim(
        v_motive__1_4023_,
        v_ctorIdx_4024_,
        v_t_4025_,
        v_h_4026_,
        v_k_4027_,
    );
    leanh::lean_dec(v_ctorIdx_4024_);
    return v_res_4028_;
}
pub unsafe fn l_Lean_Meta_Match_Example_var_elim___redArg(
    mut v_t_4029_: *mut leanh::LeanObject,
    mut v_var_4030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4031_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4029_, v_var_4030_);
    return v___x_4031_;
}
pub unsafe fn l_Lean_Meta_Match_Example_var_elim(
    mut v_motive__1_4032_: *mut leanh::LeanObject,
    mut v_t_4033_: *mut leanh::LeanObject,
    mut v_h_4034_: *mut leanh::LeanObject,
    mut v_var_4035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4033_, v_var_4035_);
    return v___x_4036_;
}
pub unsafe fn l_Lean_Meta_Match_Example_underscore_elim___redArg(
    mut v_t_4037_: *mut leanh::LeanObject,
    mut v_underscore_4038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4037_, v_underscore_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_Meta_Match_Example_underscore_elim(
    mut v_motive__1_4040_: *mut leanh::LeanObject,
    mut v_t_4041_: *mut leanh::LeanObject,
    mut v_h_4042_: *mut leanh::LeanObject,
    mut v_underscore_4043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4044_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4041_, v_underscore_4043_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctor_elim___redArg(
    mut v_t_4045_: *mut leanh::LeanObject,
    mut v_ctor_4046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4045_, v_ctor_4046_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctor_elim(
    mut v_motive__1_4048_: *mut leanh::LeanObject,
    mut v_t_4049_: *mut leanh::LeanObject,
    mut v_h_4050_: *mut leanh::LeanObject,
    mut v_ctor_4051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4052_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4049_, v_ctor_4051_);
    return v___x_4052_;
}
pub unsafe fn l_Lean_Meta_Match_Example_val_elim___redArg(
    mut v_t_4053_: *mut leanh::LeanObject,
    mut v_val_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4053_, v_val_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_Meta_Match_Example_val_elim(
    mut v_motive__1_4056_: *mut leanh::LeanObject,
    mut v_t_4057_: *mut leanh::LeanObject,
    mut v_h_4058_: *mut leanh::LeanObject,
    mut v_val_4059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4057_, v_val_4059_);
    return v___x_4060_;
}
pub unsafe fn l_Lean_Meta_Match_Example_arrayLit_elim___redArg(
    mut v_t_4061_: *mut leanh::LeanObject,
    mut v_arrayLit_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4061_, v_arrayLit_4062_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_Meta_Match_Example_arrayLit_elim(
    mut v_motive__1_4064_: *mut leanh::LeanObject,
    mut v_t_4065_: *mut leanh::LeanObject,
    mut v_h_4066_: *mut leanh::LeanObject,
    mut v_arrayLit_4067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4068_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4065_, v_arrayLit_4067_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_Meta_Match_Example_replaceFVarId(
    mut v_fvarId_4069_: *mut leanh::LeanObject,
    mut v_ex_4070_: *mut leanh::LeanObject,
    mut v_x_4071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v_a_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v_a_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4088_: u8 = 0;
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4071_) {
                0 => {
                    v_a_4072_ = leanh::lean_ctor_get(v_x_4071_, 0);
                    v___x_4073_ = l_Lean_instBEqFVarId_beq(v_a_4072_, v_fvarId_4069_);
                    if v___x_4073_ == 0 {
                        return v_x_4071_;
                    } else {
                        leanh::lean_dec_ref_known(v_x_4071_, 1);
                        leanh::lean_inc(v_ex_4070_);
                        return v_ex_4070_;
                    }
                }
                2 => {
                    v_a_4074_ = leanh::lean_ctor_get(v_x_4071_, 0);
                    v_a_4075_ = leanh::lean_ctor_get(v_x_4071_, 1);
                    v_isSharedCheck_4084_ = (!leanh::lean_is_exclusive(v_x_4071_)) as u8;
                    if v_isSharedCheck_4084_ == 0 {
                        v___x_4077_ = v_x_4071_;
                        v_isShared_4078_ = v_isSharedCheck_4084_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4075_);
                        leanh::lean_inc(v_a_4074_);
                        leanh::lean_dec(v_x_4071_);
                        v___x_4077_ = leanh::lean_box(0);
                        v_isShared_4078_ = v_isSharedCheck_4084_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_a_4085_ = leanh::lean_ctor_get(v_x_4071_, 0);
                    v_isSharedCheck_4094_ = (!leanh::lean_is_exclusive(v_x_4071_)) as u8;
                    if v_isSharedCheck_4094_ == 0 {
                        v___x_4087_ = v_x_4071_;
                        v_isShared_4088_ = v_isSharedCheck_4094_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4085_);
                        leanh::lean_dec(v_x_4071_);
                        v___x_4087_ = leanh::lean_box(0);
                        v_isShared_4088_ = v_isSharedCheck_4094_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    return v_x_4071_;
                }
            },
            1 => {
                v___x_4079_ = leanh::lean_box(0);
                v___x_4080_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
                        v_fvarId_4069_,
                        v_ex_4070_,
                        v_a_4075_,
                        v___x_4079_,
                    );
                if v_isShared_4078_ == 0 {
                    leanh::lean_ctor_set(v___x_4077_, 1, v___x_4080_);
                    v___x_4082_ = v___x_4077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4083_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4080_);
                    v___x_4082_ = v_reuseFailAlloc_4083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4082_;
            }
            3 => {
                v___x_4089_ = leanh::lean_box(0);
                v___x_4090_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
                        v_fvarId_4069_,
                        v_ex_4070_,
                        v_a_4085_,
                        v___x_4089_,
                    );
                if v_isShared_4088_ == 0 {
                    leanh::lean_ctor_set(v___x_4087_, 0, v___x_4090_);
                    v___x_4092_ = v___x_4087_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
                    v___x_4092_ = v_reuseFailAlloc_4093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
    mut v_fvarId_4095_: *mut leanh::LeanObject,
    mut v_ex_4096_: *mut leanh::LeanObject,
    mut v_a_4097_: *mut leanh::LeanObject,
    mut v_a_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4097_) == 0 {
                    v___x_4099_ = l_List_reverse___redArg(v_a_4098_);
                    return v___x_4099_;
                } else {
                    v_head_4100_ = leanh::lean_ctor_get(v_a_4097_, 0);
                    v_tail_4101_ = leanh::lean_ctor_get(v_a_4097_, 1);
                    v_isSharedCheck_4110_ = (!leanh::lean_is_exclusive(v_a_4097_)) as u8;
                    if v_isSharedCheck_4110_ == 0 {
                        v___x_4103_ = v_a_4097_;
                        v_isShared_4104_ = v_isSharedCheck_4110_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4101_);
                        leanh::lean_inc(v_head_4100_);
                        leanh::lean_dec(v_a_4097_);
                        v___x_4103_ = leanh::lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4110_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4105_ = l_Lean_Meta_Match_Example_replaceFVarId(
                    v_fvarId_4095_,
                    v_ex_4096_,
                    v_head_4100_,
                );
                if v_isShared_4104_ == 0 {
                    leanh::lean_ctor_set(v___x_4103_, 1, v_a_4098_);
                    leanh::lean_ctor_set(v___x_4103_, 0, v___x_4105_);
                    v___x_4107_ = v___x_4103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4105_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_a_4098_);
                    v___x_4107_ = v_reuseFailAlloc_4109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4097_ = v_tail_4101_;
                v_a_4098_ = v___x_4107_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(
    mut v_fvarId_4111_: *mut leanh::LeanObject,
    mut v_ex_4112_: *mut leanh::LeanObject,
    mut v_a_4113_: *mut leanh::LeanObject,
    mut v_a_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
        v_fvarId_4111_,
        v_ex_4112_,
        v_a_4113_,
        v_a_4114_,
    );
    leanh::lean_dec(v_ex_4112_);
    leanh::lean_dec(v_fvarId_4111_);
    return v_res_4115_;
}
pub unsafe fn l_Lean_Meta_Match_Example_replaceFVarId___boxed(
    mut v_fvarId_4116_: *mut leanh::LeanObject,
    mut v_ex_4117_: *mut leanh::LeanObject,
    mut v_x_4118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_4116_, v_ex_4117_, v_x_4118_);
    leanh::lean_dec(v_ex_4117_);
    leanh::lean_dec(v_fvarId_4116_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_Meta_Match_Example_applyFVarSubst(
    mut v_s_4120_: *mut leanh::LeanObject,
    mut v_x_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut v_a_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4147_: u8 = 0;
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4121_) {
                0 => {
                    v_a_4122_ = leanh::lean_ctor_get(v_x_4121_, 0);
                    v_isSharedCheck_4132_ = (!leanh::lean_is_exclusive(v_x_4121_)) as u8;
                    if v_isSharedCheck_4132_ == 0 {
                        v___x_4124_ = v_x_4121_;
                        v_isShared_4125_ = v_isSharedCheck_4132_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4122_);
                        leanh::lean_dec(v_x_4121_);
                        v___x_4124_ = leanh::lean_box(0);
                        v_isShared_4125_ = v_isSharedCheck_4132_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_a_4133_ = leanh::lean_ctor_get(v_x_4121_, 0);
                    v_a_4134_ = leanh::lean_ctor_get(v_x_4121_, 1);
                    v_isSharedCheck_4143_ = (!leanh::lean_is_exclusive(v_x_4121_)) as u8;
                    if v_isSharedCheck_4143_ == 0 {
                        v___x_4136_ = v_x_4121_;
                        v_isShared_4137_ = v_isSharedCheck_4143_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4134_);
                        leanh::lean_inc(v_a_4133_);
                        leanh::lean_dec(v_x_4121_);
                        v___x_4136_ = leanh::lean_box(0);
                        v_isShared_4137_ = v_isSharedCheck_4143_;
                        state = 3;
                        continue;
                    }
                }
                4 => {
                    v_a_4144_ = leanh::lean_ctor_get(v_x_4121_, 0);
                    v_isSharedCheck_4153_ = (!leanh::lean_is_exclusive(v_x_4121_)) as u8;
                    if v_isSharedCheck_4153_ == 0 {
                        v___x_4146_ = v_x_4121_;
                        v_isShared_4147_ = v_isSharedCheck_4153_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4144_);
                        leanh::lean_dec(v_x_4121_);
                        v___x_4146_ = leanh::lean_box(0);
                        v_isShared_4147_ = v_isSharedCheck_4153_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    return v_x_4121_;
                }
            },
            1 => {
                v___x_4126_ = l_Lean_Meta_FVarSubst_get(v_s_4120_, v_a_4122_);
                if leanh::lean_obj_tag(v___x_4126_) == 1 {
                    v_fvarId_4127_ = leanh::lean_ctor_get(v___x_4126_, 0);
                    leanh::lean_inc(v_fvarId_4127_);
                    leanh::lean_dec_ref_known(v___x_4126_, 1);
                    if v_isShared_4125_ == 0 {
                        leanh::lean_ctor_set(v___x_4124_, 0, v_fvarId_4127_);
                        v___x_4129_ = v___x_4124_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_fvarId_4127_);
                        v___x_4129_ = v_reuseFailAlloc_4130_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4126_);
                    leanh::lean_del_object(v___x_4124_);
                    v___x_4131_ = leanh::lean_box(1);
                    return v___x_4131_;
                }
            }
            2 => {
                return v___x_4129_;
            }
            3 => {
                v___x_4138_ = leanh::lean_box(0);
                v___x_4139_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
                        v_s_4120_,
                        v_a_4134_,
                        v___x_4138_,
                    );
                if v_isShared_4137_ == 0 {
                    leanh::lean_ctor_set(v___x_4136_, 1, v___x_4139_);
                    v___x_4141_ = v___x_4136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4142_, 1, v___x_4139_);
                    v___x_4141_ = v_reuseFailAlloc_4142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4141_;
            }
            5 => {
                v___x_4148_ = leanh::lean_box(0);
                v___x_4149_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
                        v_s_4120_,
                        v_a_4144_,
                        v___x_4148_,
                    );
                if v_isShared_4147_ == 0 {
                    leanh::lean_ctor_set(v___x_4146_, 0, v___x_4149_);
                    v___x_4151_ = v___x_4146_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
                    v___x_4151_ = v_reuseFailAlloc_4152_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
    mut v_s_4154_: *mut leanh::LeanObject,
    mut v_a_4155_: *mut leanh::LeanObject,
    mut v_a_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4155_) == 0 {
                    v___x_4157_ = l_List_reverse___redArg(v_a_4156_);
                    return v___x_4157_;
                } else {
                    v_head_4158_ = leanh::lean_ctor_get(v_a_4155_, 0);
                    v_tail_4159_ = leanh::lean_ctor_get(v_a_4155_, 1);
                    v_isSharedCheck_4168_ = (!leanh::lean_is_exclusive(v_a_4155_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4161_ = v_a_4155_;
                        v_isShared_4162_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4159_);
                        leanh::lean_inc(v_head_4158_);
                        leanh::lean_dec(v_a_4155_);
                        v___x_4161_ = leanh::lean_box(0);
                        v_isShared_4162_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4163_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_4154_, v_head_4158_);
                if v_isShared_4162_ == 0 {
                    leanh::lean_ctor_set(v___x_4161_, 1, v_a_4156_);
                    leanh::lean_ctor_set(v___x_4161_, 0, v___x_4163_);
                    v___x_4165_ = v___x_4161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_a_4156_);
                    v___x_4165_ = v_reuseFailAlloc_4167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4155_ = v_tail_4159_;
                v_a_4156_ = v___x_4165_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(
    mut v_s_4169_: *mut leanh::LeanObject,
    mut v_a_4170_: *mut leanh::LeanObject,
    mut v_a_4171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4172_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
        v_s_4169_, v_a_4170_, v_a_4171_,
    );
    leanh::lean_dec(v_s_4169_);
    return v_res_4172_;
}
pub unsafe fn l_Lean_Meta_Match_Example_applyFVarSubst___boxed(
    mut v_s_4173_: *mut leanh::LeanObject,
    mut v_x_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4175_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_4173_, v_x_4174_);
    leanh::lean_dec(v_s_4173_);
    return v_res_4175_;
}
pub unsafe fn l_Lean_Meta_Match_Example_varsToUnderscore(
    mut v_x_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v_a_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4176_) {
                0 => {
                    leanh::lean_dec_ref_known(v_x_4176_, 1);
                    v___x_4177_ = leanh::lean_box(1);
                    return v___x_4177_;
                }
                2 => {
                    v_a_4178_ = leanh::lean_ctor_get(v_x_4176_, 0);
                    v_a_4179_ = leanh::lean_ctor_get(v_x_4176_, 1);
                    v_isSharedCheck_4188_ = (!leanh::lean_is_exclusive(v_x_4176_)) as u8;
                    if v_isSharedCheck_4188_ == 0 {
                        v___x_4181_ = v_x_4176_;
                        v_isShared_4182_ = v_isSharedCheck_4188_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4179_);
                        leanh::lean_inc(v_a_4178_);
                        leanh::lean_dec(v_x_4176_);
                        v___x_4181_ = leanh::lean_box(0);
                        v_isShared_4182_ = v_isSharedCheck_4188_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_a_4189_ = leanh::lean_ctor_get(v_x_4176_, 0);
                    v_isSharedCheck_4198_ = (!leanh::lean_is_exclusive(v_x_4176_)) as u8;
                    if v_isSharedCheck_4198_ == 0 {
                        v___x_4191_ = v_x_4176_;
                        v_isShared_4192_ = v_isSharedCheck_4198_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4189_);
                        leanh::lean_dec(v_x_4176_);
                        v___x_4191_ = leanh::lean_box(0);
                        v_isShared_4192_ = v_isSharedCheck_4198_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    return v_x_4176_;
                }
            },
            1 => {
                v___x_4183_ = leanh::lean_box(0);
                v___x_4184_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(
                        v_a_4179_,
                        v___x_4183_,
                    );
                if v_isShared_4182_ == 0 {
                    leanh::lean_ctor_set(v___x_4181_, 1, v___x_4184_);
                    v___x_4186_ = v___x_4181_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___x_4184_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4186_;
            }
            3 => {
                v___x_4193_ = leanh::lean_box(0);
                v___x_4194_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(
                        v_a_4189_,
                        v___x_4193_,
                    );
                if v_isShared_4192_ == 0 {
                    leanh::lean_ctor_set(v___x_4191_, 0, v___x_4194_);
                    v___x_4196_ = v___x_4191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4197_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
                    v___x_4196_ = v_reuseFailAlloc_4197_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4199_) == 0 {
                    v___x_4201_ = l_List_reverse___redArg(v_a_4200_);
                    return v___x_4201_;
                } else {
                    v_head_4202_ = leanh::lean_ctor_get(v_a_4199_, 0);
                    v_tail_4203_ = leanh::lean_ctor_get(v_a_4199_, 1);
                    v_isSharedCheck_4212_ = (!leanh::lean_is_exclusive(v_a_4199_)) as u8;
                    if v_isSharedCheck_4212_ == 0 {
                        v___x_4205_ = v_a_4199_;
                        v_isShared_4206_ = v_isSharedCheck_4212_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4203_);
                        leanh::lean_inc(v_head_4202_);
                        leanh::lean_dec(v_a_4199_);
                        v___x_4205_ = leanh::lean_box(0);
                        v_isShared_4206_ = v_isSharedCheck_4212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4207_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_4202_);
                if v_isShared_4206_ == 0 {
                    leanh::lean_ctor_set(v___x_4205_, 1, v_a_4200_);
                    leanh::lean_ctor_set(v___x_4205_, 0, v___x_4207_);
                    v___x_4209_ = v___x_4205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_a_4200_);
                    v___x_4209_ = v_reuseFailAlloc_4211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4199_ = v_tail_4203_;
                v_a_4200_ = v___x_4209_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Example_toMessageData___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4216_ = l_Lean_Meta_Match_Example_toMessageData___closed__1;
    v___x_4217_ = l_Lean_MessageData_ofFormat(v___x_4216_);
    return v___x_4217_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0;
    v___x_4219_ = l_Lean_stringToMessageData(v___x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(
    mut v_x_4220_: *mut leanh::LeanObject,
    mut v_x_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4226_: u8 = 0;
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4221_) == 0 {
                    return v_x_4220_;
                } else {
                    v_head_4222_ = leanh::lean_ctor_get(v_x_4221_, 0);
                    v_tail_4223_ = leanh::lean_ctor_get(v_x_4221_, 1);
                    v_isSharedCheck_4234_ = (!leanh::lean_is_exclusive(v_x_4221_)) as u8;
                    if v_isSharedCheck_4234_ == 0 {
                        v___x_4225_ = v_x_4221_;
                        v_isShared_4226_ = v_isSharedCheck_4234_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4223_);
                        leanh::lean_inc(v_head_4222_);
                        leanh::lean_dec(v_x_4221_);
                        v___x_4225_ = leanh::lean_box(0);
                        v_isShared_4226_ = v_isSharedCheck_4234_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once), _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
                if v_isShared_4226_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4225_, 7);
                    leanh::lean_ctor_set(v___x_4225_, 1, v___x_4227_);
                    leanh::lean_ctor_set(v___x_4225_, 0, v_x_4220_);
                    v___x_4229_ = v___x_4225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4233_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_x_4220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4233_, 1, v___x_4227_);
                    v___x_4229_ = v_reuseFailAlloc_4233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4230_ = l_Lean_Meta_Match_Example_toMessageData(v_head_4222_);
                v___x_4231_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4231_, 0, v___x_4229_);
                leanh::lean_ctor_set(v___x_4231_, 1, v___x_4230_);
                v_x_4220_ = v___x_4231_;
                v_x_4221_ = v_tail_4223_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Example_toMessageData___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4238_ = l_Lean_Meta_Match_Example_toMessageData___closed__4;
    v___x_4239_ = l_Lean_MessageData_ofFormat(v___x_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Lean_Meta_Match_Example_toMessageData(
    mut v_x_4240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut v_unused_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_x_4240_) {
                    0 => {
                        v_a_4241_ = leanh::lean_ctor_get(v_x_4240_, 0);
                        leanh::lean_inc(v_a_4241_);
                        leanh::lean_dec_ref_known(v_x_4240_, 1);
                        v___x_4242_ = l_Lean_mkFVar(v_a_4241_);
                        v___x_4243_ = l_Lean_MessageData_ofExpr(v___x_4242_);
                        return v___x_4243_;
                    }
                    1 => {
                        v___x_4244_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__2_once
                            ),
                            _init_l_Lean_Meta_Match_Example_toMessageData___closed__2,
                        );
                        return v___x_4244_;
                    }
                    2 => {
                        v_a_4245_ = leanh::lean_ctor_get(v_x_4240_, 1);
                        if leanh::lean_obj_tag(v_a_4245_) == 0 {
                            v_a_4246_ = leanh::lean_ctor_get(v_x_4240_, 0);
                            leanh::lean_inc(v_a_4246_);
                            leanh::lean_dec_ref_known(v_x_4240_, 2);
                            v___x_4247_ = leanh::lean_box(0);
                            v___x_4248_ = l_Lean_mkConst(v_a_4246_, v___x_4247_);
                            v___x_4249_ = l_Lean_MessageData_ofExpr(v___x_4248_);
                            return v___x_4249_;
                        } else {
                            leanh::lean_inc(v_a_4245_);
                            v_a_4250_ = leanh::lean_ctor_get(v_x_4240_, 0);
                            v_isSharedCheck_4265_ =
                                (!leanh::lean_is_exclusive(v_x_4240_)) as u8;
                            if v_isSharedCheck_4265_ == 0 {
                                v_unused_4266_ = leanh::lean_ctor_get(v_x_4240_, 1);
                                leanh::lean_dec(v_unused_4266_);
                                v___x_4252_ = v_x_4240_;
                                v_isShared_4253_ = v_isSharedCheck_4265_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4250_);
                                leanh::lean_dec(v_x_4240_);
                                v___x_4252_ = leanh::lean_box(0);
                                v_isShared_4253_ = v_isSharedCheck_4265_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    3 => {
                        v_a_4267_ = leanh::lean_ctor_get(v_x_4240_, 0);
                        leanh::lean_inc_ref(v_a_4267_);
                        leanh::lean_dec_ref_known(v_x_4240_, 1);
                        v___x_4268_ = l_Lean_MessageData_ofExpr(v_a_4267_);
                        return v___x_4268_;
                    }
                    _ => {
                        v_a_4269_ = leanh::lean_ctor_get(v_x_4240_, 0);
                        leanh::lean_inc(v_a_4269_);
                        leanh::lean_dec_ref_known(v_x_4240_, 1);
                        v___x_4270_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__5_once
                            ),
                            _init_l_Lean_Meta_Match_Example_toMessageData___closed__5,
                        );
                        v___x_4271_ = leanh::lean_box(0);
                        v___x_4272_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_4269_, v___x_4271_);
                        v___x_4273_ = l_Lean_MessageData_ofList(v___x_4272_);
                        v___x_4274_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4274_, 0, v___x_4270_);
                        leanh::lean_ctor_set(v___x_4274_, 1, v___x_4273_);
                        return v___x_4274_;
                    }
                }
            }
            1 => {
                v___x_4254_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5,
                );
                v___x_4255_ = 0;
                v___x_4256_ = l_Lean_MessageData_ofConstName(v_a_4250_, v___x_4255_);
                if v_isShared_4253_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4252_, 7);
                    leanh::lean_ctor_set(v___x_4252_, 1, v___x_4256_);
                    leanh::lean_ctor_set(v___x_4252_, 0, v___x_4254_);
                    v___x_4258_ = v___x_4252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4256_);
                    v___x_4258_ = v_reuseFailAlloc_4264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4259_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6,
                );
                v___x_4260_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(
                    v___x_4259_,
                    v_a_4245_,
                );
                v___x_4261_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4261_, 0, v___x_4258_);
                leanh::lean_ctor_set(v___x_4261_, 1, v___x_4260_);
                v___x_4262_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                );
                v___x_4263_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4263_, 0, v___x_4261_);
                leanh::lean_ctor_set(v___x_4263_, 1, v___x_4262_);
                return v___x_4263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(
    mut v_a_4275_: *mut leanh::LeanObject,
    mut v_a_4276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4275_) == 0 {
                    v___x_4277_ = l_List_reverse___redArg(v_a_4276_);
                    return v___x_4277_;
                } else {
                    v_head_4278_ = leanh::lean_ctor_get(v_a_4275_, 0);
                    v_tail_4279_ = leanh::lean_ctor_get(v_a_4275_, 1);
                    v_isSharedCheck_4288_ = (!leanh::lean_is_exclusive(v_a_4275_)) as u8;
                    if v_isSharedCheck_4288_ == 0 {
                        v___x_4281_ = v_a_4275_;
                        v_isShared_4282_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4279_);
                        leanh::lean_inc(v_head_4278_);
                        leanh::lean_dec(v_a_4275_);
                        v___x_4281_ = leanh::lean_box(0);
                        v_isShared_4282_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4283_ = l_Lean_Meta_Match_Example_toMessageData(v_head_4278_);
                if v_isShared_4282_ == 0 {
                    leanh::lean_ctor_set(v___x_4281_, 1, v_a_4276_);
                    leanh::lean_ctor_set(v___x_4281_, 0, v___x_4283_);
                    v___x_4285_ = v___x_4281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_a_4276_);
                    v___x_4285_ = v_reuseFailAlloc_4287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4275_ = v_tail_4279_;
                v_a_4276_ = v___x_4285_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(
    mut v_a_4289_: *mut leanh::LeanObject,
    mut v_a_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4289_) == 0 {
                    v___x_4291_ = l_List_reverse___redArg(v_a_4290_);
                    return v___x_4291_;
                } else {
                    v_head_4292_ = leanh::lean_ctor_get(v_a_4289_, 0);
                    v_tail_4293_ = leanh::lean_ctor_get(v_a_4289_, 1);
                    v_isSharedCheck_4303_ = (!leanh::lean_is_exclusive(v_a_4289_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4295_ = v_a_4289_;
                        v_isShared_4296_ = v_isSharedCheck_4303_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4293_);
                        leanh::lean_inc(v_head_4292_);
                        leanh::lean_dec(v_a_4289_);
                        v___x_4295_ = leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4303_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4297_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_4292_);
                v___x_4298_ = l_Lean_Meta_Match_Example_toMessageData(v___x_4297_);
                if v_isShared_4296_ == 0 {
                    leanh::lean_ctor_set(v___x_4295_, 1, v_a_4290_);
                    leanh::lean_ctor_set(v___x_4295_, 0, v___x_4298_);
                    v___x_4300_ = v___x_4295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 1, v_a_4290_);
                    v___x_4300_ = v_reuseFailAlloc_4302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4289_ = v_tail_4293_;
                v_a_4290_ = v___x_4300_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_examplesToMessageData(
    mut v_cex_4304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4305_ = leanh::lean_box(0);
    v___x_4306_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(
        v_cex_4304_,
        v___x_4305_,
    );
    v___x_4307_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once),
        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11,
    );
    v___x_4308_ = l_Lean_MessageData_joinSep(v___x_4306_, v___x_4307_);
    return v___x_4308_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
    mut v_mvarId_4314_: *mut leanh::LeanObject,
    mut v_x_4315_: *mut leanh::LeanObject,
    mut v___y_4316_: *mut leanh::LeanObject,
    mut v___y_4317_: *mut leanh::LeanObject,
    mut v___y_4318_: *mut leanh::LeanObject,
    mut v___y_4319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut v_a_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4321_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_4314_,
                    v_x_4315_,
                    v___y_4316_,
                    v___y_4317_,
                    v___y_4318_,
                    v___y_4319_,
                );
                if leanh::lean_obj_tag(v___x_4321_) == 0 {
                    v_a_4322_ = leanh::lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4329_ = (!leanh::lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4324_ = v___x_4321_;
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4322_);
                        leanh::lean_dec(v___x_4321_);
                        v___x_4324_ = leanh::lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4330_ = leanh::lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4337_ = (!leanh::lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4332_ = v___x_4321_;
                        v_isShared_4333_ = v_isSharedCheck_4337_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4330_);
                        leanh::lean_dec(v___x_4321_);
                        v___x_4332_ = leanh::lean_box(0);
                        v_isShared_4333_ = v_isSharedCheck_4337_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4325_ == 0 {
                    v___x_4327_ = v___x_4324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
                    v___x_4327_ = v_reuseFailAlloc_4328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4327_;
            }
            3 => {
                if v_isShared_4333_ == 0 {
                    v___x_4335_ = v___x_4332_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(
    mut v_mvarId_4338_: *mut leanh::LeanObject,
    mut v_x_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4345_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
        v_mvarId_4338_,
        v_x_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
        v___y_4343_,
    );
    leanh::lean_dec(v___y_4343_);
    leanh::lean_dec_ref(v___y_4342_);
    leanh::lean_dec(v___y_4341_);
    leanh::lean_dec_ref(v___y_4340_);
    return v_res_4345_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(
    mut v_00_u03b1_4346_: *mut leanh::LeanObject,
    mut v_mvarId_4347_: *mut leanh::LeanObject,
    mut v_x_4348_: *mut leanh::LeanObject,
    mut v___y_4349_: *mut leanh::LeanObject,
    mut v___y_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
    mut v___y_4352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4354_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
        v_mvarId_4347_,
        v_x_4348_,
        v___y_4349_,
        v___y_4350_,
        v___y_4351_,
        v___y_4352_,
    );
    return v___x_4354_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(
    mut v_00_u03b1_4355_: *mut leanh::LeanObject,
    mut v_mvarId_4356_: *mut leanh::LeanObject,
    mut v_x_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4363_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(
        v_00_u03b1_4355_,
        v_mvarId_4356_,
        v_x_4357_,
        v___y_4358_,
        v___y_4359_,
        v___y_4360_,
        v___y_4361_,
    );
    leanh::lean_dec(v___y_4361_);
    leanh::lean_dec_ref(v___y_4360_);
    leanh::lean_dec(v___y_4359_);
    leanh::lean_dec_ref(v___y_4358_);
    return v_res_4363_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf___redArg(
    mut v_p_4364_: *mut leanh::LeanObject,
    mut v_x_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
    mut v_a_4368_: *mut leanh::LeanObject,
    mut v_a_4369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarId_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mvarId_4371_ = leanh::lean_ctor_get(v_p_4364_, 0);
    leanh::lean_inc(v_mvarId_4371_);
    leanh::lean_dec_ref(v_p_4364_);
    v___x_4372_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
        v_mvarId_4371_,
        v_x_4365_,
        v_a_4366_,
        v_a_4367_,
        v_a_4368_,
        v_a_4369_,
    );
    return v___x_4372_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf___redArg___boxed(
    mut v_p_4373_: *mut leanh::LeanObject,
    mut v_x_4374_: *mut leanh::LeanObject,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
    mut v_a_4377_: *mut leanh::LeanObject,
    mut v_a_4378_: *mut leanh::LeanObject,
    mut v_a_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4380_ = l_Lean_Meta_Match_withGoalOf___redArg(
        v_p_4373_, v_x_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_,
    );
    leanh::lean_dec(v_a_4378_);
    leanh::lean_dec_ref(v_a_4377_);
    leanh::lean_dec(v_a_4376_);
    leanh::lean_dec_ref(v_a_4375_);
    return v_res_4380_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf(
    mut v_00_u03b1_4381_: *mut leanh::LeanObject,
    mut v_p_4382_: *mut leanh::LeanObject,
    mut v_x_4383_: *mut leanh::LeanObject,
    mut v_a_4384_: *mut leanh::LeanObject,
    mut v_a_4385_: *mut leanh::LeanObject,
    mut v_a_4386_: *mut leanh::LeanObject,
    mut v_a_4387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_Meta_Match_withGoalOf___redArg(
        v_p_4382_, v_x_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_,
    );
    return v___x_4389_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf___boxed(
    mut v_00_u03b1_4390_: *mut leanh::LeanObject,
    mut v_p_4391_: *mut leanh::LeanObject,
    mut v_x_4392_: *mut leanh::LeanObject,
    mut v_a_4393_: *mut leanh::LeanObject,
    mut v_a_4394_: *mut leanh::LeanObject,
    mut v_a_4395_: *mut leanh::LeanObject,
    mut v_a_4396_: *mut leanh::LeanObject,
    mut v_a_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4398_ = l_Lean_Meta_Match_withGoalOf(
        v_00_u03b1_4390_,
        v_p_4391_,
        v_x_4392_,
        v_a_4393_,
        v_a_4394_,
        v_a_4395_,
        v_a_4396_,
    );
    leanh::lean_dec(v_a_4396_);
    leanh::lean_dec_ref(v_a_4395_);
    leanh::lean_dec(v_a_4394_);
    leanh::lean_dec_ref(v_a_4393_);
    return v_res_4398_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(
    mut v_x_4399_: *mut leanh::LeanObject,
    mut v_x_4400_: *mut leanh::LeanObject,
    mut v___y_4401_: *mut leanh::LeanObject,
    mut v___y_4402_: *mut leanh::LeanObject,
    mut v___y_4403_: *mut leanh::LeanObject,
    mut v___y_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4399_) == 0 {
                    v___x_4406_ = l_List_reverse___redArg(v_x_4400_);
                    v___x_4407_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4407_, 0, v___x_4406_);
                    return v___x_4407_;
                } else {
                    v_head_4408_ = leanh::lean_ctor_get(v_x_4399_, 0);
                    v_tail_4409_ = leanh::lean_ctor_get(v_x_4399_, 1);
                    v_isSharedCheck_4427_ = (!leanh::lean_is_exclusive(v_x_4399_)) as u8;
                    if v_isSharedCheck_4427_ == 0 {
                        v___x_4411_ = v_x_4399_;
                        v_isShared_4412_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4409_);
                        leanh::lean_inc(v_head_4408_);
                        leanh::lean_dec(v_x_4399_);
                        v___x_4411_ = leanh::lean_box(0);
                        v_isShared_4412_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4413_ = l_Lean_Meta_Match_Alt_toMessageData(
                    v_head_4408_,
                    v___y_4401_,
                    v___y_4402_,
                    v___y_4403_,
                    v___y_4404_,
                );
                if leanh::lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    leanh::lean_inc(v_a_4414_);
                    leanh::lean_dec_ref_known(v___x_4413_, 1);
                    if v_isShared_4412_ == 0 {
                        leanh::lean_ctor_set(v___x_4411_, 1, v_x_4400_);
                        leanh::lean_ctor_set(v___x_4411_, 0, v_a_4414_);
                        v___x_4416_ = v___x_4411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4418_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4414_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_x_4400_);
                        v___x_4416_ = v_reuseFailAlloc_4418_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4411_);
                    leanh::lean_dec(v_tail_4409_);
                    leanh::lean_dec(v_x_4400_);
                    v_a_4419_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4426_ = (!leanh::lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4426_ == 0 {
                        v___x_4421_ = v___x_4413_;
                        v_isShared_4422_ = v_isSharedCheck_4426_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4419_);
                        leanh::lean_dec(v___x_4413_);
                        v___x_4421_ = leanh::lean_box(0);
                        v_isShared_4422_ = v_isSharedCheck_4426_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4399_ = v_tail_4409_;
                v_x_4400_ = v___x_4416_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4422_ == 0 {
                    v___x_4424_ = v___x_4421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(
    mut v_x_4428_: *mut leanh::LeanObject,
    mut v_x_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(
        v_x_4428_,
        v_x_4429_,
        v___y_4430_,
        v___y_4431_,
        v___y_4432_,
        v___y_4433_,
    );
    leanh::lean_dec(v___y_4433_);
    leanh::lean_dec_ref(v___y_4432_);
    leanh::lean_dec(v___y_4431_);
    leanh::lean_dec_ref(v___y_4430_);
    return v_res_4435_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(
    mut v_x_4436_: *mut leanh::LeanObject,
    mut v_x_4437_: *mut leanh::LeanObject,
    mut v___y_4438_: *mut leanh::LeanObject,
    mut v___y_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
    mut v___y_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4436_) == 0 {
                    v___x_4443_ = l_List_reverse___redArg(v_x_4437_);
                    v___x_4444_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4444_, 0, v___x_4443_);
                    return v___x_4444_;
                } else {
                    v_head_4445_ = leanh::lean_ctor_get(v_x_4436_, 0);
                    v_tail_4446_ = leanh::lean_ctor_get(v_x_4436_, 1);
                    v_isSharedCheck_4471_ = (!leanh::lean_is_exclusive(v_x_4436_)) as u8;
                    if v_isSharedCheck_4471_ == 0 {
                        v___x_4448_ = v_x_4436_;
                        v_isShared_4449_ = v_isSharedCheck_4471_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4446_);
                        leanh::lean_inc(v_head_4445_);
                        leanh::lean_dec(v_x_4436_);
                        v___x_4448_ = leanh::lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_4441_);
                leanh::lean_inc_ref(v___y_4440_);
                leanh::lean_inc(v___y_4439_);
                leanh::lean_inc_ref(v___y_4438_);
                leanh::lean_inc(v_head_4445_);
                v___x_4450_ = lean_infer_type(
                    v_head_4445_,
                    v___y_4438_,
                    v___y_4439_,
                    v___y_4440_,
                    v___y_4441_,
                );
                if leanh::lean_obj_tag(v___x_4450_) == 0 {
                    v_a_4451_ = leanh::lean_ctor_get(v___x_4450_, 0);
                    leanh::lean_inc(v_a_4451_);
                    leanh::lean_dec_ref_known(v___x_4450_, 1);
                    v___x_4452_ = l_Lean_MessageData_ofExpr(v_head_4445_);
                    v___x_4453_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
                    v___x_4454_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4454_, 0, v___x_4452_);
                    leanh::lean_ctor_set(v___x_4454_, 1, v___x_4453_);
                    v___x_4455_ = l_Lean_MessageData_ofExpr(v_a_4451_);
                    v___x_4456_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4456_, 0, v___x_4454_);
                    leanh::lean_ctor_set(v___x_4456_, 1, v___x_4455_);
                    v___x_4457_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                    );
                    v___x_4458_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4458_, 0, v___x_4456_);
                    leanh::lean_ctor_set(v___x_4458_, 1, v___x_4457_);
                    if v_isShared_4449_ == 0 {
                        leanh::lean_ctor_set(v___x_4448_, 1, v_x_4437_);
                        leanh::lean_ctor_set(v___x_4448_, 0, v___x_4458_);
                        v___x_4460_ = v___x_4448_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4462_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4458_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_x_4437_);
                        v___x_4460_ = v_reuseFailAlloc_4462_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4448_);
                    leanh::lean_dec(v_tail_4446_);
                    leanh::lean_dec(v_head_4445_);
                    leanh::lean_dec(v_x_4437_);
                    v_a_4463_ = leanh::lean_ctor_get(v___x_4450_, 0);
                    v_isSharedCheck_4470_ = (!leanh::lean_is_exclusive(v___x_4450_)) as u8;
                    if v_isSharedCheck_4470_ == 0 {
                        v___x_4465_ = v___x_4450_;
                        v_isShared_4466_ = v_isSharedCheck_4470_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4463_);
                        leanh::lean_dec(v___x_4450_);
                        v___x_4465_ = leanh::lean_box(0);
                        v_isShared_4466_ = v_isSharedCheck_4470_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4436_ = v_tail_4446_;
                v_x_4437_ = v___x_4460_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4466_ == 0 {
                    v___x_4468_ = v___x_4465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
                    v___x_4468_ = v_reuseFailAlloc_4469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(
    mut v_x_4472_: *mut leanh::LeanObject,
    mut v_x_4473_: *mut leanh::LeanObject,
    mut v___y_4474_: *mut leanh::LeanObject,
    mut v___y_4475_: *mut leanh::LeanObject,
    mut v___y_4476_: *mut leanh::LeanObject,
    mut v___y_4477_: *mut leanh::LeanObject,
    mut v___y_4478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4479_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(
        v_x_4472_,
        v_x_4473_,
        v___y_4474_,
        v___y_4475_,
        v___y_4476_,
        v___y_4477_,
    );
    leanh::lean_dec(v___y_4477_);
    leanh::lean_dec_ref(v___y_4476_);
    leanh::lean_dec(v___y_4475_);
    leanh::lean_dec_ref(v___y_4474_);
    return v_res_4479_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0;
    v___x_4482_ = l_Lean_stringToMessageData(v___x_4481_);
    return v___x_4482_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2;
    v___x_4485_ = l_Lean_stringToMessageData(v___x_4484_);
    return v___x_4485_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = leanh::lean_box(1);
    v___x_4487_ = l_Lean_MessageData_ofFormat(v___x_4486_);
    return v___x_4487_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4489_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5;
    v___x_4490_ = l_Lean_stringToMessageData(v___x_4489_);
    return v___x_4490_;
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData___lam__0(
    mut v_alts_4491_: *mut leanh::LeanObject,
    mut v___x_4492_: *mut leanh::LeanObject,
    mut v_vars_4493_: *mut leanh::LeanObject,
    mut v_examples_4494_: *mut leanh::LeanObject,
    mut v___y_4495_: *mut leanh::LeanObject,
    mut v___y_4496_: *mut leanh::LeanObject,
    mut v___y_4497_: *mut leanh::LeanObject,
    mut v___y_4498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4526_: u8 = 0;
    let mut v_a_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4530_: u8 = 0;
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4534_: u8 = 0;
    let mut v_a_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_4492_);
                v___x_4500_ =
                    l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(
                        v_alts_4491_,
                        v___x_4492_,
                        v___y_4495_,
                        v___y_4496_,
                        v___y_4497_,
                        v___y_4498_,
                    );
                if leanh::lean_obj_tag(v___x_4500_) == 0 {
                    v_a_4501_ = leanh::lean_ctor_get(v___x_4500_, 0);
                    leanh::lean_inc(v_a_4501_);
                    leanh::lean_dec_ref_known(v___x_4500_, 1);
                    leanh::lean_inc(v___x_4492_);
                    v___x_4502_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(
                            v_vars_4493_,
                            v___x_4492_,
                            v___y_4495_,
                            v___y_4496_,
                            v___y_4497_,
                            v___y_4498_,
                        );
                    if leanh::lean_obj_tag(v___x_4502_) == 0 {
                        v_a_4503_ = leanh::lean_ctor_get(v___x_4502_, 0);
                        v_isSharedCheck_4526_ =
                            (!leanh::lean_is_exclusive(v___x_4502_)) as u8;
                        if v_isSharedCheck_4526_ == 0 {
                            v___x_4505_ = v___x_4502_;
                            v_isShared_4506_ = v_isSharedCheck_4526_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4503_);
                            leanh::lean_dec(v___x_4502_);
                            v___x_4505_ = leanh::lean_box(0);
                            v_isShared_4506_ = v_isSharedCheck_4526_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4501_);
                        leanh::lean_dec(v_examples_4494_);
                        leanh::lean_dec(v___x_4492_);
                        v_a_4527_ = leanh::lean_ctor_get(v___x_4502_, 0);
                        v_isSharedCheck_4534_ =
                            (!leanh::lean_is_exclusive(v___x_4502_)) as u8;
                        if v_isSharedCheck_4534_ == 0 {
                            v___x_4529_ = v___x_4502_;
                            v_isShared_4530_ = v_isSharedCheck_4534_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4527_);
                            leanh::lean_dec(v___x_4502_);
                            v___x_4529_ = leanh::lean_box(0);
                            v_isShared_4530_ = v_isSharedCheck_4534_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_examples_4494_);
                    leanh::lean_dec(v_vars_4493_);
                    leanh::lean_dec(v___x_4492_);
                    v_a_4535_ = leanh::lean_ctor_get(v___x_4500_, 0);
                    v_isSharedCheck_4542_ = (!leanh::lean_is_exclusive(v___x_4500_)) as u8;
                    if v_isSharedCheck_4542_ == 0 {
                        v___x_4537_ = v___x_4500_;
                        v_isShared_4538_ = v_isSharedCheck_4542_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4535_);
                        leanh::lean_dec(v___x_4500_);
                        v___x_4537_ = leanh::lean_box(0);
                        v_isShared_4538_ = v_isSharedCheck_4542_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4507_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1,
                );
                v___x_4508_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(
                    v_a_4503_,
                    v___x_4492_,
                );
                v___x_4509_ = l_Lean_MessageData_ofList(v___x_4508_);
                v___x_4510_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4510_, 0, v___x_4507_);
                leanh::lean_ctor_set(v___x_4510_, 1, v___x_4509_);
                v___x_4511_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3,
                );
                v___x_4512_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4512_, 0, v___x_4510_);
                leanh::lean_ctor_set(v___x_4512_, 1, v___x_4511_);
                v___x_4513_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4,
                );
                v___x_4514_ = l_Lean_MessageData_joinSep(v_a_4501_, v___x_4513_);
                v___x_4515_ = l_Lean_indentD(v___x_4514_);
                v___x_4516_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4516_, 0, v___x_4512_);
                leanh::lean_ctor_set(v___x_4516_, 1, v___x_4515_);
                v___x_4517_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6,
                );
                v___x_4518_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4518_, 0, v___x_4516_);
                leanh::lean_ctor_set(v___x_4518_, 1, v___x_4517_);
                v___x_4519_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_4494_);
                v___x_4520_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4520_, 0, v___x_4518_);
                leanh::lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                v___x_4521_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__5_once),
                    _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5,
                );
                v___x_4522_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4522_, 0, v___x_4520_);
                leanh::lean_ctor_set(v___x_4522_, 1, v___x_4521_);
                if v_isShared_4506_ == 0 {
                    leanh::lean_ctor_set(v___x_4505_, 0, v___x_4522_);
                    v___x_4524_ = v___x_4505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
                    v___x_4524_ = v_reuseFailAlloc_4525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4524_;
            }
            3 => {
                if v_isShared_4530_ == 0 {
                    v___x_4532_ = v___x_4529_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
                    v___x_4532_ = v_reuseFailAlloc_4533_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4532_;
            }
            5 => {
                if v_isShared_4538_ == 0 {
                    v___x_4540_ = v___x_4537_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
                    v___x_4540_ = v_reuseFailAlloc_4541_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(
    mut v_alts_4543_: *mut leanh::LeanObject,
    mut v___x_4544_: *mut leanh::LeanObject,
    mut v_vars_4545_: *mut leanh::LeanObject,
    mut v_examples_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
    mut v___y_4550_: *mut leanh::LeanObject,
    mut v___y_4551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(
        v_alts_4543_,
        v___x_4544_,
        v_vars_4545_,
        v_examples_4546_,
        v___y_4547_,
        v___y_4548_,
        v___y_4549_,
        v___y_4550_,
    );
    leanh::lean_dec(v___y_4550_);
    leanh::lean_dec_ref(v___y_4549_);
    leanh::lean_dec(v___y_4548_);
    leanh::lean_dec_ref(v___y_4547_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData(
    mut v_p_4553_: *mut leanh::LeanObject,
    mut v_a_4554_: *mut leanh::LeanObject,
    mut v_a_4555_: *mut leanh::LeanObject,
    mut v_a_4556_: *mut leanh::LeanObject,
    mut v_a_4557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_examples_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vars_4559_ = leanh::lean_ctor_get(v_p_4553_, 1);
    v_alts_4560_ = leanh::lean_ctor_get(v_p_4553_, 2);
    v_examples_4561_ = leanh::lean_ctor_get(v_p_4553_, 3);
    v___x_4562_ = leanh::lean_box(0);
    leanh::lean_inc(v_examples_4561_);
    leanh::lean_inc(v_vars_4559_);
    leanh::lean_inc(v_alts_4560_);
    v___f_4563_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_4563_, 0, v_alts_4560_);
    leanh::lean_closure_set(v___f_4563_, 1, v___x_4562_);
    leanh::lean_closure_set(v___f_4563_, 2, v_vars_4559_);
    leanh::lean_closure_set(v___f_4563_, 3, v_examples_4561_);
    v___x_4564_ = l_Lean_Meta_Match_withGoalOf___redArg(
        v_p_4553_,
        v___f_4563_,
        v_a_4554_,
        v_a_4555_,
        v_a_4556_,
        v_a_4557_,
    );
    return v___x_4564_;
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData___boxed(
    mut v_p_4565_: *mut leanh::LeanObject,
    mut v_a_4566_: *mut leanh::LeanObject,
    mut v_a_4567_: *mut leanh::LeanObject,
    mut v_a_4568_: *mut leanh::LeanObject,
    mut v_a_4569_: *mut leanh::LeanObject,
    mut v_a_4570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4571_ = l_Lean_Meta_Match_Problem_toMessageData(
        v_p_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_,
    );
    leanh::lean_dec(v_a_4569_);
    leanh::lean_dec_ref(v_a_4568_);
    leanh::lean_dec(v_a_4567_);
    leanh::lean_dec_ref(v_a_4566_);
    return v_res_4571_;
}
pub unsafe fn l_Lean_Meta_Match_counterExampleToMessageData(
    mut v_cex_4572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4573_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_4572_);
    return v___x_4573_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(
    mut v_a_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4574_) == 0 {
                    v___x_4576_ = l_List_reverse___redArg(v_a_4575_);
                    return v___x_4576_;
                } else {
                    v_head_4577_ = leanh::lean_ctor_get(v_a_4574_, 0);
                    v_tail_4578_ = leanh::lean_ctor_get(v_a_4574_, 1);
                    v_isSharedCheck_4587_ = (!leanh::lean_is_exclusive(v_a_4574_)) as u8;
                    if v_isSharedCheck_4587_ == 0 {
                        v___x_4580_ = v_a_4574_;
                        v_isShared_4581_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4578_);
                        leanh::lean_inc(v_head_4577_);
                        leanh::lean_dec(v_a_4574_);
                        v___x_4580_ = leanh::lean_box(0);
                        v_isShared_4581_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4582_ = l_Lean_Meta_Match_examplesToMessageData(v_head_4577_);
                if v_isShared_4581_ == 0 {
                    leanh::lean_ctor_set(v___x_4580_, 1, v_a_4575_);
                    leanh::lean_ctor_set(v___x_4580_, 0, v___x_4582_);
                    v___x_4584_ = v___x_4580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4586_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_a_4575_);
                    v___x_4584_ = v_reuseFailAlloc_4586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4574_ = v_tail_4578_;
                v_a_4575_ = v___x_4584_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_counterExamplesToMessageData(
    mut v_cexs_4588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4589_ = lean_array_to_list(v_cexs_4588_);
    v___x_4590_ = leanh::lean_box(0);
    v___x_4591_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(
        v___x_4589_,
        v___x_4590_,
    );
    v___x_4592_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once),
        _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4,
    );
    v___x_4593_ = l_Lean_MessageData_joinSep(v___x_4591_, v___x_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
    mut v_msg_4594_: *mut leanh::LeanObject,
    mut v___y_4595_: *mut leanh::LeanObject,
    mut v___y_4596_: *mut leanh::LeanObject,
    mut v___y_4597_: *mut leanh::LeanObject,
    mut v___y_4598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4600_ = leanh::lean_ctor_get(v___y_4597_, 5);
                v___x_4601_ =
                    l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
                        v_msg_4594_,
                        v___y_4595_,
                        v___y_4596_,
                        v___y_4597_,
                        v___y_4598_,
                    );
                v_a_4602_ = leanh::lean_ctor_get(v___x_4601_, 0);
                v_isSharedCheck_4610_ = (!leanh::lean_is_exclusive(v___x_4601_)) as u8;
                if v_isSharedCheck_4610_ == 0 {
                    v___x_4604_ = v___x_4601_;
                    v_isShared_4605_ = v_isSharedCheck_4610_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4602_);
                    leanh::lean_dec(v___x_4601_);
                    v___x_4604_ = leanh::lean_box(0);
                    v_isShared_4605_ = v_isSharedCheck_4610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4600_);
                v___x_4606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4606_, 0, v_ref_4600_);
                leanh::lean_ctor_set(v___x_4606_, 1, v_a_4602_);
                if v_isShared_4605_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4604_, 1);
                    leanh::lean_ctor_set(v___x_4604_, 0, v___x_4606_);
                    v___x_4608_ = v___x_4604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(
    mut v_msg_4611_: *mut leanh::LeanObject,
    mut v___y_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
        v_msg_4611_,
        v___y_4612_,
        v___y_4613_,
        v___y_4614_,
        v___y_4615_,
    );
    leanh::lean_dec(v___y_4615_);
    leanh::lean_dec_ref(v___y_4614_);
    leanh::lean_dec(v___y_4613_);
    leanh::lean_dec_ref(v___y_4612_);
    return v_res_4617_;
}
pub unsafe fn _init_l_Lean_Meta_Match_toPattern___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Lean_Meta_Match_toPattern___closed__0;
    v___x_4620_ = l_Lean_stringToMessageData(v___x_4619_);
    return v___x_4620_;
}
pub unsafe fn _init_l_Lean_Meta_Match_toPattern___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4622_ = l_Lean_Meta_Match_toPattern___closed__2;
    v___x_4623_ = l_Lean_stringToMessageData(v___x_4622_);
    return v___x_4623_;
}
pub unsafe fn _init_l_Lean_Meta_Match_toPattern___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ = leanh::lean_box(0);
    v_dummy_4625_ = l_Lean_Expr_sort___override(v___x_4624_);
    return v_dummy_4625_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(
    mut v_sz_4626_: usize,
    mut v_i_4627_: usize,
    mut v_bs_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: usize = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4634_ = lean_usize_dec_lt(v_i_4627_, v_sz_4626_);
                if v___x_4634_ == 0 {
                    v___x_4635_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4635_, 0, v_bs_4628_);
                    return v___x_4635_;
                } else {
                    v_v_4636_ = lean_array_uget_borrowed(v_bs_4628_, v_i_4627_);
                    leanh::lean_inc(v_v_4636_);
                    v___x_4637_ = l_Lean_Meta_Match_toPattern(
                        v_v_4636_,
                        v___y_4629_,
                        v___y_4630_,
                        v___y_4631_,
                        v___y_4632_,
                    );
                    if leanh::lean_obj_tag(v___x_4637_) == 0 {
                        v_a_4638_ = leanh::lean_ctor_get(v___x_4637_, 0);
                        leanh::lean_inc(v_a_4638_);
                        leanh::lean_dec_ref_known(v___x_4637_, 1);
                        v___x_4639_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4640_ = lean_array_uset(v_bs_4628_, v_i_4627_, v___x_4639_);
                        v___x_4641_ = 1usize;
                        v___x_4642_ = lean_usize_add(v_i_4627_, v___x_4641_);
                        v___x_4643_ = lean_array_uset(v_bs_x27_4640_, v_i_4627_, v_a_4638_);
                        v_i_4627_ = v___x_4642_;
                        v_bs_4628_ = v___x_4643_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4628_);
                        v_a_4645_ = leanh::lean_ctor_get(v___x_4637_, 0);
                        v_isSharedCheck_4652_ =
                            (!leanh::lean_is_exclusive(v___x_4637_)) as u8;
                        if v_isSharedCheck_4652_ == 0 {
                            v___x_4647_ = v___x_4637_;
                            v_isShared_4648_ = v_isSharedCheck_4652_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4645_);
                            leanh::lean_dec(v___x_4637_);
                            v___x_4647_ = leanh::lean_box(0);
                            v_isShared_4648_ = v_isSharedCheck_4652_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4648_ == 0 {
                    v___x_4650_ = v___x_4647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
                    v___x_4650_ = v_reuseFailAlloc_4651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_toPattern(
    mut v_e_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
    mut v_a_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___y_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4708_: u8 = 0;
    let mut v___x_4709_: u8 = 0;
    let mut v___x_4710_: u8 = 0;
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4741_: usize = 0;
    let mut v___x_4742_: usize = 0;
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v_name_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut v_a_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: u8 = 0;
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4778_: u8 = 0;
    let mut v_a_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4783_: u8 = 0;
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4797_: u8 = 0;
    let mut v_a_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut v_val_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut v_a_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4828_: u8 = 0;
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4832_: u8 = 0;
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut v_val_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4668_ = l_Lean_inaccessible_x3f(v_e_4653_);
                if leanh::lean_obj_tag(v___x_4668_) == 0 {
                    v___x_4669_ = l_Lean_Expr_arrayLit_x3f(v_e_4653_);
                    if leanh::lean_obj_tag(v___x_4669_) == 0 {
                        v___x_4670_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_4653_);
                        if leanh::lean_obj_tag(v___x_4670_) == 1 {
                            leanh::lean_dec_ref(v_e_4653_);
                            v_val_4671_ = leanh::lean_ctor_get(v___x_4670_, 0);
                            leanh::lean_inc(v_val_4671_);
                            leanh::lean_dec_ref_known(v___x_4670_, 1);
                            v___x_4672_ = leanh::lean_unsigned_to_nat(2);
                            v___x_4673_ = l_Lean_Expr_getAppNumArgs(v_val_4671_);
                            v___x_4674_ = lean_nat_sub(v___x_4673_, v___x_4672_);
                            v___x_4675_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4676_ = lean_nat_sub(v___x_4674_, v___x_4675_);
                            leanh::lean_dec(v___x_4674_);
                            v___x_4677_ = l_Lean_Expr_getRevArg_x21(v_val_4671_, v___x_4676_);
                            v___x_4678_ = l_Lean_Meta_Match_toPattern(
                                v___x_4677_,
                                v_a_4654_,
                                v_a_4655_,
                                v_a_4656_,
                                v_a_4657_,
                            );
                            if leanh::lean_obj_tag(v___x_4678_) == 0 {
                                v_a_4679_ = leanh::lean_ctor_get(v___x_4678_, 0);
                                v_isSharedCheck_4703_ =
                                    (!leanh::lean_is_exclusive(v___x_4678_)) as u8;
                                if v_isSharedCheck_4703_ == 0 {
                                    v___x_4681_ = v___x_4678_;
                                    v_isShared_4682_ = v_isSharedCheck_4703_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4679_);
                                    leanh::lean_dec(v___x_4678_);
                                    v___x_4681_ = leanh::lean_box(0);
                                    v_isShared_4682_ = v_isSharedCheck_4703_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_4673_);
                                leanh::lean_dec(v_val_4671_);
                                return v___x_4678_;
                            }
                        } else {
                            leanh::lean_dec(v___x_4670_);
                            leanh::lean_inc_ref(v_e_4653_);
                            v___x_4704_ = l_Lean_Meta_isMatchValue(
                                v_e_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_,
                            );
                            if leanh::lean_obj_tag(v___x_4704_) == 0 {
                                v_a_4705_ = leanh::lean_ctor_get(v___x_4704_, 0);
                                v_isSharedCheck_4797_ =
                                    (!leanh::lean_is_exclusive(v___x_4704_)) as u8;
                                if v_isSharedCheck_4797_ == 0 {
                                    v___x_4707_ = v___x_4704_;
                                    v_isShared_4708_ = v_isSharedCheck_4797_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4705_);
                                    leanh::lean_dec(v___x_4704_);
                                    v___x_4707_ = leanh::lean_box(0);
                                    v_isShared_4708_ = v_isSharedCheck_4797_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_4653_);
                                v_a_4798_ = leanh::lean_ctor_get(v___x_4704_, 0);
                                v_isSharedCheck_4805_ =
                                    (!leanh::lean_is_exclusive(v___x_4704_)) as u8;
                                if v_isSharedCheck_4805_ == 0 {
                                    v___x_4800_ = v___x_4704_;
                                    v_isShared_4801_ = v_isSharedCheck_4805_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4798_);
                                    leanh::lean_dec(v___x_4704_);
                                    v___x_4800_ = leanh::lean_box(0);
                                    v_isShared_4801_ = v_isSharedCheck_4805_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_4653_);
                        v_val_4806_ = leanh::lean_ctor_get(v___x_4669_, 0);
                        leanh::lean_inc(v_val_4806_);
                        leanh::lean_dec_ref_known(v___x_4669_, 1);
                        v_fst_4807_ = leanh::lean_ctor_get(v_val_4806_, 0);
                        v_snd_4808_ = leanh::lean_ctor_get(v_val_4806_, 1);
                        v_isSharedCheck_4833_ =
                            (!leanh::lean_is_exclusive(v_val_4806_)) as u8;
                        if v_isSharedCheck_4833_ == 0 {
                            v___x_4810_ = v_val_4806_;
                            v_isShared_4811_ = v_isSharedCheck_4833_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_4808_);
                            leanh::lean_inc(v_fst_4807_);
                            leanh::lean_dec(v_val_4806_);
                            v___x_4810_ = leanh::lean_box(0);
                            v_isShared_4811_ = v_isSharedCheck_4833_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4653_);
                    v_val_4834_ = leanh::lean_ctor_get(v___x_4668_, 0);
                    v_isSharedCheck_4842_ = (!leanh::lean_is_exclusive(v___x_4668_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4836_ = v___x_4668_;
                        v_isShared_4837_ = v_isSharedCheck_4842_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4834_);
                        leanh::lean_dec(v___x_4668_);
                        v___x_4836_ = leanh::lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4842_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4664_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1_once),
                    _init_l_Lean_Meta_Match_toPattern___closed__1,
                );
                v___x_4665_ = l_Lean_indentExpr(v_e_4653_);
                v___x_4666_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4666_, 0, v___x_4664_);
                leanh::lean_ctor_set(v___x_4666_, 1, v___x_4665_);
                v___x_4667_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
                    v___x_4666_,
                    v___y_4660_,
                    v___y_4661_,
                    v___y_4662_,
                    v___y_4663_,
                );
                return v___x_4667_;
            }
            2 => {
                v___x_4690_ = lean_nat_sub(v___x_4673_, v___x_4675_);
                v___x_4691_ = lean_nat_sub(v___x_4690_, v___x_4675_);
                leanh::lean_dec(v___x_4690_);
                v___x_4692_ = l_Lean_Expr_getRevArg_x21(v_val_4671_, v___x_4691_);
                if leanh::lean_obj_tag(v___x_4692_) == 1 {
                    v_fvarId_4693_ = leanh::lean_ctor_get(v___x_4692_, 0);
                    leanh::lean_inc(v_fvarId_4693_);
                    leanh::lean_dec_ref_known(v___x_4692_, 1);
                    v___x_4694_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4695_ = lean_nat_sub(v___x_4673_, v___x_4694_);
                    leanh::lean_dec(v___x_4673_);
                    v___x_4696_ = lean_nat_sub(v___x_4695_, v___x_4675_);
                    leanh::lean_dec(v___x_4695_);
                    v___x_4697_ = l_Lean_Expr_getRevArg_x21(v_val_4671_, v___x_4696_);
                    leanh::lean_dec(v_val_4671_);
                    if leanh::lean_obj_tag(v___x_4697_) == 1 {
                        v_fvarId_4698_ = leanh::lean_ctor_get(v___x_4697_, 0);
                        leanh::lean_inc(v_fvarId_4698_);
                        leanh::lean_dec_ref_known(v___x_4697_, 1);
                        v___x_4699_ = leanh::lean_alloc_ctor(5, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_4699_, 0, v_fvarId_4693_);
                        leanh::lean_ctor_set(v___x_4699_, 1, v_a_4679_);
                        leanh::lean_ctor_set(v___x_4699_, 2, v_fvarId_4698_);
                        if v_isShared_4682_ == 0 {
                            leanh::lean_ctor_set(v___x_4681_, 0, v___x_4699_);
                            v___x_4701_ = v___x_4681_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4702_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4699_);
                            v___x_4701_ = v_reuseFailAlloc_4702_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4697_);
                        leanh::lean_dec(v_fvarId_4693_);
                        leanh::lean_del_object(v___x_4681_);
                        leanh::lean_dec(v_a_4679_);
                        v___y_4684_ = v_a_4654_;
                        v___y_4685_ = v_a_4655_;
                        v___y_4686_ = v_a_4656_;
                        v___y_4687_ = v_a_4657_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4692_);
                    leanh::lean_del_object(v___x_4681_);
                    leanh::lean_dec(v_a_4679_);
                    leanh::lean_dec(v___x_4673_);
                    leanh::lean_dec(v_val_4671_);
                    v___y_4684_ = v_a_4654_;
                    v___y_4685_ = v_a_4655_;
                    v___y_4686_ = v_a_4656_;
                    v___y_4687_ = v_a_4657_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4688_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__3_once),
                    _init_l_Lean_Meta_Match_toPattern___closed__3,
                );
                v___x_4689_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
                    v___x_4688_,
                    v___y_4684_,
                    v___y_4685_,
                    v___y_4686_,
                    v___y_4687_,
                );
                return v___x_4689_;
            }
            4 => {
                return v___x_4701_;
            }
            5 => {
                v___x_4709_ = (leanh::lean_unbox(v_a_4705_) as u8);
                leanh::lean_dec(v_a_4705_);
                if v___x_4709_ == 0 {
                    v___x_4710_ = l_Lean_Expr_isFVar(v_e_4653_);
                    if v___x_4710_ == 0 {
                        leanh::lean_del_object(v___x_4707_);
                        leanh::lean_inc(v_a_4657_);
                        leanh::lean_inc_ref(v_a_4656_);
                        leanh::lean_inc(v_a_4655_);
                        leanh::lean_inc_ref(v_a_4654_);
                        leanh::lean_inc_ref(v_e_4653_);
                        v___x_4711_ =
                            lean_whnf(v_e_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
                        if leanh::lean_obj_tag(v___x_4711_) == 0 {
                            v_a_4712_ = leanh::lean_ctor_get(v___x_4711_, 0);
                            leanh::lean_inc(v_a_4712_);
                            leanh::lean_dec_ref_known(v___x_4711_, 1);
                            v___x_4713_ = lean_expr_eqv(v_a_4712_, v_e_4653_);
                            if v___x_4713_ == 0 {
                                leanh::lean_dec_ref(v_e_4653_);
                                v_e_4653_ = v_a_4712_;
                                state = 0;
                                continue;
                            } else {
                                if v___x_4710_ == 0 {
                                    leanh::lean_dec(v_a_4712_);
                                    v___x_4715_ = l_Lean_Expr_getAppFn(v_e_4653_);
                                    if leanh::lean_obj_tag(v___x_4715_) == 4 {
                                        v_declName_4716_ =
                                            leanh::lean_ctor_get(v___x_4715_, 0);
                                        leanh::lean_inc(v_declName_4716_);
                                        v_us_4717_ = leanh::lean_ctor_get(v___x_4715_, 1);
                                        leanh::lean_inc(v_us_4717_);
                                        leanh::lean_dec_ref_known(v___x_4715_, 2);
                                        v___x_4718_ = lean_st_ref_get(v_a_4657_);
                                        v_env_4719_ = leanh::lean_ctor_get(v___x_4718_, 0);
                                        leanh::lean_inc_ref(v_env_4719_);
                                        leanh::lean_dec(v___x_4718_);
                                        v___x_4720_ = l_Lean_Environment_find_x3f(
                                            v_env_4719_,
                                            v_declName_4716_,
                                            v___x_4710_,
                                        );
                                        if leanh::lean_obj_tag(v___x_4720_) == 0 {
                                            leanh::lean_dec(v_us_4717_);
                                            v___y_4660_ = v_a_4654_;
                                            v___y_4661_ = v_a_4655_;
                                            v___y_4662_ = v_a_4656_;
                                            v___y_4663_ = v_a_4657_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_val_4721_ =
                                                leanh::lean_ctor_get(v___x_4720_, 0);
                                            leanh::lean_inc(v_val_4721_);
                                            leanh::lean_dec_ref_known(v___x_4720_, 1);
                                            if leanh::lean_obj_tag(v_val_4721_) == 6 {
                                                v_val_4722_ =
                                                    leanh::lean_ctor_get(v_val_4721_, 0);
                                                leanh::lean_inc_ref(v_val_4722_);
                                                leanh::lean_dec_ref_known(v_val_4721_, 1);
                                                v_toConstantVal_4723_ =
                                                    leanh::lean_ctor_get(v_val_4722_, 0);
                                                leanh::lean_inc_ref(v_toConstantVal_4723_);
                                                v_numParams_4724_ =
                                                    leanh::lean_ctor_get(v_val_4722_, 3);
                                                leanh::lean_inc(v_numParams_4724_);
                                                v_numFields_4725_ =
                                                    leanh::lean_ctor_get(v_val_4722_, 4);
                                                leanh::lean_inc(v_numFields_4725_);
                                                leanh::lean_dec_ref(v_val_4722_);
                                                v_nargs_4726_ =
                                                    l_Lean_Expr_getAppNumArgs(v_e_4653_);
                                                v_dummy_4727_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__4_once), _init_l_Lean_Meta_Match_toPattern___closed__4);
                                                leanh::lean_inc(v_nargs_4726_);
                                                v___x_4728_ =
                                                    lean_mk_array(v_nargs_4726_, v_dummy_4727_);
                                                v___x_4729_ = leanh::lean_unsigned_to_nat(1);
                                                v___x_4730_ =
                                                    lean_nat_sub(v_nargs_4726_, v___x_4729_);
                                                leanh::lean_dec(v_nargs_4726_);
                                                leanh::lean_inc_ref(v_e_4653_);
                                                v___x_4731_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4653_, v___x_4728_, v___x_4730_);
                                                v___x_4764_ = lean_array_get_size(v___x_4731_);
                                                v___x_4765_ = lean_nat_add(
                                                    v_numParams_4724_,
                                                    v_numFields_4725_,
                                                );
                                                leanh::lean_dec(v_numFields_4725_);
                                                v___x_4766_ =
                                                    lean_nat_dec_eq(v___x_4764_, v___x_4765_);
                                                leanh::lean_dec(v___x_4765_);
                                                if v___x_4766_ == 0 {
                                                    v___x_4767_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1_once), _init_l_Lean_Meta_Match_toPattern___closed__1);
                                                    v___x_4768_ = l_Lean_indentExpr(v_e_4653_);
                                                    v___x_4769_ = leanh::lean_alloc_ctor(
                                                        7,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4769_,
                                                        0,
                                                        v___x_4767_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4769_,
                                                        1,
                                                        v___x_4768_,
                                                    );
                                                    v___x_4770_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_4769_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
                                                    if leanh::lean_obj_tag(v___x_4770_) == 0
                                                    {
                                                        leanh::lean_dec_ref_known(
                                                            v___x_4770_,
                                                            1,
                                                        );
                                                        v___y_4733_ = v_a_4654_;
                                                        v___y_4734_ = v_a_4655_;
                                                        v___y_4735_ = v_a_4656_;
                                                        v___y_4736_ = v_a_4657_;
                                                        state = 6;
                                                        continue;
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_4731_);
                                                        leanh::lean_dec(v_numParams_4724_);
                                                        leanh::lean_dec_ref(
                                                            v_toConstantVal_4723_,
                                                        );
                                                        leanh::lean_dec(v_us_4717_);
                                                        v_a_4771_ = leanh::lean_ctor_get(
                                                            v___x_4770_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4778_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_4770_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4778_ == 0 {
                                                            v___x_4773_ = v___x_4770_;
                                                            v_isShared_4774_ =
                                                                v_isSharedCheck_4778_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_4771_);
                                                            leanh::lean_dec(v___x_4770_);
                                                            v___x_4773_ = leanh::lean_box(0);
                                                            v_isShared_4774_ =
                                                                v_isSharedCheck_4778_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v_e_4653_);
                                                    v___y_4733_ = v_a_4654_;
                                                    v___y_4734_ = v_a_4655_;
                                                    v___y_4735_ = v_a_4656_;
                                                    v___y_4736_ = v_a_4657_;
                                                    state = 6;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_val_4721_);
                                                leanh::lean_dec(v_us_4717_);
                                                v___y_4660_ = v_a_4654_;
                                                v___y_4661_ = v_a_4655_;
                                                v___y_4662_ = v_a_4656_;
                                                v___y_4663_ = v_a_4657_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_4715_);
                                        v___y_4660_ = v_a_4654_;
                                        v___y_4661_ = v_a_4655_;
                                        v___y_4662_ = v_a_4656_;
                                        v___y_4663_ = v_a_4657_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_e_4653_);
                                    v_e_4653_ = v_a_4712_;
                                    state = 0;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_4653_);
                            v_a_4780_ = leanh::lean_ctor_get(v___x_4711_, 0);
                            v_isSharedCheck_4787_ =
                                (!leanh::lean_is_exclusive(v___x_4711_)) as u8;
                            if v_isSharedCheck_4787_ == 0 {
                                v___x_4782_ = v___x_4711_;
                                v_isShared_4783_ = v_isSharedCheck_4787_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4780_);
                                leanh::lean_dec(v___x_4711_);
                                v___x_4782_ = leanh::lean_box(0);
                                v_isShared_4783_ = v_isSharedCheck_4787_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___x_4788_ = l_Lean_Expr_fvarId_x21(v_e_4653_);
                        leanh::lean_dec_ref(v_e_4653_);
                        v___x_4789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                        if v_isShared_4708_ == 0 {
                            leanh::lean_ctor_set(v___x_4707_, 0, v___x_4789_);
                            v___x_4791_ = v___x_4707_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_4792_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
                            v___x_4791_ = v_reuseFailAlloc_4792_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    v___x_4793_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4793_, 0, v_e_4653_);
                    if v_isShared_4708_ == 0 {
                        leanh::lean_ctor_set(v___x_4707_, 0, v___x_4793_);
                        v___x_4795_ = v___x_4707_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4796_, 0, v___x_4793_);
                        v___x_4795_ = v_reuseFailAlloc_4796_;
                        state = 16;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4737_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc(v_numParams_4724_);
                v___x_4738_ = l_Array_extract___redArg(v___x_4731_, v___x_4737_, v_numParams_4724_);
                v___x_4739_ = lean_array_get_size(v___x_4731_);
                v___x_4740_ = l_Array_extract___redArg(v___x_4731_, v_numParams_4724_, v___x_4739_);
                leanh::lean_dec_ref(v___x_4731_);
                v_sz_4741_ = lean_array_size(v___x_4740_);
                v___x_4742_ = 0usize;
                v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_4741_, v___x_4742_, v___x_4740_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
                if leanh::lean_obj_tag(v___x_4743_) == 0 {
                    v_a_4744_ = leanh::lean_ctor_get(v___x_4743_, 0);
                    v_isSharedCheck_4755_ = (!leanh::lean_is_exclusive(v___x_4743_)) as u8;
                    if v_isSharedCheck_4755_ == 0 {
                        v___x_4746_ = v___x_4743_;
                        v_isShared_4747_ = v_isSharedCheck_4755_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4744_);
                        leanh::lean_dec(v___x_4743_);
                        v___x_4746_ = leanh::lean_box(0);
                        v_isShared_4747_ = v_isSharedCheck_4755_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4738_);
                    leanh::lean_dec_ref(v_toConstantVal_4723_);
                    leanh::lean_dec(v_us_4717_);
                    v_a_4756_ = leanh::lean_ctor_get(v___x_4743_, 0);
                    v_isSharedCheck_4763_ = (!leanh::lean_is_exclusive(v___x_4743_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4758_ = v___x_4743_;
                        v_isShared_4759_ = v_isSharedCheck_4763_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4756_);
                        leanh::lean_dec(v___x_4743_);
                        v___x_4758_ = leanh::lean_box(0);
                        v_isShared_4759_ = v_isSharedCheck_4763_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v_name_4748_ = leanh::lean_ctor_get(v_toConstantVal_4723_, 0);
                leanh::lean_inc(v_name_4748_);
                leanh::lean_dec_ref(v_toConstantVal_4723_);
                v___x_4749_ = lean_array_to_list(v___x_4738_);
                v___x_4750_ = lean_array_to_list(v_a_4744_);
                v___x_4751_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4751_, 0, v_name_4748_);
                leanh::lean_ctor_set(v___x_4751_, 1, v_us_4717_);
                leanh::lean_ctor_set(v___x_4751_, 2, v___x_4749_);
                leanh::lean_ctor_set(v___x_4751_, 3, v___x_4750_);
                if v_isShared_4747_ == 0 {
                    leanh::lean_ctor_set(v___x_4746_, 0, v___x_4751_);
                    v___x_4753_ = v___x_4746_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
                    v___x_4753_ = v_reuseFailAlloc_4754_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4753_;
            }
            9 => {
                if v_isShared_4759_ == 0 {
                    v___x_4761_ = v___x_4758_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
                    v___x_4761_ = v_reuseFailAlloc_4762_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4761_;
            }
            11 => {
                if v_isShared_4774_ == 0 {
                    v___x_4776_ = v___x_4773_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
                    v___x_4776_ = v_reuseFailAlloc_4777_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4776_;
            }
            13 => {
                if v_isShared_4783_ == 0 {
                    v___x_4785_ = v___x_4782_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4785_;
            }
            15 => {
                return v___x_4791_;
            }
            16 => {
                return v___x_4795_;
            }
            17 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4803_;
            }
            19 => {
                v___x_4812_ = leanh::lean_box(0);
                v___x_4813_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(
                    v_snd_4808_,
                    v___x_4812_,
                    v_a_4654_,
                    v_a_4655_,
                    v_a_4656_,
                    v_a_4657_,
                );
                if leanh::lean_obj_tag(v___x_4813_) == 0 {
                    v_a_4814_ = leanh::lean_ctor_get(v___x_4813_, 0);
                    v_isSharedCheck_4824_ = (!leanh::lean_is_exclusive(v___x_4813_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v___x_4816_ = v___x_4813_;
                        v_isShared_4817_ = v_isSharedCheck_4824_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4814_);
                        leanh::lean_dec(v___x_4813_);
                        v___x_4816_ = leanh::lean_box(0);
                        v_isShared_4817_ = v_isSharedCheck_4824_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4810_);
                    leanh::lean_dec(v_fst_4807_);
                    v_a_4825_ = leanh::lean_ctor_get(v___x_4813_, 0);
                    v_isSharedCheck_4832_ = (!leanh::lean_is_exclusive(v___x_4813_)) as u8;
                    if v_isSharedCheck_4832_ == 0 {
                        v___x_4827_ = v___x_4813_;
                        v_isShared_4828_ = v_isSharedCheck_4832_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4825_);
                        leanh::lean_dec(v___x_4813_);
                        v___x_4827_ = leanh::lean_box(0);
                        v_isShared_4828_ = v_isSharedCheck_4832_;
                        state = 23;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_4811_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4810_, 4);
                    leanh::lean_ctor_set(v___x_4810_, 1, v_a_4814_);
                    v___x_4819_ = v___x_4810_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4823_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_fst_4807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4823_, 1, v_a_4814_);
                    v___x_4819_ = v_reuseFailAlloc_4823_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4817_ == 0 {
                    leanh::lean_ctor_set(v___x_4816_, 0, v___x_4819_);
                    v___x_4821_ = v___x_4816_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4821_;
            }
            23 => {
                if v_isShared_4828_ == 0 {
                    v___x_4830_ = v___x_4827_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
                    v___x_4830_ = v_reuseFailAlloc_4831_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4830_;
            }
            25 => {
                if v_isShared_4837_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4836_, 0);
                    v___x_4839_ = v___x_4836_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_val_4834_);
                    v___x_4839_ = v_reuseFailAlloc_4841_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4840_, 0, v___x_4839_);
                return v___x_4840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(
    mut v_x_4843_: *mut leanh::LeanObject,
    mut v_x_4844_: *mut leanh::LeanObject,
    mut v___y_4845_: *mut leanh::LeanObject,
    mut v___y_4846_: *mut leanh::LeanObject,
    mut v___y_4847_: *mut leanh::LeanObject,
    mut v___y_4848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4856_: u8 = 0;
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4843_) == 0 {
                    v___x_4850_ = l_List_reverse___redArg(v_x_4844_);
                    v___x_4851_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4851_, 0, v___x_4850_);
                    return v___x_4851_;
                } else {
                    v_head_4852_ = leanh::lean_ctor_get(v_x_4843_, 0);
                    v_tail_4853_ = leanh::lean_ctor_get(v_x_4843_, 1);
                    v_isSharedCheck_4871_ = (!leanh::lean_is_exclusive(v_x_4843_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4855_ = v_x_4843_;
                        v_isShared_4856_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4853_);
                        leanh::lean_inc(v_head_4852_);
                        leanh::lean_dec(v_x_4843_);
                        v___x_4855_ = leanh::lean_box(0);
                        v_isShared_4856_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4857_ = l_Lean_Meta_Match_toPattern(
                    v_head_4852_,
                    v___y_4845_,
                    v___y_4846_,
                    v___y_4847_,
                    v___y_4848_,
                );
                if leanh::lean_obj_tag(v___x_4857_) == 0 {
                    v_a_4858_ = leanh::lean_ctor_get(v___x_4857_, 0);
                    leanh::lean_inc(v_a_4858_);
                    leanh::lean_dec_ref_known(v___x_4857_, 1);
                    if v_isShared_4856_ == 0 {
                        leanh::lean_ctor_set(v___x_4855_, 1, v_x_4844_);
                        leanh::lean_ctor_set(v___x_4855_, 0, v_a_4858_);
                        v___x_4860_ = v___x_4855_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4862_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4858_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_x_4844_);
                        v___x_4860_ = v_reuseFailAlloc_4862_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4855_);
                    leanh::lean_dec(v_tail_4853_);
                    leanh::lean_dec(v_x_4844_);
                    v_a_4863_ = leanh::lean_ctor_get(v___x_4857_, 0);
                    v_isSharedCheck_4870_ = (!leanh::lean_is_exclusive(v___x_4857_)) as u8;
                    if v_isSharedCheck_4870_ == 0 {
                        v___x_4865_ = v___x_4857_;
                        v_isShared_4866_ = v_isSharedCheck_4870_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4863_);
                        leanh::lean_dec(v___x_4857_);
                        v___x_4865_ = leanh::lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4870_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4843_ = v_tail_4853_;
                v_x_4844_ = v___x_4860_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4866_ == 0 {
                    v___x_4868_ = v___x_4865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(
    mut v_x_4872_: *mut leanh::LeanObject,
    mut v_x_4873_: *mut leanh::LeanObject,
    mut v___y_4874_: *mut leanh::LeanObject,
    mut v___y_4875_: *mut leanh::LeanObject,
    mut v___y_4876_: *mut leanh::LeanObject,
    mut v___y_4877_: *mut leanh::LeanObject,
    mut v___y_4878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4879_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(
        v_x_4872_,
        v_x_4873_,
        v___y_4874_,
        v___y_4875_,
        v___y_4876_,
        v___y_4877_,
    );
    leanh::lean_dec(v___y_4877_);
    leanh::lean_dec_ref(v___y_4876_);
    leanh::lean_dec(v___y_4875_);
    leanh::lean_dec_ref(v___y_4874_);
    return v_res_4879_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(
    mut v_sz_4880_: *mut leanh::LeanObject,
    mut v_i_4881_: *mut leanh::LeanObject,
    mut v_bs_4882_: *mut leanh::LeanObject,
    mut v___y_4883_: *mut leanh::LeanObject,
    mut v___y_4884_: *mut leanh::LeanObject,
    mut v___y_4885_: *mut leanh::LeanObject,
    mut v___y_4886_: *mut leanh::LeanObject,
    mut v___y_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4888_: usize = 0;
    let mut v_i_boxed_4889_: usize = 0;
    let mut v_res_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4888_ = leanh::lean_unbox_usize(v_sz_4880_);
    leanh::lean_dec(v_sz_4880_);
    v_i_boxed_4889_ = leanh::lean_unbox_usize(v_i_4881_);
    leanh::lean_dec(v_i_4881_);
    v_res_4890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_4888_, v_i_boxed_4889_, v_bs_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
    leanh::lean_dec(v___y_4886_);
    leanh::lean_dec_ref(v___y_4885_);
    leanh::lean_dec(v___y_4884_);
    leanh::lean_dec_ref(v___y_4883_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_Meta_Match_toPattern___boxed(
    mut v_e_4891_: *mut leanh::LeanObject,
    mut v_a_4892_: *mut leanh::LeanObject,
    mut v_a_4893_: *mut leanh::LeanObject,
    mut v_a_4894_: *mut leanh::LeanObject,
    mut v_a_4895_: *mut leanh::LeanObject,
    mut v_a_4896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4897_ =
        l_Lean_Meta_Match_toPattern(v_e_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_);
    leanh::lean_dec(v_a_4895_);
    leanh::lean_dec_ref(v_a_4894_);
    leanh::lean_dec(v_a_4893_);
    leanh::lean_dec_ref(v_a_4892_);
    return v_res_4897_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(
    mut v_00_u03b1_4898_: *mut leanh::LeanObject,
    mut v_msg_4899_: *mut leanh::LeanObject,
    mut v___y_4900_: *mut leanh::LeanObject,
    mut v___y_4901_: *mut leanh::LeanObject,
    mut v___y_4902_: *mut leanh::LeanObject,
    mut v___y_4903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
        v_msg_4899_,
        v___y_4900_,
        v___y_4901_,
        v___y_4902_,
        v___y_4903_,
    );
    return v___x_4905_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(
    mut v_00_u03b1_4906_: *mut leanh::LeanObject,
    mut v_msg_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
    mut v___y_4910_: *mut leanh::LeanObject,
    mut v___y_4911_: *mut leanh::LeanObject,
    mut v___y_4912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(
        v_00_u03b1_4906_,
        v_msg_4907_,
        v___y_4908_,
        v___y_4909_,
        v___y_4910_,
        v___y_4911_,
    );
    leanh::lean_dec(v___y_4911_);
    leanh::lean_dec_ref(v___y_4910_);
    leanh::lean_dec(v___y_4909_);
    leanh::lean_dec_ref(v___y_4908_);
    return v_res_4913_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
    v___x_4921_ = lean_string_utf8_byte_size(v___x_4920_);
    return v___x_4921_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(
    mut v_s_4922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    v___x_4923_ = l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
    v___x_4924_ = lean_string_utf8_byte_size(v_s_4922_);
    v___x_4925_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0_once), _init_l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0);
    v___x_4926_ = lean_nat_dec_le(v___x_4925_, v___x_4924_);
    if v___x_4926_ == 0 {
        let mut v___x_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_4922_);
        v___x_4927_ = leanh::lean_box(0);
        return v___x_4927_;
    } else {
        let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4929_: u8 = 0;
        v___x_4928_ = leanh::lean_unsigned_to_nat(0);
        v___x_4929_ = lean_string_memcmp(
            v_s_4922_,
            v___x_4923_,
            v___x_4928_,
            v___x_4928_,
            v___x_4925_,
        );
        if v___x_4929_ == 0 {
            let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_4922_);
            v___x_4930_ = leanh::lean_box(0);
            return v___x_4930_;
        } else {
            let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_4922_);
            v___x_4931_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_4931_, 0, v_s_4922_);
            leanh::lean_ctor_set(v___x_4931_, 1, v___x_4928_);
            leanh::lean_ctor_set(v___x_4931_, 2, v___x_4924_);
            v___x_4932_ = l_String_Slice_pos_x21(v___x_4931_, v___x_4925_);
            leanh::lean_dec_ref_known(v___x_4931_, 3);
            v___x_4933_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_4933_, 0, v_s_4922_);
            leanh::lean_ctor_set(v___x_4933_, 1, v___x_4932_);
            leanh::lean_ctor_set(v___x_4933_, 2, v___x_4924_);
            v___x_4934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4934_, 0, v___x_4933_);
            return v___x_4934_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(
    mut v_s_4935_: *mut leanh::LeanObject,
    mut v_pat_4936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4937_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_4935_);
    return v___x_4937_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(
    mut v_s_4938_: *mut leanh::LeanObject,
    mut v_pat_4939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4940_ =
        l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(
            v_s_4938_,
            v_pat_4939_,
        );
    leanh::lean_dec_ref(v_pat_4939_);
    return v_res_4940_;
}
pub unsafe fn l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(
    mut v_s_4941_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4942_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_4941_);
    if leanh::lean_obj_tag(v___x_4942_) == 0 {
        let mut v___x_4943_: u8 = 0;
        v___x_4943_ = 0;
        return v___x_4943_;
    } else {
        let mut v_val_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: u8 = 0;
        v_val_4944_ = leanh::lean_ctor_get(v___x_4942_, 0);
        leanh::lean_inc(v_val_4944_);
        leanh::lean_dec_ref_known(v___x_4942_, 1);
        v___x_4945_ = l_String_Slice_isNat(v_val_4944_);
        leanh::lean_dec(v_val_4944_);
        return v___x_4945_;
    }
}
pub unsafe fn l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(
    mut v_s_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4947_: u8 = 0;
    let mut v_r_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_4946_);
    v_r_4948_ = leanh::lean_box((v_res_4947_) as usize);
    return v_r_4948_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Value(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Match_instInhabitedPattern_default =
        _init_l_Lean_Meta_Match_instInhabitedPattern_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default);
    l_Lean_Meta_Match_instInhabitedPattern = _init_l_Lean_Meta_Match_instInhabitedPattern();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern);
    l_Lean_Meta_Match_instInhabitedAlt_default = _init_l_Lean_Meta_Match_instInhabitedAlt_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt_default);
    l_Lean_Meta_Match_instInhabitedAlt = _init_l_Lean_Meta_Match_instInhabitedAlt();
    leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_Value(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_Basic(builtin);
}