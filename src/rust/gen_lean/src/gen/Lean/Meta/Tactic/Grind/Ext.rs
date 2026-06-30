// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Ext
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.SynthInstance
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_infer_type, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp4, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_getFalseExpr___redArg,
    l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceAndAssign___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_addNewRawFact,
    l_Lean_Meta_Grind_getGeneration___redArg, l_Lean_Meta_Grind_getMaxGeneration___redArg,
    l_Lean_Meta_Grind_mkEqFalseProof, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1_value: leanh::LeanStringObject<74> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 119, 104, 101, 110, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 110, 103, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 97, 108, 105, 116, 121, 32, 116, 104, 101, 111, 114, 101, 109, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [96, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value:
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
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value:
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
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value:
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
    m_data: [101, 120, 116, 0],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
        15947788021050471391 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value)
            as *mut leanh::LeanObject,
        12545347794981986237 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value:
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
    m_data: [58, 32, 0],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 101, 120, 116,
        101, 110, 115, 105, 111, 110, 97, 108, 105, 116, 121, 32, 116, 104, 101, 111, 114, 101,
        109, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        10, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 116, 101, 114, 109, 115, 32, 99, 111,
        110, 116, 97, 105, 110, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97,
        108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value:
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
    m_data: [109, 112, 0],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value)
            as *mut leanh::LeanObject,
        5647098122476602039 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20_value:
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
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21: u64 = 0;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(
    mut v_e_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_unused_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1401_ = l_Lean_Expr_hasMVar(v_e_1398_);
                if v___x_1401_ == 0 {
                    v___x_1402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1402_, 0, v_e_1398_);
                    return v___x_1402_;
                } else {
                    v___x_1403_ = lean_st_ref_get(v___y_1399_);
                    v_mctx_1404_ = leanh::lean_ctor_get(v___x_1403_, 0);
                    leanh::lean_inc_ref(v_mctx_1404_);
                    leanh::lean_dec(v___x_1403_);
                    v___x_1405_ = l_Lean_instantiateMVarsCore(v_mctx_1404_, v_e_1398_);
                    v_fst_1406_ = leanh::lean_ctor_get(v___x_1405_, 0);
                    leanh::lean_inc(v_fst_1406_);
                    v_snd_1407_ = leanh::lean_ctor_get(v___x_1405_, 1);
                    leanh::lean_inc(v_snd_1407_);
                    leanh::lean_dec_ref(v___x_1405_);
                    v___x_1408_ = lean_st_ref_take(v___y_1399_);
                    v_cache_1409_ = leanh::lean_ctor_get(v___x_1408_, 1);
                    v_zetaDeltaFVarIds_1410_ = leanh::lean_ctor_get(v___x_1408_, 2);
                    v_postponed_1411_ = leanh::lean_ctor_get(v___x_1408_, 3);
                    v_diag_1412_ = leanh::lean_ctor_get(v___x_1408_, 4);
                    v_isSharedCheck_1421_ = (!leanh::lean_is_exclusive(v___x_1408_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v_unused_1422_ = leanh::lean_ctor_get(v___x_1408_, 0);
                        leanh::lean_dec(v_unused_1422_);
                        v___x_1414_ = v___x_1408_;
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1412_);
                        leanh::lean_inc(v_postponed_1411_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1410_);
                        leanh::lean_inc(v_cache_1409_);
                        leanh::lean_dec(v___x_1408_);
                        v___x_1414_ = leanh::lean_box(0);
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1415_ == 0 {
                    leanh::lean_ctor_set(v___x_1414_, 0, v_snd_1407_);
                    v___x_1417_ = v___x_1414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_snd_1407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_cache_1409_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1420_,
                        2,
                        v_zetaDeltaFVarIds_1410_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_postponed_1411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_diag_1412_);
                    v___x_1417_ = v_reuseFailAlloc_1420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1418_ = lean_st_ref_set(v___y_1399_, v___x_1417_);
                v___x_1419_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1419_, 0, v_fst_1406_);
                return v___x_1419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(
    mut v_e_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(
            v_e_1423_,
            v___y_1424_,
        );
    leanh::lean_dec(v___y_1424_);
    return v_res_1426_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(
    mut v_e_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
    mut v___y_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
    mut v___y_1436_: *mut leanh::LeanObject,
    mut v___y_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(
            v_e_1427_,
            v___y_1435_,
        );
    return v___x_1439_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(
    mut v_e_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
    mut v___y_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(
        v_e_1440_,
        v___y_1441_,
        v___y_1442_,
        v___y_1443_,
        v___y_1444_,
        v___y_1445_,
        v___y_1446_,
        v___y_1447_,
        v___y_1448_,
        v___y_1449_,
        v___y_1450_,
    );
    leanh::lean_dec(v___y_1450_);
    leanh::lean_dec_ref(v___y_1449_);
    leanh::lean_dec(v___y_1448_);
    leanh::lean_dec_ref(v___y_1447_);
    leanh::lean_dec(v___y_1446_);
    leanh::lean_dec_ref(v___y_1445_);
    leanh::lean_dec(v___y_1444_);
    leanh::lean_dec_ref(v___y_1443_);
    leanh::lean_dec(v___y_1442_);
    leanh::lean_dec(v___y_1441_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(
    mut v_k_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
    mut v___y_1455_: *mut leanh::LeanObject,
    mut v___y_1456_: *mut leanh::LeanObject,
    mut v___y_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1459_);
    leanh::lean_inc_ref(v___y_1458_);
    leanh::lean_inc(v___y_1457_);
    leanh::lean_inc_ref(v___y_1456_);
    leanh::lean_inc(v___y_1455_);
    leanh::lean_inc(v___y_1454_);
    v___x_1465_ = leanh::lean_apply_11(
        v_k_1453_,
        v___y_1454_,
        v___y_1455_,
        v___y_1456_,
        v___y_1457_,
        v___y_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
        v___y_1463_,
        leanh::lean_box(0),
    );
    return v___x_1465_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(
    mut v_k_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
    mut v___y_1475_: *mut leanh::LeanObject,
    mut v___y_1476_: *mut leanh::LeanObject,
    mut v___y_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(v_k_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
    leanh::lean_dec(v___y_1472_);
    leanh::lean_dec_ref(v___y_1471_);
    leanh::lean_dec(v___y_1470_);
    leanh::lean_dec_ref(v___y_1469_);
    leanh::lean_dec(v___y_1468_);
    leanh::lean_dec(v___y_1467_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(
    mut v_k_1479_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_1480_: u8,
    mut v___y_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
    mut v___y_1488_: *mut leanh::LeanObject,
    mut v___y_1489_: *mut leanh::LeanObject,
    mut v___y_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1486_);
                leanh::lean_inc_ref(v___y_1485_);
                leanh::lean_inc(v___y_1484_);
                leanh::lean_inc_ref(v___y_1483_);
                leanh::lean_inc(v___y_1482_);
                leanh::lean_inc(v___y_1481_);
                v___f_1492_ = leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 7);
                leanh::lean_closure_set(v___f_1492_, 0, v_k_1479_);
                leanh::lean_closure_set(v___f_1492_, 1, v___y_1481_);
                leanh::lean_closure_set(v___f_1492_, 2, v___y_1482_);
                leanh::lean_closure_set(v___f_1492_, 3, v___y_1483_);
                leanh::lean_closure_set(v___f_1492_, 4, v___y_1484_);
                leanh::lean_closure_set(v___f_1492_, 5, v___y_1485_);
                leanh::lean_closure_set(v___f_1492_, 6, v___y_1486_);
                v___x_1493_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_1480_,
                    v___f_1492_,
                    v___y_1487_,
                    v___y_1488_,
                    v___y_1489_,
                    v___y_1490_,
                );
                if leanh::lean_obj_tag(v___x_1493_) == 0 {
                    return v___x_1493_;
                } else {
                    v_a_1494_ = leanh::lean_ctor_get(v___x_1493_, 0);
                    v_isSharedCheck_1501_ = (!leanh::lean_is_exclusive(v___x_1493_)) as u8;
                    if v_isSharedCheck_1501_ == 0 {
                        v___x_1496_ = v___x_1493_;
                        v_isShared_1497_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1494_);
                        leanh::lean_dec(v___x_1493_);
                        v___x_1496_ = leanh::lean_box(0);
                        v_isShared_1497_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1497_ == 0 {
                    v___x_1499_ = v___x_1496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
                    v___x_1499_ = v_reuseFailAlloc_1500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(
    mut v_k_1502_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
    mut v___y_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v___y_1510_: *mut leanh::LeanObject,
    mut v___y_1511_: *mut leanh::LeanObject,
    mut v___y_1512_: *mut leanh::LeanObject,
    mut v___y_1513_: *mut leanh::LeanObject,
    mut v___y_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1515_: u8 = 0;
    let mut v_res_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1515_ =
        (leanh::lean_unbox(v_allowLevelAssignments_1503_) as u8);
    v_res_1516_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_1502_, v_allowLevelAssignments_boxed_1515_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
    leanh::lean_dec(v___y_1513_);
    leanh::lean_dec_ref(v___y_1512_);
    leanh::lean_dec(v___y_1511_);
    leanh::lean_dec_ref(v___y_1510_);
    leanh::lean_dec(v___y_1509_);
    leanh::lean_dec_ref(v___y_1508_);
    leanh::lean_dec(v___y_1507_);
    leanh::lean_dec_ref(v___y_1506_);
    leanh::lean_dec(v___y_1505_);
    leanh::lean_dec(v___y_1504_);
    return v_res_1516_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(
    mut v_00_u03b1_1517_: *mut leanh::LeanObject,
    mut v_k_1518_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_1519_: u8,
    mut v___y_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_1518_, v_allowLevelAssignments_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
    return v___x_1531_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(
    mut v_00_u03b1_1532_: *mut leanh::LeanObject,
    mut v_k_1533_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
    mut v___y_1543_: *mut leanh::LeanObject,
    mut v___y_1544_: *mut leanh::LeanObject,
    mut v___y_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1546_: u8 = 0;
    let mut v_res_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1546_ =
        (leanh::lean_unbox(v_allowLevelAssignments_1534_) as u8);
    v_res_1547_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(
            v_00_u03b1_1532_,
            v_k_1533_,
            v_allowLevelAssignments_boxed_1546_,
            v___y_1535_,
            v___y_1536_,
            v___y_1537_,
            v___y_1538_,
            v___y_1539_,
            v___y_1540_,
            v___y_1541_,
            v___y_1542_,
            v___y_1543_,
            v___y_1544_,
        );
    leanh::lean_dec(v___y_1544_);
    leanh::lean_dec_ref(v___y_1543_);
    leanh::lean_dec(v___y_1542_);
    leanh::lean_dec_ref(v___y_1541_);
    leanh::lean_dec(v___y_1540_);
    leanh::lean_dec_ref(v___y_1539_);
    leanh::lean_dec(v___y_1538_);
    leanh::lean_dec_ref(v___y_1537_);
    leanh::lean_dec(v___y_1536_);
    leanh::lean_dec(v___y_1535_);
    return v_res_1547_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(
    mut v_x_1548_: *mut leanh::LeanObject,
    mut v_x_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
    mut v_x_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1552_ = leanh::lean_ctor_get(v_x_1548_, 0);
                v_vs_1553_ = leanh::lean_ctor_get(v_x_1548_, 1);
                v_isSharedCheck_1577_ = (!leanh::lean_is_exclusive(v_x_1548_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1555_ = v_x_1548_;
                    v_isShared_1556_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1553_);
                    leanh::lean_inc(v_ks_1552_);
                    leanh::lean_dec(v_x_1548_);
                    v___x_1555_ = leanh::lean_box(0);
                    v_isShared_1556_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1557_ = lean_array_get_size(v_ks_1552_);
                v___x_1558_ = lean_nat_dec_lt(v_x_1549_, v___x_1557_);
                if v___x_1558_ == 0 {
                    leanh::lean_dec(v_x_1549_);
                    v___x_1559_ = lean_array_push(v_ks_1552_, v_x_1550_);
                    v___x_1560_ = lean_array_push(v_vs_1553_, v_x_1551_);
                    if v_isShared_1556_ == 0 {
                        leanh::lean_ctor_set(v___x_1555_, 1, v___x_1560_);
                        leanh::lean_ctor_set(v___x_1555_, 0, v___x_1559_);
                        v___x_1562_ = v___x_1555_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1563_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1559_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1560_);
                        v___x_1562_ = v_reuseFailAlloc_1563_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1564_ = lean_array_fget_borrowed(v_ks_1552_, v_x_1549_);
                    v___x_1565_ = l_Lean_instBEqMVarId_beq(v_x_1550_, v_k_x27_1564_);
                    if v___x_1565_ == 0 {
                        if v_isShared_1556_ == 0 {
                            v___x_1567_ = v___x_1555_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1571_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_ks_1552_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_vs_1553_);
                            v___x_1567_ = v_reuseFailAlloc_1571_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1572_ = lean_array_fset(v_ks_1552_, v_x_1549_, v_x_1550_);
                        v___x_1573_ = lean_array_fset(v_vs_1553_, v_x_1549_, v_x_1551_);
                        leanh::lean_dec(v_x_1549_);
                        if v_isShared_1556_ == 0 {
                            leanh::lean_ctor_set(v___x_1555_, 1, v___x_1573_);
                            leanh::lean_ctor_set(v___x_1555_, 0, v___x_1572_);
                            v___x_1575_ = v___x_1555_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1576_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1572_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
                            v___x_1575_ = v_reuseFailAlloc_1576_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1562_;
            }
            3 => {
                v___x_1568_ = leanh::lean_unsigned_to_nat(1);
                v___x_1569_ = lean_nat_add(v_x_1549_, v___x_1568_);
                leanh::lean_dec(v_x_1549_);
                v_x_1548_ = v___x_1567_;
                v_x_1549_ = v___x_1569_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(
    mut v_n_1578_: *mut leanh::LeanObject,
    mut v_k_1579_: *mut leanh::LeanObject,
    mut v_v_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = leanh::lean_unsigned_to_nat(0);
    v___x_1582_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_n_1578_, v___x_1581_, v_k_1579_, v_v_1580_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: usize = 0;
    v___x_1583_ = 5usize;
    v___x_1584_ = 1usize;
    v___x_1585_ = lean_usize_shift_left(v___x_1584_, v___x_1583_);
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_1586_: usize = 0;
    let mut v___x_1587_: usize = 0;
    let mut v___x_1588_: usize = 0;
    v___x_1586_ = 1usize;
    v___x_1587_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0);
    v___x_1588_ = lean_usize_sub(v___x_1587_, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(
    mut v_x_1590_: *mut leanh::LeanObject,
    mut v_x_1591_: usize,
    mut v_x_1592_: usize,
    mut v_x_1593_: *mut leanh::LeanObject,
    mut v_x_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: usize = 0;
    let mut v___x_1597_: usize = 0;
    let mut v___x_1598_: usize = 0;
    let mut v___x_1599_: usize = 0;
    let mut v_j_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v_v_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_node_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_unused_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1650_: u8 = 0;
    let mut v_ks_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: usize = 0;
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v_reuseFailAlloc_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1590_) == 0 {
                    v_es_1595_ = leanh::lean_ctor_get(v_x_1590_, 0);
                    v___x_1596_ = 5usize;
                    v___x_1597_ = 1usize;
                    v___x_1598_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
                    v___x_1599_ = lean_usize_land(v_x_1591_, v___x_1598_);
                    v_j_1600_ = lean_usize_to_nat(v___x_1599_);
                    v___x_1601_ = lean_array_get_size(v_es_1595_);
                    v___x_1602_ = lean_nat_dec_lt(v_j_1600_, v___x_1601_);
                    if v___x_1602_ == 0 {
                        leanh::lean_dec(v_j_1600_);
                        leanh::lean_dec(v_x_1594_);
                        leanh::lean_dec(v_x_1593_);
                        return v_x_1590_;
                    } else {
                        leanh::lean_inc_ref(v_es_1595_);
                        v_isSharedCheck_1639_ = (!leanh::lean_is_exclusive(v_x_1590_)) as u8;
                        if v_isSharedCheck_1639_ == 0 {
                            v_unused_1640_ = leanh::lean_ctor_get(v_x_1590_, 0);
                            leanh::lean_dec(v_unused_1640_);
                            v___x_1604_ = v_x_1590_;
                            v_isShared_1605_ = v_isSharedCheck_1639_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1590_);
                            v___x_1604_ = leanh::lean_box(0);
                            v_isShared_1605_ = v_isSharedCheck_1639_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1641_ = leanh::lean_ctor_get(v_x_1590_, 0);
                    v_vs_1642_ = leanh::lean_ctor_get(v_x_1590_, 1);
                    v_isSharedCheck_1662_ = (!leanh::lean_is_exclusive(v_x_1590_)) as u8;
                    if v_isSharedCheck_1662_ == 0 {
                        v___x_1644_ = v_x_1590_;
                        v_isShared_1645_ = v_isSharedCheck_1662_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1642_);
                        leanh::lean_inc(v_ks_1641_);
                        leanh::lean_dec(v_x_1590_);
                        v___x_1644_ = leanh::lean_box(0);
                        v_isShared_1645_ = v_isSharedCheck_1662_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1606_ = lean_array_fget(v_es_1595_, v_j_1600_);
                v___x_1607_ = leanh::lean_box(0);
                v_xs_x27_1608_ = lean_array_fset(v_es_1595_, v_j_1600_, v___x_1607_);
                match leanh::lean_obj_tag(v_v_1606_) {
                    0 => {
                        v_key_1615_ = leanh::lean_ctor_get(v_v_1606_, 0);
                        v_val_1616_ = leanh::lean_ctor_get(v_v_1606_, 1);
                        v_isSharedCheck_1626_ = (!leanh::lean_is_exclusive(v_v_1606_)) as u8;
                        if v_isSharedCheck_1626_ == 0 {
                            v___x_1618_ = v_v_1606_;
                            v_isShared_1619_ = v_isSharedCheck_1626_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1616_);
                            leanh::lean_inc(v_key_1615_);
                            leanh::lean_dec(v_v_1606_);
                            v___x_1618_ = leanh::lean_box(0);
                            v_isShared_1619_ = v_isSharedCheck_1626_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1627_ = leanh::lean_ctor_get(v_v_1606_, 0);
                        v_isSharedCheck_1637_ = (!leanh::lean_is_exclusive(v_v_1606_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1629_ = v_v_1606_;
                            v_isShared_1630_ = v_isSharedCheck_1637_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1627_);
                            leanh::lean_dec(v_v_1606_);
                            v___x_1629_ = leanh::lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1637_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1638_, 0, v_x_1593_);
                        leanh::lean_ctor_set(v___x_1638_, 1, v_x_1594_);
                        v___y_1610_ = v___x_1638_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1611_ = lean_array_fset(v_xs_x27_1608_, v_j_1600_, v___y_1610_);
                leanh::lean_dec(v_j_1600_);
                if v_isShared_1605_ == 0 {
                    leanh::lean_ctor_set(v___x_1604_, 0, v___x_1611_);
                    v___x_1613_ = v___x_1604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
                    v___x_1613_ = v_reuseFailAlloc_1614_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1613_;
            }
            4 => {
                v___x_1620_ = l_Lean_instBEqMVarId_beq(v_x_1593_, v_key_1615_);
                if v___x_1620_ == 0 {
                    leanh::lean_del_object(v___x_1618_);
                    v___x_1621_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1615_,
                        v_val_1616_,
                        v_x_1593_,
                        v_x_1594_,
                    );
                    v___x_1622_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1622_, 0, v___x_1621_);
                    v___y_1610_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1616_);
                    leanh::lean_dec(v_key_1615_);
                    if v_isShared_1619_ == 0 {
                        leanh::lean_ctor_set(v___x_1618_, 1, v_x_1594_);
                        leanh::lean_ctor_set(v___x_1618_, 0, v_x_1593_);
                        v___x_1624_ = v___x_1618_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1625_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_x_1593_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_x_1594_);
                        v___x_1624_ = v_reuseFailAlloc_1625_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1610_ = v___x_1624_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1631_ = lean_usize_shift_right(v_x_1591_, v___x_1596_);
                v___x_1632_ = lean_usize_add(v_x_1592_, v___x_1597_);
                v___x_1633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_node_1627_, v___x_1631_, v___x_1632_, v_x_1593_, v_x_1594_);
                if v_isShared_1630_ == 0 {
                    leanh::lean_ctor_set(v___x_1629_, 0, v___x_1633_);
                    v___x_1635_ = v___x_1629_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1636_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
                    v___x_1635_ = v_reuseFailAlloc_1636_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1610_ = v___x_1635_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1645_ == 0 {
                    v___x_1647_ = v___x_1644_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1661_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_ks_1641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_vs_1642_);
                    v___x_1647_ = v_reuseFailAlloc_1661_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1648_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v___x_1647_, v_x_1593_, v_x_1594_);
                v___x_1656_ = 7usize;
                v___x_1657_ = lean_usize_dec_le(v___x_1656_, v_x_1592_);
                if v___x_1657_ == 0 {
                    v___x_1658_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1648_);
                    v___x_1659_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1660_ = lean_nat_dec_lt(v___x_1658_, v___x_1659_);
                    leanh::lean_dec(v___x_1658_);
                    v___y_1650_ = v___x_1660_;
                    state = 10;
                    continue;
                } else {
                    v___y_1650_ = v___x_1657_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1650_ == 0 {
                    v_ks_1651_ = leanh::lean_ctor_get(v_newNode_1648_, 0);
                    leanh::lean_inc_ref(v_ks_1651_);
                    v_vs_1652_ = leanh::lean_ctor_get(v_newNode_1648_, 1);
                    leanh::lean_inc_ref(v_vs_1652_);
                    leanh::lean_dec_ref(v_newNode_1648_);
                    v___x_1653_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2);
                    v___x_1655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_x_1592_, v_ks_1651_, v_vs_1652_, v___x_1653_, v___x_1654_);
                    leanh::lean_dec_ref(v_vs_1652_);
                    leanh::lean_dec_ref(v_ks_1651_);
                    return v___x_1655_;
                } else {
                    return v_newNode_1648_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(
    mut v_depth_1663_: usize,
    mut v_keys_1664_: *mut leanh::LeanObject,
    mut v_vals_1665_: *mut leanh::LeanObject,
    mut v_i_1666_: *mut leanh::LeanObject,
    mut v_entries_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut v_k_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u64 = 0;
    let mut v_h_1673_: usize = 0;
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: usize = 0;
    let mut v___x_1677_: usize = 0;
    let mut v___x_1678_: usize = 0;
    let mut v_h_1679_: usize = 0;
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = lean_array_get_size(v_keys_1664_);
                v___x_1669_ = lean_nat_dec_lt(v_i_1666_, v___x_1668_);
                if v___x_1669_ == 0 {
                    leanh::lean_dec(v_i_1666_);
                    return v_entries_1667_;
                } else {
                    v_k_1670_ = lean_array_fget_borrowed(v_keys_1664_, v_i_1666_);
                    v_v_1671_ = lean_array_fget_borrowed(v_vals_1665_, v_i_1666_);
                    v___x_1672_ = l_Lean_instHashableMVarId_hash(v_k_1670_);
                    v_h_1673_ = lean_uint64_to_usize(v___x_1672_);
                    v___x_1674_ = 5usize;
                    v___x_1675_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1676_ = 1usize;
                    v___x_1677_ = lean_usize_sub(v_depth_1663_, v___x_1676_);
                    v___x_1678_ = lean_usize_mul(v___x_1674_, v___x_1677_);
                    v_h_1679_ = lean_usize_shift_right(v_h_1673_, v___x_1678_);
                    v___x_1680_ = lean_nat_add(v_i_1666_, v___x_1675_);
                    leanh::lean_dec(v_i_1666_);
                    leanh::lean_inc(v_v_1671_);
                    leanh::lean_inc(v_k_1670_);
                    v___x_1681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_entries_1667_, v_h_1679_, v_depth_1663_, v_k_1670_, v_v_1671_);
                    v_i_1666_ = v___x_1680_;
                    v_entries_1667_ = v___x_1681_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg___boxed(
    mut v_depth_1683_: *mut leanh::LeanObject,
    mut v_keys_1684_: *mut leanh::LeanObject,
    mut v_vals_1685_: *mut leanh::LeanObject,
    mut v_i_1686_: *mut leanh::LeanObject,
    mut v_entries_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1688_: usize = 0;
    let mut v_res_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1688_ = leanh::lean_unbox_usize(v_depth_1683_);
    leanh::lean_dec(v_depth_1683_);
    v_res_1689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_boxed_1688_, v_keys_1684_, v_vals_1685_, v_i_1686_, v_entries_1687_);
    leanh::lean_dec_ref(v_vals_1685_);
    leanh::lean_dec_ref(v_keys_1684_);
    return v_res_1689_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_x_1690_: *mut leanh::LeanObject,
    mut v_x_1691_: *mut leanh::LeanObject,
    mut v_x_1692_: *mut leanh::LeanObject,
    mut v_x_1693_: *mut leanh::LeanObject,
    mut v_x_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_215239__boxed_1695_: usize = 0;
    let mut v_x_215240__boxed_1696_: usize = 0;
    let mut v_res_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_215239__boxed_1695_ = leanh::lean_unbox_usize(v_x_1691_);
    leanh::lean_dec(v_x_1691_);
    v_x_215240__boxed_1696_ = leanh::lean_unbox_usize(v_x_1692_);
    leanh::lean_dec(v_x_1692_);
    v_res_1697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1690_, v_x_215239__boxed_1695_, v_x_215240__boxed_1696_, v_x_1693_, v_x_1694_);
    return v_res_1697_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(
    mut v_x_1698_: *mut leanh::LeanObject,
    mut v_x_1699_: *mut leanh::LeanObject,
    mut v_x_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: usize = 0;
    let mut v___x_1703_: usize = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_instHashableMVarId_hash(v_x_1699_);
    v___x_1702_ = lean_uint64_to_usize(v___x_1701_);
    v___x_1703_ = 1usize;
    v___x_1704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1698_, v___x_1702_, v___x_1703_, v_x_1699_, v_x_1700_);
    return v___x_1704_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(
    mut v_mvarId_1705_: *mut leanh::LeanObject,
    mut v_val_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v_depth_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1709_ = lean_st_ref_take(v___y_1707_);
                v_mctx_1710_ = leanh::lean_ctor_get(v___x_1709_, 0);
                v_cache_1711_ = leanh::lean_ctor_get(v___x_1709_, 1);
                v_zetaDeltaFVarIds_1712_ = leanh::lean_ctor_get(v___x_1709_, 2);
                v_postponed_1713_ = leanh::lean_ctor_get(v___x_1709_, 3);
                v_diag_1714_ = leanh::lean_ctor_get(v___x_1709_, 4);
                v_isSharedCheck_1742_ = (!leanh::lean_is_exclusive(v___x_1709_)) as u8;
                if v_isSharedCheck_1742_ == 0 {
                    v___x_1716_ = v___x_1709_;
                    v_isShared_1717_ = v_isSharedCheck_1742_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1714_);
                    leanh::lean_inc(v_postponed_1713_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1712_);
                    leanh::lean_inc(v_cache_1711_);
                    leanh::lean_inc(v_mctx_1710_);
                    leanh::lean_dec(v___x_1709_);
                    v___x_1716_ = leanh::lean_box(0);
                    v_isShared_1717_ = v_isSharedCheck_1742_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1718_ = leanh::lean_ctor_get(v_mctx_1710_, 0);
                v_levelAssignDepth_1719_ = leanh::lean_ctor_get(v_mctx_1710_, 1);
                v_lmvarCounter_1720_ = leanh::lean_ctor_get(v_mctx_1710_, 2);
                v_mvarCounter_1721_ = leanh::lean_ctor_get(v_mctx_1710_, 3);
                v_lDecls_1722_ = leanh::lean_ctor_get(v_mctx_1710_, 4);
                v_decls_1723_ = leanh::lean_ctor_get(v_mctx_1710_, 5);
                v_userNames_1724_ = leanh::lean_ctor_get(v_mctx_1710_, 6);
                v_lAssignment_1725_ = leanh::lean_ctor_get(v_mctx_1710_, 7);
                v_eAssignment_1726_ = leanh::lean_ctor_get(v_mctx_1710_, 8);
                v_dAssignment_1727_ = leanh::lean_ctor_get(v_mctx_1710_, 9);
                v_isSharedCheck_1741_ = (!leanh::lean_is_exclusive(v_mctx_1710_)) as u8;
                if v_isSharedCheck_1741_ == 0 {
                    v___x_1729_ = v_mctx_1710_;
                    v_isShared_1730_ = v_isSharedCheck_1741_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1727_);
                    leanh::lean_inc(v_eAssignment_1726_);
                    leanh::lean_inc(v_lAssignment_1725_);
                    leanh::lean_inc(v_userNames_1724_);
                    leanh::lean_inc(v_decls_1723_);
                    leanh::lean_inc(v_lDecls_1722_);
                    leanh::lean_inc(v_mvarCounter_1721_);
                    leanh::lean_inc(v_lmvarCounter_1720_);
                    leanh::lean_inc(v_levelAssignDepth_1719_);
                    leanh::lean_inc(v_depth_1718_);
                    leanh::lean_dec(v_mctx_1710_);
                    v___x_1729_ = leanh::lean_box(0);
                    v_isShared_1730_ = v_isSharedCheck_1741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1731_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_1726_, v_mvarId_1705_, v_val_1706_);
                if v_isShared_1730_ == 0 {
                    leanh::lean_ctor_set(v___x_1729_, 8, v___x_1731_);
                    v___x_1733_ = v___x_1729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_depth_1718_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1740_,
                        1,
                        v_levelAssignDepth_1719_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_lmvarCounter_1720_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_mvarCounter_1721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_lDecls_1722_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_decls_1723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_userNames_1724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_lAssignment_1725_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 8, v___x_1731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 9, v_dAssignment_1727_);
                    v___x_1733_ = v_reuseFailAlloc_1740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1717_ == 0 {
                    leanh::lean_ctor_set(v___x_1716_, 0, v___x_1733_);
                    v___x_1735_ = v___x_1716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_cache_1711_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1739_,
                        2,
                        v_zetaDeltaFVarIds_1712_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_postponed_1713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_diag_1714_);
                    v___x_1735_ = v_reuseFailAlloc_1739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1736_ = lean_st_ref_set(v___y_1707_, v___x_1735_);
                v___x_1737_ = leanh::lean_box(0);
                v___x_1738_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1738_, 0, v___x_1737_);
                return v___x_1738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(
    mut v_mvarId_1743_: *mut leanh::LeanObject,
    mut v_val_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(
            v_mvarId_1743_,
            v_val_1744_,
            v___y_1745_,
        );
    leanh::lean_dec(v___y_1745_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(
    mut v___x_1748_: u8,
    mut v_p_1749_: *mut leanh::LeanObject,
    mut v_e_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
    mut v___y_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
    mut v___y_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_unused_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1762_ = l_Lean_Expr_isMVar(v_p_1749_);
                if v___x_1762_ == 0 {
                    v___x_1763_ = l_Lean_Meta_isExprDefEq(
                        v_p_1749_,
                        v_e_1750_,
                        v___y_1757_,
                        v___y_1758_,
                        v___y_1759_,
                        v___y_1760_,
                    );
                    return v___x_1763_;
                } else {
                    v___x_1764_ = l_Lean_Expr_mvarId_x21(v_p_1749_);
                    leanh::lean_dec_ref(v_p_1749_);
                    v___x_1765_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_1764_, v_e_1750_, v___y_1758_);
                    v_isSharedCheck_1773_ = (!leanh::lean_is_exclusive(v___x_1765_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v_unused_1774_ = leanh::lean_ctor_get(v___x_1765_, 0);
                        leanh::lean_dec(v_unused_1774_);
                        v___x_1767_ = v___x_1765_;
                        v_isShared_1768_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1765_);
                        v___x_1767_ = leanh::lean_box(0);
                        v_isShared_1768_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1769_ = leanh::lean_box((v___x_1748_) as usize);
                if v_isShared_1768_ == 0 {
                    leanh::lean_ctor_set(v___x_1767_, 0, v___x_1769_);
                    v___x_1771_ = v___x_1767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
                    v___x_1771_ = v_reuseFailAlloc_1772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(
    mut v___x_1775_: *mut leanh::LeanObject,
    mut v_p_1776_: *mut leanh::LeanObject,
    mut v_e_1777_: *mut leanh::LeanObject,
    mut v___y_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
    mut v___y_1787_: *mut leanh::LeanObject,
    mut v___y_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_215458__boxed_1789_: u8 = 0;
    let mut v_res_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_215458__boxed_1789_ = (leanh::lean_unbox(v___x_1775_) as u8);
    v_res_1790_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(
        v___x_215458__boxed_1789_,
        v_p_1776_,
        v_e_1777_,
        v___y_1778_,
        v___y_1779_,
        v___y_1780_,
        v___y_1781_,
        v___y_1782_,
        v___y_1783_,
        v___y_1784_,
        v___y_1785_,
        v___y_1786_,
        v___y_1787_,
    );
    leanh::lean_dec(v___y_1787_);
    leanh::lean_dec_ref(v___y_1786_);
    leanh::lean_dec(v___y_1785_);
    leanh::lean_dec_ref(v___y_1784_);
    leanh::lean_dec(v___y_1783_);
    leanh::lean_dec_ref(v___y_1782_);
    leanh::lean_dec(v___y_1781_);
    leanh::lean_dec_ref(v___y_1780_);
    leanh::lean_dec(v___y_1779_);
    leanh::lean_dec(v___y_1778_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(
    mut v_msgData_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1797_ = lean_st_ref_get(v___y_1795_);
    v_env_1798_ = leanh::lean_ctor_get(v___x_1797_, 0);
    leanh::lean_inc_ref(v_env_1798_);
    leanh::lean_dec(v___x_1797_);
    v___x_1799_ = lean_st_ref_get(v___y_1793_);
    v_mctx_1800_ = leanh::lean_ctor_get(v___x_1799_, 0);
    leanh::lean_inc_ref(v_mctx_1800_);
    leanh::lean_dec(v___x_1799_);
    v_lctx_1801_ = leanh::lean_ctor_get(v___y_1792_, 2);
    v_options_1802_ = leanh::lean_ctor_get(v___y_1794_, 2);
    leanh::lean_inc_ref(v_options_1802_);
    leanh::lean_inc_ref(v_lctx_1801_);
    v___x_1803_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1803_, 0, v_env_1798_);
    leanh::lean_ctor_set(v___x_1803_, 1, v_mctx_1800_);
    leanh::lean_ctor_set(v___x_1803_, 2, v_lctx_1801_);
    leanh::lean_ctor_set(v___x_1803_, 3, v_options_1802_);
    v___x_1804_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
    leanh::lean_ctor_set(v___x_1804_, 1, v_msgData_1791_);
    v___x_1805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(
    mut v_msgData_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
    leanh::lean_dec(v___y_1810_);
    leanh::lean_dec_ref(v___y_1809_);
    leanh::lean_dec(v___y_1808_);
    leanh::lean_dec_ref(v___y_1807_);
    return v_res_1812_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0()
-> f64 {
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: f64 = 0.0;
    v___x_1813_ = leanh::lean_unsigned_to_nat(0);
    v___x_1814_ = lean_float_of_nat(v___x_1813_);
    return v___x_1814_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(
    mut v_cls_1818_: *mut leanh::LeanObject,
    mut v_msg_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
    mut v___y_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v_tid_1844_: u64 = 0;
    let mut v_traces_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: f64 = 0.0;
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1825_ = leanh::lean_ctor_get(v___y_1822_, 5);
                v___x_1826_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
                v_a_1827_ = leanh::lean_ctor_get(v___x_1826_, 0);
                v_isSharedCheck_1871_ = (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                if v_isSharedCheck_1871_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    v_isShared_1830_ = v_isSharedCheck_1871_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1827_);
                    leanh::lean_dec(v___x_1826_);
                    v___x_1829_ = leanh::lean_box(0);
                    v_isShared_1830_ = v_isSharedCheck_1871_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1831_ = lean_st_ref_take(v___y_1823_);
                v_traceState_1832_ = leanh::lean_ctor_get(v___x_1831_, 4);
                v_env_1833_ = leanh::lean_ctor_get(v___x_1831_, 0);
                v_nextMacroScope_1834_ = leanh::lean_ctor_get(v___x_1831_, 1);
                v_ngen_1835_ = leanh::lean_ctor_get(v___x_1831_, 2);
                v_auxDeclNGen_1836_ = leanh::lean_ctor_get(v___x_1831_, 3);
                v_cache_1837_ = leanh::lean_ctor_get(v___x_1831_, 5);
                v_messages_1838_ = leanh::lean_ctor_get(v___x_1831_, 6);
                v_infoState_1839_ = leanh::lean_ctor_get(v___x_1831_, 7);
                v_snapshotTasks_1840_ = leanh::lean_ctor_get(v___x_1831_, 8);
                v_isSharedCheck_1870_ = (!leanh::lean_is_exclusive(v___x_1831_)) as u8;
                if v_isSharedCheck_1870_ == 0 {
                    v___x_1842_ = v___x_1831_;
                    v_isShared_1843_ = v_isSharedCheck_1870_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1840_);
                    leanh::lean_inc(v_infoState_1839_);
                    leanh::lean_inc(v_messages_1838_);
                    leanh::lean_inc(v_cache_1837_);
                    leanh::lean_inc(v_traceState_1832_);
                    leanh::lean_inc(v_auxDeclNGen_1836_);
                    leanh::lean_inc(v_ngen_1835_);
                    leanh::lean_inc(v_nextMacroScope_1834_);
                    leanh::lean_inc(v_env_1833_);
                    leanh::lean_dec(v___x_1831_);
                    v___x_1842_ = leanh::lean_box(0);
                    v_isShared_1843_ = v_isSharedCheck_1870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1844_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1832_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1845_ = leanh::lean_ctor_get(v_traceState_1832_, 0);
                v_isSharedCheck_1869_ =
                    (!leanh::lean_is_exclusive(v_traceState_1832_)) as u8;
                if v_isSharedCheck_1869_ == 0 {
                    v___x_1847_ = v_traceState_1832_;
                    v_isShared_1848_ = v_isSharedCheck_1869_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1845_);
                    leanh::lean_dec(v_traceState_1832_);
                    v___x_1847_ = leanh::lean_box(0);
                    v_isShared_1848_ = v_isSharedCheck_1869_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1849_ = leanh::lean_box(0);
                v___x_1850_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
                v___x_1851_ = 0;
                v___x_1852_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1;
                v___x_1853_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1853_, 0, v_cls_1818_);
                leanh::lean_ctor_set(v___x_1853_, 1, v___x_1849_);
                leanh::lean_ctor_set(v___x_1853_, 2, v___x_1852_);
                leanh::lean_ctor_set_float(
                    v___x_1853_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1850_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1853_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1850_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1853_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1851_,
                );
                v___x_1854_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
                v___x_1855_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1855_, 0, v___x_1853_);
                leanh::lean_ctor_set(v___x_1855_, 1, v_a_1827_);
                leanh::lean_ctor_set(v___x_1855_, 2, v___x_1854_);
                leanh::lean_inc(v_ref_1825_);
                v___x_1856_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1856_, 0, v_ref_1825_);
                leanh::lean_ctor_set(v___x_1856_, 1, v___x_1855_);
                v___x_1857_ = l_Lean_PersistentArray_push___redArg(v_traces_1845_, v___x_1856_);
                if v_isShared_1848_ == 0 {
                    leanh::lean_ctor_set(v___x_1847_, 0, v___x_1857_);
                    v___x_1859_ = v___x_1847_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1857_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1868_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1844_,
                    );
                    v___x_1859_ = v_reuseFailAlloc_1868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1843_ == 0 {
                    leanh::lean_ctor_set(v___x_1842_, 4, v___x_1859_);
                    v___x_1861_ = v___x_1842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_env_1833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 4, v___x_1859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 5, v_cache_1837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_messages_1838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_infoState_1839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_snapshotTasks_1840_);
                    v___x_1861_ = v_reuseFailAlloc_1867_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1862_ = lean_st_ref_set(v___y_1823_, v___x_1861_);
                v___x_1863_ = leanh::lean_box(0);
                if v_isShared_1830_ == 0 {
                    leanh::lean_ctor_set(v___x_1829_, 0, v___x_1863_);
                    v___x_1865_ = v___x_1829_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
                    v___x_1865_ = v_reuseFailAlloc_1866_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(
    mut v_cls_1872_: *mut leanh::LeanObject,
    mut v_msg_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1879_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(
        v_cls_1872_,
        v_msg_1873_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
        v___y_1877_,
    );
    leanh::lean_dec(v___y_1877_);
    leanh::lean_dec_ref(v___y_1876_);
    leanh::lean_dec(v___y_1875_);
    leanh::lean_dec_ref(v___y_1874_);
    return v_res_1879_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(
    mut v_keys_1880_: *mut leanh::LeanObject,
    mut v_i_1881_: *mut leanh::LeanObject,
    mut v_k_1882_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: u8 = 0;
    let mut v_k_x27_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = lean_array_get_size(v_keys_1880_);
                v___x_1884_ = lean_nat_dec_lt(v_i_1881_, v___x_1883_);
                if v___x_1884_ == 0 {
                    leanh::lean_dec(v_i_1881_);
                    return v___x_1884_;
                } else {
                    v_k_x27_1885_ = lean_array_fget_borrowed(v_keys_1880_, v_i_1881_);
                    v___x_1886_ = l_Lean_instBEqMVarId_beq(v_k_1882_, v_k_x27_1885_);
                    if v___x_1886_ == 0 {
                        v___x_1887_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1888_ = lean_nat_add(v_i_1881_, v___x_1887_);
                        leanh::lean_dec(v_i_1881_);
                        v_i_1881_ = v___x_1888_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1881_);
                        return v___x_1886_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(
    mut v_keys_1890_: *mut leanh::LeanObject,
    mut v_i_1891_: *mut leanh::LeanObject,
    mut v_k_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1893_: u8 = 0;
    let mut v_r_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1890_, v_i_1891_, v_k_1892_);
    leanh::lean_dec(v_k_1892_);
    leanh::lean_dec_ref(v_keys_1890_);
    v_r_1894_ = leanh::lean_box((v_res_1893_) as usize);
    return v_r_1894_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(
    mut v_x_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: usize,
    mut v_x_1897_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v_j_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: u8 = 0;
    let mut v_node_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: usize = 0;
    let mut v___x_1910_: u8 = 0;
    let mut v_ks_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1895_) == 0 {
                    v_es_1898_ = leanh::lean_ctor_get(v_x_1895_, 0);
                    v___x_1899_ = leanh::lean_box(2);
                    v___x_1900_ = 5usize;
                    v___x_1901_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
                    v___x_1902_ = lean_usize_land(v_x_1896_, v___x_1901_);
                    v_j_1903_ = lean_usize_to_nat(v___x_1902_);
                    v___x_1904_ = lean_array_get_borrowed(v___x_1899_, v_es_1898_, v_j_1903_);
                    leanh::lean_dec(v_j_1903_);
                    match leanh::lean_obj_tag(v___x_1904_) {
                        0 => {
                            v_key_1905_ = leanh::lean_ctor_get(v___x_1904_, 0);
                            v___x_1906_ = l_Lean_instBEqMVarId_beq(v_x_1897_, v_key_1905_);
                            return v___x_1906_;
                        }
                        1 => {
                            v_node_1907_ = leanh::lean_ctor_get(v___x_1904_, 0);
                            v___x_1908_ = lean_usize_shift_right(v_x_1896_, v___x_1900_);
                            v_x_1895_ = v_node_1907_;
                            v_x_1896_ = v___x_1908_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1910_ = 0;
                            return v___x_1910_;
                        }
                    }
                } else {
                    v_ks_1911_ = leanh::lean_ctor_get(v_x_1895_, 0);
                    v___x_1912_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1913_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_1911_, v___x_1912_, v_x_1897_);
                    return v___x_1913_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_x_1914_: *mut leanh::LeanObject,
    mut v_x_1915_: *mut leanh::LeanObject,
    mut v_x_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_215667__boxed_1917_: usize = 0;
    let mut v_res_1918_: u8 = 0;
    let mut v_r_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_215667__boxed_1917_ = leanh::lean_unbox_usize(v_x_1915_);
    leanh::lean_dec(v_x_1915_);
    v_res_1918_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1914_, v_x_215667__boxed_1917_, v_x_1916_);
    leanh::lean_dec(v_x_1916_);
    leanh::lean_dec_ref(v_x_1914_);
    v_r_1919_ = leanh::lean_box((v_res_1918_) as usize);
    return v_r_1919_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(
    mut v_x_1920_: *mut leanh::LeanObject,
    mut v_x_1921_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1922_: u64 = 0;
    let mut v___x_1923_: usize = 0;
    let mut v___x_1924_: u8 = 0;
    v___x_1922_ = l_Lean_instHashableMVarId_hash(v_x_1921_);
    v___x_1923_ = lean_uint64_to_usize(v___x_1922_);
    v___x_1924_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1920_, v___x_1923_, v_x_1921_);
    return v___x_1924_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(
    mut v_x_1925_: *mut leanh::LeanObject,
    mut v_x_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1927_: u8 = 0;
    let mut v_r_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1925_, v_x_1926_);
    leanh::lean_dec(v_x_1926_);
    leanh::lean_dec_ref(v_x_1925_);
    v_r_1928_ = leanh::lean_box((v_res_1927_) as usize);
    return v_r_1928_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(
    mut v_mvarId_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = lean_st_ref_get(v___y_1930_);
    v_mctx_1933_ = leanh::lean_ctor_get(v___x_1932_, 0);
    leanh::lean_inc_ref(v_mctx_1933_);
    leanh::lean_dec(v___x_1932_);
    v_eAssignment_1934_ = leanh::lean_ctor_get(v_mctx_1933_, 8);
    leanh::lean_inc_ref(v_eAssignment_1934_);
    leanh::lean_dec_ref(v_mctx_1933_);
    v___x_1935_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_1934_, v_mvarId_1929_);
    leanh::lean_dec_ref(v_eAssignment_1934_);
    v___x_1936_ = leanh::lean_box((v___x_1935_) as usize);
    v___x_1937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(
    mut v_mvarId_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1941_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(
            v_mvarId_1938_,
            v___y_1939_,
        );
    leanh::lean_dec(v___y_1939_);
    leanh::lean_dec(v_mvarId_1938_);
    return v_res_1941_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(
    mut v_as_1942_: *mut leanh::LeanObject,
    mut v_i_1943_: usize,
    mut v_stop_1944_: usize,
    mut v_b_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v_a_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v_a_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = lean_usize_dec_eq(v_i_1943_, v_stop_1944_);
                if v___x_1962_ == 0 {
                    v___x_1963_ = lean_array_uget_borrowed(v_as_1942_, v_i_1943_);
                    v___x_1966_ = l_Lean_Expr_mvarId_x21(v___x_1963_);
                    v___x_1967_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_1966_, v___y_1953_);
                    leanh::lean_dec(v___x_1966_);
                    if leanh::lean_obj_tag(v___x_1967_) == 0 {
                        v_a_1968_ = leanh::lean_ctor_get(v___x_1967_, 0);
                        leanh::lean_inc(v_a_1968_);
                        leanh::lean_dec_ref_known(v___x_1967_, 1);
                        v___x_1969_ = (leanh::lean_unbox(v_a_1968_) as u8);
                        leanh::lean_dec(v_a_1968_);
                        if v___x_1969_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1958_ = v_b_1945_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1967_) == 0 {
                            v_a_1970_ = leanh::lean_ctor_get(v___x_1967_, 0);
                            leanh::lean_inc(v_a_1970_);
                            leanh::lean_dec_ref_known(v___x_1967_, 1);
                            v___x_1971_ = (leanh::lean_unbox(v_a_1970_) as u8);
                            leanh::lean_dec(v_a_1970_);
                            if v___x_1971_ == 0 {
                                v_a_1958_ = v_b_1945_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_1945_);
                            v_a_1972_ = leanh::lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_1979_ =
                                (!leanh::lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_1979_ == 0 {
                                v___x_1974_ = v___x_1967_;
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1972_);
                                leanh::lean_dec(v___x_1967_);
                                v___x_1974_ = leanh::lean_box(0);
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1980_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1980_, 0, v_b_1945_);
                    return v___x_1980_;
                }
            }
            1 => {
                v___x_1959_ = 1usize;
                v___x_1960_ = lean_usize_add(v_i_1943_, v___x_1959_);
                v_i_1943_ = v___x_1960_;
                v_b_1945_ = v_a_1958_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v___x_1963_);
                v___x_1965_ = lean_array_push(v_b_1945_, v___x_1963_);
                v_a_1958_ = v___x_1965_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_1975_ == 0 {
                    v___x_1977_ = v___x_1974_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
                    v___x_1977_ = v_reuseFailAlloc_1978_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(
    mut v_as_1981_: *mut leanh::LeanObject,
    mut v_i_1982_: *mut leanh::LeanObject,
    mut v_stop_1983_: *mut leanh::LeanObject,
    mut v_b_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1996_: usize = 0;
    let mut v_stop_boxed_1997_: usize = 0;
    let mut v_res_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1996_ = leanh::lean_unbox_usize(v_i_1982_);
    leanh::lean_dec(v_i_1982_);
    v_stop_boxed_1997_ = leanh::lean_unbox_usize(v_stop_1983_);
    leanh::lean_dec(v_stop_1983_);
    v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_1981_, v_i_boxed_1996_, v_stop_boxed_1997_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
    leanh::lean_dec(v___y_1994_);
    leanh::lean_dec_ref(v___y_1993_);
    leanh::lean_dec(v___y_1992_);
    leanh::lean_dec_ref(v___y_1991_);
    leanh::lean_dec(v___y_1990_);
    leanh::lean_dec_ref(v___y_1989_);
    leanh::lean_dec(v___y_1988_);
    leanh::lean_dec_ref(v___y_1987_);
    leanh::lean_dec(v___y_1986_);
    leanh::lean_dec(v___y_1985_);
    leanh::lean_dec_ref(v_as_1981_);
    return v_res_1998_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1;
    v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
    return v___x_2003_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3;
    v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
    return v___x_2006_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(
    mut v___x_2007_: *mut leanh::LeanObject,
    mut v_e_2008_: *mut leanh::LeanObject,
    mut v_as_2009_: *mut leanh::LeanObject,
    mut v_sz_2010_: usize,
    mut v_i_2011_: usize,
    mut v_b_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: usize = 0;
    let mut v___x_2027_: usize = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v_array_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v_a_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: u8 = 0;
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_a_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_a_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2119_: u8 = 0;
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut v_reuseFailAlloc_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_a_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut v_unused_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v_unused_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2029_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
                if v___x_2029_ == 0 {
                    leanh::lean_dec_ref(v_e_2008_);
                    leanh::lean_dec(v___x_2007_);
                    v___x_2030_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2030_, 0, v_b_2012_);
                    return v___x_2030_;
                } else {
                    v_snd_2031_ = leanh::lean_ctor_get(v_b_2012_, 1);
                    v_isSharedCheck_2137_ = (!leanh::lean_is_exclusive(v_b_2012_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v_unused_2138_ = leanh::lean_ctor_get(v_b_2012_, 0);
                        leanh::lean_dec(v_unused_2138_);
                        v___x_2033_ = v_b_2012_;
                        v_isShared_2034_ = v_isSharedCheck_2137_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2031_);
                        leanh::lean_dec(v_b_2012_);
                        v___x_2033_ = leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2137_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2026_ = 1usize;
                v___x_2027_ = lean_usize_add(v_i_2011_, v___x_2026_);
                v_i_2011_ = v___x_2027_;
                v_b_2012_ = v_a_2025_;
                state = 0;
                continue;
            }
            2 => {
                v_array_2035_ = leanh::lean_ctor_get(v_snd_2031_, 0);
                v_start_2036_ = leanh::lean_ctor_get(v_snd_2031_, 1);
                v_stop_2037_ = leanh::lean_ctor_get(v_snd_2031_, 2);
                v___x_2038_ = leanh::lean_box(0);
                v___x_2039_ = lean_nat_dec_lt(v_start_2036_, v_stop_2037_);
                if v___x_2039_ == 0 {
                    leanh::lean_dec_ref(v_e_2008_);
                    leanh::lean_dec(v___x_2007_);
                    if v_isShared_2034_ == 0 {
                        leanh::lean_ctor_set(v___x_2033_, 0, v___x_2038_);
                        v___x_2041_ = v___x_2033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2038_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_snd_2031_);
                        v___x_2041_ = v_reuseFailAlloc_2043_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_2037_);
                    leanh::lean_inc(v_start_2036_);
                    leanh::lean_inc_ref(v_array_2035_);
                    v_isSharedCheck_2133_ = (!leanh::lean_is_exclusive(v_snd_2031_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v_unused_2134_ = leanh::lean_ctor_get(v_snd_2031_, 2);
                        leanh::lean_dec(v_unused_2134_);
                        v_unused_2135_ = leanh::lean_ctor_get(v_snd_2031_, 1);
                        leanh::lean_dec(v_unused_2135_);
                        v_unused_2136_ = leanh::lean_ctor_get(v_snd_2031_, 0);
                        leanh::lean_dec(v_unused_2136_);
                        v___x_2045_ = v_snd_2031_;
                        v_isShared_2046_ = v_isSharedCheck_2133_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_2031_);
                        v___x_2045_ = leanh::lean_box(0);
                        v_isShared_2046_ = v_isSharedCheck_2133_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2042_, 0, v___x_2041_);
                return v___x_2042_;
            }
            4 => {
                v_a_2047_ = lean_array_uget_borrowed(v_as_2009_, v_i_2011_);
                v___x_2048_ = l_Lean_Expr_mvarId_x21(v_a_2047_);
                v___x_2049_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_2048_, v___y_2020_);
                leanh::lean_dec(v___x_2048_);
                if leanh::lean_obj_tag(v___x_2049_) == 0 {
                    v_a_2050_ = leanh::lean_ctor_get(v___x_2049_, 0);
                    v_isSharedCheck_2124_ = (!leanh::lean_is_exclusive(v___x_2049_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2052_ = v___x_2049_;
                        v_isShared_2053_ = v_isSharedCheck_2124_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2050_);
                        leanh::lean_dec(v___x_2049_);
                        v___x_2052_ = leanh::lean_box(0);
                        v_isShared_2053_ = v_isSharedCheck_2124_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2045_);
                    leanh::lean_dec(v_stop_2037_);
                    leanh::lean_dec(v_start_2036_);
                    leanh::lean_dec_ref(v_array_2035_);
                    leanh::lean_del_object(v___x_2033_);
                    leanh::lean_dec_ref(v_e_2008_);
                    leanh::lean_dec(v___x_2007_);
                    v_a_2125_ = leanh::lean_ctor_get(v___x_2049_, 0);
                    v_isSharedCheck_2132_ = (!leanh::lean_is_exclusive(v___x_2049_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v___x_2127_ = v___x_2049_;
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2125_);
                        leanh::lean_dec(v___x_2049_);
                        v___x_2127_ = leanh::lean_box(0);
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 20;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2054_ = lean_array_fget(v_array_2035_, v_start_2036_);
                v___x_2055_ = leanh::lean_unsigned_to_nat(1);
                v___x_2056_ = lean_nat_add(v_start_2036_, v___x_2055_);
                leanh::lean_dec(v_start_2036_);
                if v_isShared_2046_ == 0 {
                    leanh::lean_ctor_set(v___x_2045_, 1, v___x_2056_);
                    v___x_2058_ = v___x_2045_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_array_2035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_stop_2037_);
                    v___x_2058_ = v_reuseFailAlloc_2123_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2120_ = (leanh::lean_unbox(v___x_2054_) as u8);
                leanh::lean_dec(v___x_2054_);
                v___x_2121_ = l_Lean_BinderInfo_isInstImplicit(v___x_2120_);
                if v___x_2121_ == 0 {
                    leanh::lean_dec(v_a_2050_);
                    v___y_2070_ = v___x_2121_;
                    state = 11;
                    continue;
                } else {
                    v___x_2122_ = (leanh::lean_unbox(v_a_2050_) as u8);
                    leanh::lean_dec(v_a_2050_);
                    if v___x_2122_ == 0 {
                        v___y_2070_ = v___x_2121_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2052_);
                        leanh::lean_del_object(v___x_2033_);
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0;
                if v_isShared_2034_ == 0 {
                    leanh::lean_ctor_set(v___x_2033_, 1, v___x_2058_);
                    leanh::lean_ctor_set(v___x_2033_, 0, v___x_2060_);
                    v___x_2062_ = v___x_2033_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2058_);
                    v___x_2062_ = v_reuseFailAlloc_2066_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2053_ == 0 {
                    leanh::lean_ctor_set(v___x_2052_, 0, v___x_2062_);
                    v___x_2064_ = v___x_2052_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2064_;
            }
            10 => {
                v___x_2068_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2068_, 0, v___x_2038_);
                leanh::lean_ctor_set(v___x_2068_, 1, v___x_2058_);
                v_a_2025_ = v___x_2068_;
                state = 1;
                continue;
            }
            11 => {
                if v___y_2070_ == 0 {
                    leanh::lean_del_object(v___x_2052_);
                    leanh::lean_del_object(v___x_2033_);
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v___y_2022_);
                    leanh::lean_inc_ref(v___y_2021_);
                    leanh::lean_inc(v___y_2020_);
                    leanh::lean_inc_ref(v___y_2019_);
                    leanh::lean_inc(v_a_2047_);
                    v___x_2071_ = lean_infer_type(
                        v_a_2047_,
                        v___y_2019_,
                        v___y_2020_,
                        v___y_2021_,
                        v___y_2022_,
                    );
                    if leanh::lean_obj_tag(v___x_2071_) == 0 {
                        v_a_2072_ = leanh::lean_ctor_get(v___x_2071_, 0);
                        leanh::lean_inc(v_a_2072_);
                        leanh::lean_dec_ref_known(v___x_2071_, 1);
                        leanh::lean_inc(v_a_2047_);
                        v___x_2073_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(
                            v_a_2047_,
                            v_a_2072_,
                            v___y_2019_,
                            v___y_2020_,
                            v___y_2021_,
                            v___y_2022_,
                        );
                        if leanh::lean_obj_tag(v___x_2073_) == 0 {
                            v_a_2074_ = leanh::lean_ctor_get(v___x_2073_, 0);
                            leanh::lean_inc(v_a_2074_);
                            leanh::lean_dec_ref_known(v___x_2073_, 1);
                            v___x_2075_ = (leanh::lean_unbox(v_a_2074_) as u8);
                            leanh::lean_dec(v_a_2074_);
                            if v___x_2075_ == 0 {
                                v___x_2076_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_2017_);
                                if leanh::lean_obj_tag(v___x_2076_) == 0 {
                                    v_a_2077_ = leanh::lean_ctor_get(v___x_2076_, 0);
                                    leanh::lean_inc(v_a_2077_);
                                    leanh::lean_dec_ref_known(v___x_2076_, 1);
                                    v___x_2078_ = (leanh::lean_unbox(v_a_2077_) as u8);
                                    leanh::lean_dec(v_a_2077_);
                                    if v___x_2078_ == 0 {
                                        leanh::lean_dec_ref(v_e_2008_);
                                        leanh::lean_dec(v___x_2007_);
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_2079_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
                                        v___x_2080_ = l_Lean_MessageData_ofName(v___x_2007_);
                                        v___x_2081_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2081_, 0, v___x_2079_);
                                        leanh::lean_ctor_set(v___x_2081_, 1, v___x_2080_);
                                        v___x_2082_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
                                        v___x_2083_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2083_, 0, v___x_2081_);
                                        leanh::lean_ctor_set(v___x_2083_, 1, v___x_2082_);
                                        v___x_2084_ = l_Lean_indentExpr(v_e_2008_);
                                        v___x_2085_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2085_, 0, v___x_2083_);
                                        leanh::lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                                        v___x_2086_ = l_Lean_Meta_Sym_reportIssue(
                                            v___x_2085_,
                                            v___y_2017_,
                                            v___y_2018_,
                                            v___y_2019_,
                                            v___y_2020_,
                                            v___y_2021_,
                                            v___y_2022_,
                                        );
                                        if leanh::lean_obj_tag(v___x_2086_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_2086_, 1);
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v___x_2058_);
                                            leanh::lean_del_object(v___x_2052_);
                                            leanh::lean_del_object(v___x_2033_);
                                            v_a_2087_ = leanh::lean_ctor_get(v___x_2086_, 0);
                                            v_isSharedCheck_2094_ =
                                                (!leanh::lean_is_exclusive(v___x_2086_))
                                                    as u8;
                                            if v_isSharedCheck_2094_ == 0 {
                                                v___x_2089_ = v___x_2086_;
                                                v_isShared_2090_ = v_isSharedCheck_2094_;
                                                state = 12;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2087_);
                                                leanh::lean_dec(v___x_2086_);
                                                v___x_2089_ = leanh::lean_box(0);
                                                v_isShared_2090_ = v_isSharedCheck_2094_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2058_);
                                    leanh::lean_del_object(v___x_2052_);
                                    leanh::lean_del_object(v___x_2033_);
                                    leanh::lean_dec_ref(v_e_2008_);
                                    leanh::lean_dec(v___x_2007_);
                                    v_a_2095_ = leanh::lean_ctor_get(v___x_2076_, 0);
                                    v_isSharedCheck_2102_ =
                                        (!leanh::lean_is_exclusive(v___x_2076_)) as u8;
                                    if v_isSharedCheck_2102_ == 0 {
                                        v___x_2097_ = v___x_2076_;
                                        v_isShared_2098_ = v_isSharedCheck_2102_;
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2095_);
                                        leanh::lean_dec(v___x_2076_);
                                        v___x_2097_ = leanh::lean_box(0);
                                        v_isShared_2098_ = v_isSharedCheck_2102_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_2052_);
                                leanh::lean_del_object(v___x_2033_);
                                v___x_2103_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2103_, 0, v___x_2038_);
                                leanh::lean_ctor_set(v___x_2103_, 1, v___x_2058_);
                                v_a_2025_ = v___x_2103_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2058_);
                            leanh::lean_del_object(v___x_2052_);
                            leanh::lean_del_object(v___x_2033_);
                            leanh::lean_dec_ref(v_e_2008_);
                            leanh::lean_dec(v___x_2007_);
                            v_a_2104_ = leanh::lean_ctor_get(v___x_2073_, 0);
                            v_isSharedCheck_2111_ =
                                (!leanh::lean_is_exclusive(v___x_2073_)) as u8;
                            if v_isSharedCheck_2111_ == 0 {
                                v___x_2106_ = v___x_2073_;
                                v_isShared_2107_ = v_isSharedCheck_2111_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2104_);
                                leanh::lean_dec(v___x_2073_);
                                v___x_2106_ = leanh::lean_box(0);
                                v_isShared_2107_ = v_isSharedCheck_2111_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2058_);
                        leanh::lean_del_object(v___x_2052_);
                        leanh::lean_del_object(v___x_2033_);
                        leanh::lean_dec_ref(v_e_2008_);
                        leanh::lean_dec(v___x_2007_);
                        v_a_2112_ = leanh::lean_ctor_get(v___x_2071_, 0);
                        v_isSharedCheck_2119_ =
                            (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                        if v_isSharedCheck_2119_ == 0 {
                            v___x_2114_ = v___x_2071_;
                            v_isShared_2115_ = v_isSharedCheck_2119_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2112_);
                            leanh::lean_dec(v___x_2071_);
                            v___x_2114_ = leanh::lean_box(0);
                            v_isShared_2115_ = v_isSharedCheck_2119_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_2090_ == 0 {
                    v___x_2092_ = v___x_2089_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
                    v___x_2092_ = v_reuseFailAlloc_2093_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2092_;
            }
            14 => {
                if v_isShared_2098_ == 0 {
                    v___x_2100_ = v___x_2097_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2101_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
                    v___x_2100_ = v_reuseFailAlloc_2101_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2100_;
            }
            16 => {
                if v_isShared_2107_ == 0 {
                    v___x_2109_ = v___x_2106_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
                    v___x_2109_ = v_reuseFailAlloc_2110_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2109_;
            }
            18 => {
                if v_isShared_2115_ == 0 {
                    v___x_2117_ = v___x_2114_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
                    v___x_2117_ = v_reuseFailAlloc_2118_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2117_;
            }
            20 => {
                if v_isShared_2128_ == 0 {
                    v___x_2130_ = v___x_2127_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
                    v___x_2130_ = v_reuseFailAlloc_2131_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2139_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_e_2140_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_2141_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_2142_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_2143_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_2144_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_2145_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_2146_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_2147_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_2148_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_2149_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_2150_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_2151_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_2152_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_2153_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_2154_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_2155_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_2156_: usize = 0;
    let mut v_i_boxed_2157_: usize = 0;
    let mut v_res_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2156_ = leanh::lean_unbox_usize(v_sz_2142_);
    leanh::lean_dec(v_sz_2142_);
    v_i_boxed_2157_ = leanh::lean_unbox_usize(v_i_2143_);
    leanh::lean_dec(v_i_2143_);
    v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_2139_, v_e_2140_, v_as_2141_, v_sz_boxed_2156_, v_i_boxed_2157_, v_b_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
    leanh::lean_dec(v___y_2154_);
    leanh::lean_dec_ref(v___y_2153_);
    leanh::lean_dec(v___y_2152_);
    leanh::lean_dec_ref(v___y_2151_);
    leanh::lean_dec(v___y_2150_);
    leanh::lean_dec_ref(v___y_2149_);
    leanh::lean_dec(v___y_2148_);
    leanh::lean_dec_ref(v___y_2147_);
    leanh::lean_dec(v___y_2146_);
    leanh::lean_dec(v___y_2145_);
    leanh::lean_dec_ref(v_as_2141_);
    return v_res_2158_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2170_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4;
    v___x_2171_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6;
    v___x_2172_ = l_Lean_Name_append(v___x_2171_, v___x_2170_);
    return v___x_2172_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2174_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8;
    v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
    return v___x_2175_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10;
    v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12;
    v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14;
    v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
    return v___x_2184_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18;
    v___x_2193_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17;
    v___x_2194_ = l_Lean_mkConst(v___x_2193_, v___x_2192_);
    return v___x_2194_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21() -> u64 {
    let mut v___x_2197_: u8 = 0;
    let mut v___x_2198_: u64 = 0;
    v___x_2197_ = 1;
    v___x_2198_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2197_);
    return v___x_2198_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(
    mut v_e_2199_: *mut leanh::LeanObject,
    mut v_thm_2200_: *mut leanh::LeanObject,
    mut v___y_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
    mut v___y_2205_: *mut leanh::LeanObject,
    mut v___y_2206_: *mut leanh::LeanObject,
    mut v___y_2207_: *mut leanh::LeanObject,
    mut v___y_2208_: *mut leanh::LeanObject,
    mut v___y_2209_: *mut leanh::LeanObject,
    mut v___y_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v_arg_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v_arg_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v_arg_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v_declName_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v___y_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: u8 = 0;
    let mut v_options_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2282_: u8 = 0;
    let mut v_inheritedTraceOptions_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v___y_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2316_: u8 = 0;
    let mut v_a_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: u8 = 0;
    let mut v_a_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut v_a_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2339_: u8 = 0;
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v___y_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: u8 = 0;
    let mut v___y_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2356_: u8 = 0;
    let mut v___y_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: u8 = 0;
    let mut v___y_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2397_: usize = 0;
    let mut v___x_2398_: usize = 0;
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v_fst_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u8 = 0;
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: usize = 0;
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: usize = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v_a_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut v_val_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_a_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut v_a_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2454_: u8 = 0;
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v_a_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: u8 = 0;
    let mut v_arg_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: u8 = 0;
    let mut v_arg_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v_arg_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2494_: u8 = 0;
    let mut v_ctxApprox_2495_: u8 = 0;
    let mut v_quasiPatternApprox_2496_: u8 = 0;
    let mut v_constApprox_2497_: u8 = 0;
    let mut v_isDefEqStuckEx_2498_: u8 = 0;
    let mut v_unificationHints_2499_: u8 = 0;
    let mut v_proofIrrelevance_2500_: u8 = 0;
    let mut v_assignSyntheticOpaque_2501_: u8 = 0;
    let mut v_offsetCnstrs_2502_: u8 = 0;
    let mut v_etaStruct_2503_: u8 = 0;
    let mut v_univApprox_2504_: u8 = 0;
    let mut v_iota_2505_: u8 = 0;
    let mut v_beta_2506_: u8 = 0;
    let mut v_proj_2507_: u8 = 0;
    let mut v_zeta_2508_: u8 = 0;
    let mut v_zetaDelta_2509_: u8 = 0;
    let mut v_zetaUnused_2510_: u8 = 0;
    let mut v_zetaHave_2511_: u8 = 0;
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v_trackZetaDelta_2515_: u8 = 0;
    let mut v_zetaDeltaSet_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2522_: u8 = 0;
    let mut v_inTypeClassResolution_2523_: u8 = 0;
    let mut v_cacheInferType_2524_: u8 = 0;
    let mut v___x_2525_: u8 = 0;
    let mut v_config_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u64 = 0;
    let mut v___x_2529_: u64 = 0;
    let mut v___x_2530_: u64 = 0;
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: u64 = 0;
    let mut v___x_2534_: u64 = 0;
    let mut v_key_2535_: u64 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2544_: u8 = 0;
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v_reuseFailAlloc_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_a_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_a_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_a_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2224_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_2199_, v___y_2201_);
                if leanh::lean_obj_tag(v___x_2224_) == 0 {
                    v_a_2225_ = leanh::lean_ctor_get(v___x_2224_, 0);
                    leanh::lean_inc(v_a_2225_);
                    leanh::lean_dec_ref_known(v___x_2224_, 1);
                    v___x_2226_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_2203_);
                    if leanh::lean_obj_tag(v___x_2226_) == 0 {
                        v_a_2227_ = leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2567_ =
                            (!leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2567_ == 0 {
                            v___x_2229_ = v___x_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2567_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2227_);
                            leanh::lean_dec(v___x_2226_);
                            v___x_2229_ = leanh::lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2567_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2225_);
                        leanh::lean_dec_ref(v_thm_2200_);
                        leanh::lean_dec_ref(v_e_2199_);
                        v_a_2568_ = leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2575_ =
                            (!leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2575_ == 0 {
                            v___x_2570_ = v___x_2226_;
                            v_isShared_2571_ = v_isSharedCheck_2575_;
                            state = 46;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2568_);
                            leanh::lean_dec(v___x_2226_);
                            v___x_2570_ = leanh::lean_box(0);
                            v_isShared_2571_ = v_isSharedCheck_2575_;
                            state = 46;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_thm_2200_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v_a_2576_ = leanh::lean_ctor_get(v___x_2224_, 0);
                    v_isSharedCheck_2583_ = (!leanh::lean_is_exclusive(v___x_2224_)) as u8;
                    if v_isSharedCheck_2583_ == 0 {
                        v___x_2578_ = v___x_2224_;
                        v_isShared_2579_ = v_isSharedCheck_2583_;
                        state = 48;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2576_);
                        leanh::lean_dec(v___x_2224_);
                        v___x_2578_ = leanh::lean_box(0);
                        v_isShared_2579_ = v_isSharedCheck_2583_;
                        state = 48;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2213_ = leanh::lean_box(0);
                v___x_2214_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2214_, 0, v___x_2213_);
                return v___x_2214_;
            }
            2 => {
                v___x_2216_ = leanh::lean_box(0);
                v___x_2217_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2217_, 0, v___x_2216_);
                return v___x_2217_;
            }
            3 => {
                v___x_2219_ = leanh::lean_box(0);
                v___x_2220_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
                return v___x_2220_;
            }
            4 => {
                v___x_2222_ = leanh::lean_box(0);
                v___x_2223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2223_, 0, v___x_2222_);
                return v___x_2223_;
            }
            5 => {
                v___x_2231_ = lean_nat_dec_lt(v_a_2225_, v_a_2227_);
                leanh::lean_dec(v_a_2227_);
                leanh::lean_dec(v_a_2225_);
                if v___x_2231_ == 0 {
                    leanh::lean_dec_ref(v_thm_2200_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v___x_2232_ = leanh::lean_box(0);
                    if v_isShared_2230_ == 0 {
                        leanh::lean_ctor_set(v___x_2229_, 0, v___x_2232_);
                        v___x_2234_ = v___x_2229_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2235_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
                        v___x_2234_ = v_reuseFailAlloc_2235_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2229_);
                    leanh::lean_inc_ref(v_e_2199_);
                    v___x_2236_ = l_Lean_Expr_cleanupAnnotations(v_e_2199_);
                    v___x_2237_ = l_Lean_Expr_isApp(v___x_2236_);
                    if v___x_2237_ == 0 {
                        leanh::lean_dec_ref(v___x_2236_);
                        leanh::lean_dec_ref(v_thm_2200_);
                        leanh::lean_dec_ref(v_e_2199_);
                        state = 4;
                        continue;
                    } else {
                        v_arg_2238_ = leanh::lean_ctor_get(v___x_2236_, 1);
                        leanh::lean_inc_ref(v_arg_2238_);
                        v___x_2239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2236_);
                        v___x_2240_ = l_Lean_Expr_isApp(v___x_2239_);
                        if v___x_2240_ == 0 {
                            leanh::lean_dec_ref(v___x_2239_);
                            leanh::lean_dec_ref(v_arg_2238_);
                            leanh::lean_dec_ref(v_thm_2200_);
                            leanh::lean_dec_ref(v_e_2199_);
                            state = 4;
                            continue;
                        } else {
                            v_arg_2241_ = leanh::lean_ctor_get(v___x_2239_, 1);
                            leanh::lean_inc_ref(v_arg_2241_);
                            v___x_2242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2239_);
                            v___x_2243_ = l_Lean_Expr_isApp(v___x_2242_);
                            if v___x_2243_ == 0 {
                                leanh::lean_dec_ref(v___x_2242_);
                                leanh::lean_dec_ref(v_arg_2241_);
                                leanh::lean_dec_ref(v_arg_2238_);
                                leanh::lean_dec_ref(v_thm_2200_);
                                leanh::lean_dec_ref(v_e_2199_);
                                state = 4;
                                continue;
                            } else {
                                v_arg_2244_ = leanh::lean_ctor_get(v___x_2242_, 1);
                                leanh::lean_inc_ref(v_arg_2244_);
                                v___x_2245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2242_);
                                v___x_2246_ =
                                    l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1;
                                v___x_2247_ = l_Lean_Expr_isConstOf(v___x_2245_, v___x_2246_);
                                leanh::lean_dec_ref(v___x_2245_);
                                if v___x_2247_ == 0 {
                                    leanh::lean_dec_ref(v_arg_2244_);
                                    leanh::lean_dec_ref(v_arg_2241_);
                                    leanh::lean_dec_ref(v_arg_2238_);
                                    leanh::lean_dec_ref(v_thm_2200_);
                                    leanh::lean_dec_ref(v_e_2199_);
                                    state = 4;
                                    continue;
                                } else {
                                    v_declName_2248_ = leanh::lean_ctor_get(v_thm_2200_, 0);
                                    leanh::lean_inc_n(v_declName_2248_, 2);
                                    leanh::lean_dec_ref(v_thm_2200_);
                                    v___x_2382_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                                        v_declName_2248_,
                                        v___y_2207_,
                                        v___y_2208_,
                                        v___y_2209_,
                                        v___y_2210_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2382_) == 0 {
                                        v_a_2383_ = leanh::lean_ctor_get(v___x_2382_, 0);
                                        leanh::lean_inc_n(v_a_2383_, 2);
                                        leanh::lean_dec_ref_known(v___x_2382_, 1);
                                        leanh::lean_inc(v___y_2210_);
                                        leanh::lean_inc_ref(v___y_2209_);
                                        leanh::lean_inc(v___y_2208_);
                                        leanh::lean_inc_ref(v___y_2207_);
                                        v___x_2491_ = lean_infer_type(
                                            v_a_2383_,
                                            v___y_2207_,
                                            v___y_2208_,
                                            v___y_2209_,
                                            v___y_2210_,
                                        );
                                        if leanh::lean_obj_tag(v___x_2491_) == 0 {
                                            v_a_2492_ = leanh::lean_ctor_get(v___x_2491_, 0);
                                            leanh::lean_inc(v_a_2492_);
                                            leanh::lean_dec_ref_known(v___x_2491_, 1);
                                            v___x_2493_ = l_Lean_Meta_Context_config(v___y_2207_);
                                            v_foApprox_2494_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                0 as u32,
                                            );
                                            v_ctxApprox_2495_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                1 as u32,
                                            );
                                            v_quasiPatternApprox_2496_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    2 as u32,
                                                );
                                            v_constApprox_2497_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                3 as u32,
                                            );
                                            v_isDefEqStuckEx_2498_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    4 as u32,
                                                );
                                            v_unificationHints_2499_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    5 as u32,
                                                );
                                            v_proofIrrelevance_2500_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    6 as u32,
                                                );
                                            v_assignSyntheticOpaque_2501_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    7 as u32,
                                                );
                                            v_offsetCnstrs_2502_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    8 as u32,
                                                );
                                            v_etaStruct_2503_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                10 as u32,
                                            );
                                            v_univApprox_2504_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                11 as u32,
                                            );
                                            v_iota_2505_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                12 as u32,
                                            );
                                            v_beta_2506_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                13 as u32,
                                            );
                                            v_proj_2507_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                14 as u32,
                                            );
                                            v_zeta_2508_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                15 as u32,
                                            );
                                            v_zetaDelta_2509_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                16 as u32,
                                            );
                                            v_zetaUnused_2510_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                17 as u32,
                                            );
                                            v_zetaHave_2511_ = leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                18 as u32,
                                            );
                                            v_isSharedCheck_2550_ =
                                                (!leanh::lean_is_exclusive(v___x_2493_))
                                                    as u8;
                                            if v_isSharedCheck_2550_ == 0 {
                                                v___x_2513_ = v___x_2493_;
                                                v_isShared_2514_ = v_isSharedCheck_2550_;
                                                state = 38;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___x_2493_);
                                                v___x_2513_ = leanh::lean_box(0);
                                                v_isShared_2514_ = v_isSharedCheck_2550_;
                                                state = 38;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_2383_);
                                            leanh::lean_dec(v_declName_2248_);
                                            leanh::lean_dec_ref(v_arg_2244_);
                                            leanh::lean_dec_ref(v_arg_2241_);
                                            leanh::lean_dec_ref(v_arg_2238_);
                                            leanh::lean_dec_ref(v_e_2199_);
                                            v_a_2551_ = leanh::lean_ctor_get(v___x_2491_, 0);
                                            v_isSharedCheck_2558_ =
                                                (!leanh::lean_is_exclusive(v___x_2491_))
                                                    as u8;
                                            if v_isSharedCheck_2558_ == 0 {
                                                v___x_2553_ = v___x_2491_;
                                                v_isShared_2554_ = v_isSharedCheck_2558_;
                                                state = 42;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2551_);
                                                leanh::lean_dec(v___x_2491_);
                                                v___x_2553_ = leanh::lean_box(0);
                                                v_isShared_2554_ = v_isSharedCheck_2558_;
                                                state = 42;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_declName_2248_);
                                        leanh::lean_dec_ref(v_arg_2244_);
                                        leanh::lean_dec_ref(v_arg_2241_);
                                        leanh::lean_dec_ref(v_arg_2238_);
                                        leanh::lean_dec_ref(v_e_2199_);
                                        v_a_2559_ = leanh::lean_ctor_get(v___x_2382_, 0);
                                        v_isSharedCheck_2566_ =
                                            (!leanh::lean_is_exclusive(v___x_2382_)) as u8;
                                        if v_isSharedCheck_2566_ == 0 {
                                            v___x_2561_ = v___x_2382_;
                                            v_isShared_2562_ = v_isSharedCheck_2566_;
                                            state = 44;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2559_);
                                            leanh::lean_dec(v___x_2382_);
                                            v___x_2561_ = leanh::lean_box(0);
                                            v_isShared_2562_ = v_isSharedCheck_2566_;
                                            state = 44;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                return v___x_2234_;
            }
            7 => {
                v___x_2262_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_2199_, v___y_2252_);
                leanh::lean_dec_ref(v_e_2199_);
                if leanh::lean_obj_tag(v___x_2262_) == 0 {
                    v_a_2263_ = leanh::lean_ctor_get(v___x_2262_, 0);
                    leanh::lean_inc(v_a_2263_);
                    leanh::lean_dec_ref_known(v___x_2262_, 1);
                    v___x_2264_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2265_ = lean_nat_add(v_a_2263_, v___x_2264_);
                    leanh::lean_dec(v_a_2263_);
                    v___x_2266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2266_, 0, v_declName_2248_);
                    v___x_2267_ = leanh::lean_box(1);
                    v___x_2268_ = l_Lean_Meta_Grind_addNewRawFact(
                        v___y_2250_,
                        v___y_2251_,
                        v___x_2265_,
                        v___x_2266_,
                        v___x_2267_,
                        v___y_2252_,
                        v___y_2253_,
                        v___y_2254_,
                        v___y_2255_,
                        v___y_2256_,
                        v___y_2257_,
                        v___y_2258_,
                        v___y_2259_,
                        v___y_2260_,
                        v___y_2261_,
                    );
                    return v___x_2268_;
                } else {
                    leanh::lean_dec_ref(v___y_2251_);
                    leanh::lean_dec_ref(v___y_2250_);
                    leanh::lean_dec(v_declName_2248_);
                    v_a_2269_ = leanh::lean_ctor_get(v___x_2262_, 0);
                    v_isSharedCheck_2276_ = (!leanh::lean_is_exclusive(v___x_2262_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v___x_2271_ = v___x_2262_;
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2269_);
                        leanh::lean_dec(v___x_2262_);
                        v___x_2271_ = leanh::lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2272_ == 0 {
                    v___x_2274_ = v___x_2271_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
                    v___x_2274_ = v_reuseFailAlloc_2275_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2274_;
            }
            10 => {
                if v___y_2280_ == 0 {
                    v_options_2281_ = leanh::lean_ctor_get(v___y_2209_, 2);
                    v_hasTrace_2282_ = leanh::lean_ctor_get_uint8(
                        v_options_2281_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2282_ == 0 {
                        v___y_2250_ = v___y_2278_;
                        v___y_2251_ = v___y_2279_;
                        v___y_2252_ = v___y_2201_;
                        v___y_2253_ = v___y_2202_;
                        v___y_2254_ = v___y_2203_;
                        v___y_2255_ = v___y_2204_;
                        v___y_2256_ = v___y_2205_;
                        v___y_2257_ = v___y_2206_;
                        v___y_2258_ = v___y_2207_;
                        v___y_2259_ = v___y_2208_;
                        v___y_2260_ = v___y_2209_;
                        v___y_2261_ = v___y_2210_;
                        state = 7;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2283_ =
                            leanh::lean_ctor_get(v___y_2209_, 13);
                        v___x_2284_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4;
                        v___x_2285_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once
                            ),
                            _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7,
                        );
                        v___x_2286_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2283_,
                            v_options_2281_,
                            v___x_2285_,
                        );
                        if v___x_2286_ == 0 {
                            v___y_2250_ = v___y_2278_;
                            v___y_2251_ = v___y_2279_;
                            v___y_2252_ = v___y_2201_;
                            v___y_2253_ = v___y_2202_;
                            v___y_2254_ = v___y_2203_;
                            v___y_2255_ = v___y_2204_;
                            v___y_2256_ = v___y_2205_;
                            v___y_2257_ = v___y_2206_;
                            v___y_2258_ = v___y_2207_;
                            v___y_2259_ = v___y_2208_;
                            v___y_2260_ = v___y_2209_;
                            v___y_2261_ = v___y_2210_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_2248_);
                            v___x_2287_ = l_Lean_MessageData_ofName(v_declName_2248_);
                            v___x_2288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
                            v___x_2289_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2289_, 0, v___x_2287_);
                            leanh::lean_ctor_set(v___x_2289_, 1, v___x_2288_);
                            leanh::lean_inc_ref(v___y_2279_);
                            v___x_2290_ = l_Lean_MessageData_ofExpr(v___y_2279_);
                            v___x_2291_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2291_, 0, v___x_2289_);
                            leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
                            v___x_2292_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_2284_, v___x_2291_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                            if leanh::lean_obj_tag(v___x_2292_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2292_, 1);
                                v___y_2250_ = v___y_2278_;
                                v___y_2251_ = v___y_2279_;
                                v___y_2252_ = v___y_2201_;
                                v___y_2253_ = v___y_2202_;
                                v___y_2254_ = v___y_2203_;
                                v___y_2255_ = v___y_2204_;
                                v___y_2256_ = v___y_2205_;
                                v___y_2257_ = v___y_2206_;
                                v___y_2258_ = v___y_2207_;
                                v___y_2259_ = v___y_2208_;
                                v___y_2260_ = v___y_2209_;
                                v___y_2261_ = v___y_2210_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___y_2279_);
                                leanh::lean_dec_ref(v___y_2278_);
                                leanh::lean_dec(v_declName_2248_);
                                leanh::lean_dec_ref(v_e_2199_);
                                return v___x_2292_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2279_);
                    leanh::lean_dec_ref(v___y_2278_);
                    v___x_2293_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_2205_);
                    if leanh::lean_obj_tag(v___x_2293_) == 0 {
                        v_a_2294_ = leanh::lean_ctor_get(v___x_2293_, 0);
                        leanh::lean_inc(v_a_2294_);
                        leanh::lean_dec_ref_known(v___x_2293_, 1);
                        v___x_2295_ = (leanh::lean_unbox(v_a_2294_) as u8);
                        leanh::lean_dec(v_a_2294_);
                        if v___x_2295_ == 0 {
                            leanh::lean_dec(v_declName_2248_);
                            leanh::lean_dec_ref(v_e_2199_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
                            v___x_2297_ = l_Lean_MessageData_ofName(v_declName_2248_);
                            v___x_2298_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                            leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
                            v___x_2299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
                            v___x_2300_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2300_, 0, v___x_2298_);
                            leanh::lean_ctor_set(v___x_2300_, 1, v___x_2299_);
                            v___x_2301_ = l_Lean_indentExpr(v_e_2199_);
                            v___x_2302_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2302_, 0, v___x_2300_);
                            leanh::lean_ctor_set(v___x_2302_, 1, v___x_2301_);
                            v___x_2303_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
                            v___x_2304_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2304_, 0, v___x_2302_);
                            leanh::lean_ctor_set(v___x_2304_, 1, v___x_2303_);
                            v___x_2305_ = l_Lean_Meta_Sym_reportIssue(
                                v___x_2304_,
                                v___y_2205_,
                                v___y_2206_,
                                v___y_2207_,
                                v___y_2208_,
                                v___y_2209_,
                                v___y_2210_,
                            );
                            if leanh::lean_obj_tag(v___x_2305_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2305_, 1);
                                state = 1;
                                continue;
                            } else {
                                return v___x_2305_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_declName_2248_);
                        leanh::lean_dec_ref(v_e_2199_);
                        v_a_2306_ = leanh::lean_ctor_get(v___x_2293_, 0);
                        v_isSharedCheck_2313_ =
                            (!leanh::lean_is_exclusive(v___x_2293_)) as u8;
                        if v_isSharedCheck_2313_ == 0 {
                            v___x_2308_ = v___x_2293_;
                            v_isShared_2309_ = v_isSharedCheck_2313_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2306_);
                            leanh::lean_dec(v___x_2293_);
                            v___x_2308_ = leanh::lean_box(0);
                            v_isShared_2309_ = v_isSharedCheck_2313_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            11 => {
                if v_isShared_2309_ == 0 {
                    v___x_2311_ = v___x_2308_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2312_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
                    v___x_2311_ = v_reuseFailAlloc_2312_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2311_;
            }
            13 => {
                v___x_2318_ = 0;
                v___x_2319_ = 1;
                v___x_2320_ = l_Lean_Meta_mkLambdaFVars(
                    v_a_2317_,
                    v___y_2315_,
                    v___x_2318_,
                    v___y_2316_,
                    v___x_2318_,
                    v___y_2316_,
                    v___x_2319_,
                    v___y_2207_,
                    v___y_2208_,
                    v___y_2209_,
                    v___y_2210_,
                );
                leanh::lean_dec_ref(v_a_2317_);
                if leanh::lean_obj_tag(v___x_2320_) == 0 {
                    v_a_2321_ = leanh::lean_ctor_get(v___x_2320_, 0);
                    leanh::lean_inc(v_a_2321_);
                    leanh::lean_dec_ref_known(v___x_2320_, 1);
                    v___x_2322_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_2321_, v___y_2208_);
                    v_a_2323_ = leanh::lean_ctor_get(v___x_2322_, 0);
                    leanh::lean_inc_n(v_a_2323_, 2);
                    leanh::lean_dec_ref(v___x_2322_);
                    leanh::lean_inc(v___y_2210_);
                    leanh::lean_inc_ref(v___y_2209_);
                    leanh::lean_inc(v___y_2208_);
                    leanh::lean_inc_ref(v___y_2207_);
                    v___x_2324_ = lean_infer_type(
                        v_a_2323_,
                        v___y_2207_,
                        v___y_2208_,
                        v___y_2209_,
                        v___y_2210_,
                    );
                    if leanh::lean_obj_tag(v___x_2324_) == 0 {
                        v_a_2325_ = leanh::lean_ctor_get(v___x_2324_, 0);
                        leanh::lean_inc(v_a_2325_);
                        leanh::lean_dec_ref_known(v___x_2324_, 1);
                        v___x_2326_ = l_Lean_Expr_hasMVar(v_a_2323_);
                        if v___x_2326_ == 0 {
                            v___x_2327_ = l_Lean_Expr_hasMVar(v_a_2325_);
                            v___y_2278_ = v_a_2323_;
                            v___y_2279_ = v_a_2325_;
                            v___y_2280_ = v___x_2327_;
                            state = 10;
                            continue;
                        } else {
                            v___y_2278_ = v_a_2323_;
                            v___y_2279_ = v_a_2325_;
                            v___y_2280_ = v___y_2316_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2323_);
                        leanh::lean_dec(v_declName_2248_);
                        leanh::lean_dec_ref(v_e_2199_);
                        v_a_2328_ = leanh::lean_ctor_get(v___x_2324_, 0);
                        v_isSharedCheck_2335_ =
                            (!leanh::lean_is_exclusive(v___x_2324_)) as u8;
                        if v_isSharedCheck_2335_ == 0 {
                            v___x_2330_ = v___x_2324_;
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2328_);
                            leanh::lean_dec(v___x_2324_);
                            v___x_2330_ = leanh::lean_box(0);
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_2248_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v_a_2336_ = leanh::lean_ctor_get(v___x_2320_, 0);
                    v_isSharedCheck_2343_ = (!leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2343_ == 0 {
                        v___x_2338_ = v___x_2320_;
                        v_isShared_2339_ = v_isSharedCheck_2343_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2336_);
                        leanh::lean_dec(v___x_2320_);
                        v___x_2338_ = leanh::lean_box(0);
                        v_isShared_2339_ = v_isSharedCheck_2343_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2331_ == 0 {
                    v___x_2333_ = v___x_2330_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
                    v___x_2333_ = v_reuseFailAlloc_2334_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2333_;
            }
            16 => {
                if v_isShared_2339_ == 0 {
                    v___x_2341_ = v___x_2338_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2341_;
            }
            18 => {
                if leanh::lean_obj_tag(v___y_2347_) == 0 {
                    v_a_2348_ = leanh::lean_ctor_get(v___y_2347_, 0);
                    leanh::lean_inc(v_a_2348_);
                    leanh::lean_dec_ref_known(v___y_2347_, 1);
                    v___y_2315_ = v___y_2345_;
                    v___y_2316_ = v___y_2346_;
                    v_a_2317_ = v_a_2348_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_2345_);
                    leanh::lean_dec(v_declName_2248_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v_a_2349_ = leanh::lean_ctor_get(v___y_2347_, 0);
                    v_isSharedCheck_2356_ = (!leanh::lean_is_exclusive(v___y_2347_)) as u8;
                    if v_isSharedCheck_2356_ == 0 {
                        v___x_2351_ = v___y_2347_;
                        v_isShared_2352_ = v_isSharedCheck_2356_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2349_);
                        leanh::lean_dec(v___y_2347_);
                        v___x_2351_ = leanh::lean_box(0);
                        v_isShared_2352_ = v_isSharedCheck_2356_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_2352_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
                    v___x_2354_ = v_reuseFailAlloc_2355_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2354_;
            }
            21 => {
                v___x_2359_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_2205_);
                if leanh::lean_obj_tag(v___x_2359_) == 0 {
                    v_a_2360_ = leanh::lean_ctor_get(v___x_2359_, 0);
                    leanh::lean_inc(v_a_2360_);
                    leanh::lean_dec_ref_known(v___x_2359_, 1);
                    v___x_2361_ = (leanh::lean_unbox(v_a_2360_) as u8);
                    leanh::lean_dec(v_a_2360_);
                    if v___x_2361_ == 0 {
                        leanh::lean_dec_ref(v___y_2358_);
                        leanh::lean_dec(v_declName_2248_);
                        leanh::lean_dec_ref(v_e_2199_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2362_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once
                            ),
                            _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11,
                        );
                        v___x_2363_ = l_Lean_MessageData_ofName(v_declName_2248_);
                        v___x_2364_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2364_, 0, v___x_2362_);
                        leanh::lean_ctor_set(v___x_2364_, 1, v___x_2363_);
                        v___x_2365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
                        v___x_2366_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2366_, 0, v___x_2364_);
                        leanh::lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                        v___x_2367_ = l_Lean_indentExpr(v_e_2199_);
                        v___x_2368_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2368_, 0, v___x_2366_);
                        leanh::lean_ctor_set(v___x_2368_, 1, v___x_2367_);
                        v___x_2369_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once
                            ),
                            _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15,
                        );
                        v___x_2370_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2370_, 0, v___x_2368_);
                        leanh::lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                        v___x_2371_ = l_Lean_indentExpr(v___y_2358_);
                        v___x_2372_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2372_, 0, v___x_2370_);
                        leanh::lean_ctor_set(v___x_2372_, 1, v___x_2371_);
                        v___x_2373_ = l_Lean_Meta_Sym_reportIssue(
                            v___x_2372_,
                            v___y_2205_,
                            v___y_2206_,
                            v___y_2207_,
                            v___y_2208_,
                            v___y_2209_,
                            v___y_2210_,
                        );
                        if leanh::lean_obj_tag(v___x_2373_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2373_, 1);
                            state = 2;
                            continue;
                        } else {
                            return v___x_2373_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2358_);
                    leanh::lean_dec(v_declName_2248_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v_a_2374_ = leanh::lean_ctor_get(v___x_2359_, 0);
                    v_isSharedCheck_2381_ = (!leanh::lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2376_ = v___x_2359_;
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2374_);
                        leanh::lean_dec(v___x_2359_);
                        v___x_2376_ = leanh::lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_2377_ == 0 {
                    v___x_2379_ = v___x_2376_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2379_;
            }
            24 => {
                if leanh::lean_obj_tag(v___y_2389_) == 0 {
                    v_a_2390_ = leanh::lean_ctor_get(v___y_2389_, 0);
                    leanh::lean_inc(v_a_2390_);
                    leanh::lean_dec_ref_known(v___y_2389_, 1);
                    v___x_2391_ = (leanh::lean_unbox(v_a_2390_) as u8);
                    leanh::lean_dec(v_a_2390_);
                    if v___x_2391_ == 0 {
                        leanh::lean_dec_ref(v___y_2388_);
                        leanh::lean_dec_ref(v___y_2387_);
                        leanh::lean_dec(v_a_2383_);
                        v___y_2358_ = v___y_2385_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_2385_);
                        v___x_2392_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2393_ = lean_array_get_size(v___y_2388_);
                        v___x_2394_ =
                            l_Array_toSubarray___redArg(v___y_2388_, v___x_2392_, v___x_2393_);
                        v___x_2395_ = leanh::lean_box(0);
                        v___x_2396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2396_, 0, v___x_2395_);
                        leanh::lean_ctor_set(v___x_2396_, 1, v___x_2394_);
                        v_sz_2397_ = lean_array_size(v___y_2387_);
                        v___x_2398_ = 0usize;
                        leanh::lean_inc_ref(v_e_2199_);
                        leanh::lean_inc(v_declName_2248_);
                        v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_2248_, v_e_2199_, v___y_2387_, v_sz_2397_, v___x_2398_, v___x_2396_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                        if leanh::lean_obj_tag(v___x_2399_) == 0 {
                            v_a_2400_ = leanh::lean_ctor_get(v___x_2399_, 0);
                            v_isSharedCheck_2442_ =
                                (!leanh::lean_is_exclusive(v___x_2399_)) as u8;
                            if v_isSharedCheck_2442_ == 0 {
                                v___x_2402_ = v___x_2399_;
                                v_isShared_2403_ = v_isSharedCheck_2442_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2400_);
                                leanh::lean_dec(v___x_2399_);
                                v___x_2402_ = leanh::lean_box(0);
                                v_isShared_2403_ = v_isSharedCheck_2442_;
                                state = 25;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___y_2387_);
                            leanh::lean_dec(v_a_2383_);
                            leanh::lean_dec(v_declName_2248_);
                            leanh::lean_dec_ref(v_e_2199_);
                            v_a_2443_ = leanh::lean_ctor_get(v___x_2399_, 0);
                            v_isSharedCheck_2450_ =
                                (!leanh::lean_is_exclusive(v___x_2399_)) as u8;
                            if v_isSharedCheck_2450_ == 0 {
                                v___x_2445_ = v___x_2399_;
                                v_isShared_2446_ = v_isSharedCheck_2450_;
                                state = 31;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2443_);
                                leanh::lean_dec(v___x_2399_);
                                v___x_2445_ = leanh::lean_box(0);
                                v_isShared_2446_ = v_isSharedCheck_2450_;
                                state = 31;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2388_);
                    leanh::lean_dec_ref(v___y_2387_);
                    leanh::lean_dec_ref(v___y_2385_);
                    leanh::lean_dec(v_a_2383_);
                    leanh::lean_dec(v_declName_2248_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v_a_2451_ = leanh::lean_ctor_get(v___y_2389_, 0);
                    v_isSharedCheck_2458_ = (!leanh::lean_is_exclusive(v___y_2389_)) as u8;
                    if v_isSharedCheck_2458_ == 0 {
                        v___x_2453_ = v___y_2389_;
                        v_isShared_2454_ = v_isSharedCheck_2458_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2451_);
                        leanh::lean_dec(v___y_2389_);
                        v___x_2453_ = leanh::lean_box(0);
                        v_isShared_2454_ = v_isSharedCheck_2458_;
                        state = 33;
                        continue;
                    }
                }
            }
            25 => {
                v_fst_2404_ = leanh::lean_ctor_get(v_a_2400_, 0);
                leanh::lean_inc(v_fst_2404_);
                leanh::lean_dec(v_a_2400_);
                if leanh::lean_obj_tag(v_fst_2404_) == 0 {
                    leanh::lean_del_object(v___x_2402_);
                    v___x_2405_ = l_Lean_mkAppN(v_a_2383_, v___y_2387_);
                    v___x_2406_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_2405_, v___y_2208_);
                    v_a_2407_ = leanh::lean_ctor_get(v___x_2406_, 0);
                    leanh::lean_inc(v_a_2407_);
                    leanh::lean_dec_ref(v___x_2406_);
                    leanh::lean_inc_ref(v_e_2199_);
                    v___x_2408_ = l_Lean_Meta_Grind_mkEqFalseProof(
                        v_e_2199_,
                        v___y_2201_,
                        v___y_2202_,
                        v___y_2203_,
                        v___y_2204_,
                        v___y_2205_,
                        v___y_2206_,
                        v___y_2207_,
                        v___y_2208_,
                        v___y_2209_,
                        v___y_2210_,
                    );
                    if leanh::lean_obj_tag(v___x_2408_) == 0 {
                        v_a_2409_ = leanh::lean_ctor_get(v___x_2408_, 0);
                        leanh::lean_inc(v_a_2409_);
                        leanh::lean_dec_ref_known(v___x_2408_, 1);
                        v___x_2410_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_2205_);
                        if leanh::lean_obj_tag(v___x_2410_) == 0 {
                            v_a_2411_ = leanh::lean_ctor_get(v___x_2410_, 0);
                            leanh::lean_inc(v_a_2411_);
                            leanh::lean_dec_ref_known(v___x_2410_, 1);
                            v___x_2412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
                            leanh::lean_inc_ref(v_e_2199_);
                            v___x_2413_ = l_Lean_mkApp4(
                                v___x_2412_,
                                v_e_2199_,
                                v_a_2411_,
                                v_a_2409_,
                                v_a_2407_,
                            );
                            v___x_2414_ = lean_array_get_size(v___y_2387_);
                            v___x_2415_ =
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20;
                            v___x_2416_ = lean_nat_dec_lt(v___x_2392_, v___x_2414_);
                            if v___x_2416_ == 0 {
                                leanh::lean_dec_ref(v___y_2387_);
                                v___y_2315_ = v___x_2413_;
                                v___y_2316_ = v___y_2386_;
                                v_a_2317_ = v___x_2415_;
                                state = 13;
                                continue;
                            } else {
                                v___x_2417_ = lean_nat_dec_le(v___x_2414_, v___x_2414_);
                                if v___x_2417_ == 0 {
                                    if v___x_2416_ == 0 {
                                        leanh::lean_dec_ref(v___y_2387_);
                                        v___y_2315_ = v___x_2413_;
                                        v___y_2316_ = v___y_2386_;
                                        v_a_2317_ = v___x_2415_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___x_2418_ = lean_usize_of_nat(v___x_2414_);
                                        v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_2387_, v___x_2398_, v___x_2418_, v___x_2415_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                                        leanh::lean_dec_ref(v___y_2387_);
                                        v___y_2345_ = v___x_2413_;
                                        v___y_2346_ = v___y_2386_;
                                        v___y_2347_ = v___x_2419_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_2420_ = lean_usize_of_nat(v___x_2414_);
                                    v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_2387_, v___x_2398_, v___x_2420_, v___x_2415_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                                    leanh::lean_dec_ref(v___y_2387_);
                                    v___y_2345_ = v___x_2413_;
                                    v___y_2346_ = v___y_2386_;
                                    v___y_2347_ = v___x_2421_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2409_);
                            leanh::lean_dec(v_a_2407_);
                            leanh::lean_dec_ref(v___y_2387_);
                            leanh::lean_dec(v_declName_2248_);
                            leanh::lean_dec_ref(v_e_2199_);
                            v_a_2422_ = leanh::lean_ctor_get(v___x_2410_, 0);
                            v_isSharedCheck_2429_ =
                                (!leanh::lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2429_ == 0 {
                                v___x_2424_ = v___x_2410_;
                                v_isShared_2425_ = v_isSharedCheck_2429_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2422_);
                                leanh::lean_dec(v___x_2410_);
                                v___x_2424_ = leanh::lean_box(0);
                                v_isShared_2425_ = v_isSharedCheck_2429_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2407_);
                        leanh::lean_dec_ref(v___y_2387_);
                        leanh::lean_dec(v_declName_2248_);
                        leanh::lean_dec_ref(v_e_2199_);
                        v_a_2430_ = leanh::lean_ctor_get(v___x_2408_, 0);
                        v_isSharedCheck_2437_ =
                            (!leanh::lean_is_exclusive(v___x_2408_)) as u8;
                        if v_isSharedCheck_2437_ == 0 {
                            v___x_2432_ = v___x_2408_;
                            v_isShared_2433_ = v_isSharedCheck_2437_;
                            state = 28;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2430_);
                            leanh::lean_dec(v___x_2408_);
                            v___x_2432_ = leanh::lean_box(0);
                            v_isShared_2433_ = v_isSharedCheck_2437_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2387_);
                    leanh::lean_dec(v_a_2383_);
                    leanh::lean_dec(v_declName_2248_);
                    leanh::lean_dec_ref(v_e_2199_);
                    v_val_2438_ = leanh::lean_ctor_get(v_fst_2404_, 0);
                    leanh::lean_inc(v_val_2438_);
                    leanh::lean_dec_ref_known(v_fst_2404_, 1);
                    if v_isShared_2403_ == 0 {
                        leanh::lean_ctor_set(v___x_2402_, 0, v_val_2438_);
                        v___x_2440_ = v___x_2402_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_2441_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_val_2438_);
                        v___x_2440_ = v_reuseFailAlloc_2441_;
                        state = 30;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_2425_ == 0 {
                    v___x_2427_ = v___x_2424_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
                    v___x_2427_ = v_reuseFailAlloc_2428_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2427_;
            }
            28 => {
                if v_isShared_2433_ == 0 {
                    v___x_2435_ = v___x_2432_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2436_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
                    v___x_2435_ = v_reuseFailAlloc_2436_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2435_;
            }
            30 => {
                return v___x_2440_;
            }
            31 => {
                if v_isShared_2446_ == 0 {
                    v___x_2448_ = v___x_2445_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
                    v___x_2448_ = v_reuseFailAlloc_2449_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2448_;
            }
            33 => {
                if v_isShared_2454_ == 0 {
                    v___x_2456_ = v___x_2453_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
                    v___x_2456_ = v_reuseFailAlloc_2457_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2456_;
            }
            35 => {
                v_snd_2461_ = leanh::lean_ctor_get(v_a_2460_, 1);
                leanh::lean_inc(v_snd_2461_);
                v_fst_2462_ = leanh::lean_ctor_get(v_a_2460_, 0);
                leanh::lean_inc(v_fst_2462_);
                leanh::lean_dec_ref(v_a_2460_);
                v_fst_2463_ = leanh::lean_ctor_get(v_snd_2461_, 0);
                leanh::lean_inc(v_fst_2463_);
                v_snd_2464_ = leanh::lean_ctor_get(v_snd_2461_, 1);
                leanh::lean_inc_n(v_snd_2464_, 2);
                leanh::lean_dec(v_snd_2461_);
                v___x_2465_ = l_Lean_Expr_cleanupAnnotations(v_snd_2464_);
                v___x_2466_ = l_Lean_Expr_isApp(v___x_2465_);
                if v___x_2466_ == 0 {
                    leanh::lean_dec_ref(v___x_2465_);
                    leanh::lean_dec(v_snd_2464_);
                    leanh::lean_dec(v_fst_2463_);
                    leanh::lean_dec(v_fst_2462_);
                    leanh::lean_dec(v_a_2383_);
                    leanh::lean_dec(v_declName_2248_);
                    leanh::lean_dec_ref(v_arg_2244_);
                    leanh::lean_dec_ref(v_arg_2241_);
                    leanh::lean_dec_ref(v_arg_2238_);
                    leanh::lean_dec_ref(v_e_2199_);
                    state = 3;
                    continue;
                } else {
                    v_arg_2467_ = leanh::lean_ctor_get(v___x_2465_, 1);
                    leanh::lean_inc_ref(v_arg_2467_);
                    v___x_2468_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2465_);
                    v___x_2469_ = l_Lean_Expr_isApp(v___x_2468_);
                    if v___x_2469_ == 0 {
                        leanh::lean_dec_ref(v___x_2468_);
                        leanh::lean_dec_ref(v_arg_2467_);
                        leanh::lean_dec(v_snd_2464_);
                        leanh::lean_dec(v_fst_2463_);
                        leanh::lean_dec(v_fst_2462_);
                        leanh::lean_dec(v_a_2383_);
                        leanh::lean_dec(v_declName_2248_);
                        leanh::lean_dec_ref(v_arg_2244_);
                        leanh::lean_dec_ref(v_arg_2241_);
                        leanh::lean_dec_ref(v_arg_2238_);
                        leanh::lean_dec_ref(v_e_2199_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_2470_ = leanh::lean_ctor_get(v___x_2468_, 1);
                        leanh::lean_inc_ref(v_arg_2470_);
                        v___x_2471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2468_);
                        v___x_2472_ = l_Lean_Expr_isApp(v___x_2471_);
                        if v___x_2472_ == 0 {
                            leanh::lean_dec_ref(v___x_2471_);
                            leanh::lean_dec_ref(v_arg_2470_);
                            leanh::lean_dec_ref(v_arg_2467_);
                            leanh::lean_dec(v_snd_2464_);
                            leanh::lean_dec(v_fst_2463_);
                            leanh::lean_dec(v_fst_2462_);
                            leanh::lean_dec(v_a_2383_);
                            leanh::lean_dec(v_declName_2248_);
                            leanh::lean_dec_ref(v_arg_2244_);
                            leanh::lean_dec_ref(v_arg_2241_);
                            leanh::lean_dec_ref(v_arg_2238_);
                            leanh::lean_dec_ref(v_e_2199_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_2473_ = leanh::lean_ctor_get(v___x_2471_, 1);
                            leanh::lean_inc_ref(v_arg_2473_);
                            v___x_2474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2471_);
                            v___x_2475_ = l_Lean_Expr_isConstOf(v___x_2474_, v___x_2246_);
                            leanh::lean_dec_ref(v___x_2474_);
                            if v___x_2475_ == 0 {
                                leanh::lean_dec_ref(v_arg_2473_);
                                leanh::lean_dec_ref(v_arg_2470_);
                                leanh::lean_dec_ref(v_arg_2467_);
                                leanh::lean_dec(v_snd_2464_);
                                leanh::lean_dec(v_fst_2463_);
                                leanh::lean_dec(v_fst_2462_);
                                leanh::lean_dec(v_a_2383_);
                                leanh::lean_dec(v_declName_2248_);
                                leanh::lean_dec_ref(v_arg_2244_);
                                leanh::lean_dec_ref(v_arg_2241_);
                                leanh::lean_dec_ref(v_arg_2238_);
                                leanh::lean_dec_ref(v_e_2199_);
                                state = 3;
                                continue;
                            } else {
                                v___x_2476_ = l_Lean_Meta_isExprDefEq(
                                    v_arg_2244_,
                                    v_arg_2473_,
                                    v___y_2207_,
                                    v___y_2208_,
                                    v___y_2209_,
                                    v___y_2210_,
                                );
                                if leanh::lean_obj_tag(v___x_2476_) == 0 {
                                    v_a_2477_ = leanh::lean_ctor_get(v___x_2476_, 0);
                                    leanh::lean_inc(v_a_2477_);
                                    v___x_2478_ = (leanh::lean_unbox(v_a_2477_) as u8);
                                    leanh::lean_dec(v_a_2477_);
                                    if v___x_2478_ == 0 {
                                        leanh::lean_dec_ref(v_arg_2470_);
                                        leanh::lean_dec_ref(v_arg_2467_);
                                        leanh::lean_dec_ref(v_arg_2241_);
                                        leanh::lean_dec_ref(v_arg_2238_);
                                        v___y_2385_ = v_snd_2464_;
                                        v___y_2386_ = v___x_2475_;
                                        v___y_2387_ = v_fst_2462_;
                                        v___y_2388_ = v_fst_2463_;
                                        v___y_2389_ = v___x_2476_;
                                        state = 24;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_2476_, 1);
                                        v___x_2479_ =
                                            l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(
                                                v___x_2475_,
                                                v_arg_2470_,
                                                v_arg_2241_,
                                                v___y_2201_,
                                                v___y_2202_,
                                                v___y_2203_,
                                                v___y_2204_,
                                                v___y_2205_,
                                                v___y_2206_,
                                                v___y_2207_,
                                                v___y_2208_,
                                                v___y_2209_,
                                                v___y_2210_,
                                            );
                                        if leanh::lean_obj_tag(v___x_2479_) == 0 {
                                            v_a_2480_ = leanh::lean_ctor_get(v___x_2479_, 0);
                                            leanh::lean_inc(v_a_2480_);
                                            leanh::lean_dec_ref_known(v___x_2479_, 1);
                                            v___x_2481_ =
                                                (leanh::lean_unbox(v_a_2480_) as u8);
                                            leanh::lean_dec(v_a_2480_);
                                            if v___x_2481_ == 0 {
                                                leanh::lean_dec_ref(v_arg_2467_);
                                                leanh::lean_dec(v_fst_2463_);
                                                leanh::lean_dec(v_fst_2462_);
                                                leanh::lean_dec(v_a_2383_);
                                                leanh::lean_dec_ref(v_arg_2238_);
                                                v___y_2358_ = v_snd_2464_;
                                                state = 21;
                                                continue;
                                            } else {
                                                v___x_2482_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_2475_, v_arg_2467_, v_arg_2238_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                                                v___y_2385_ = v_snd_2464_;
                                                v___y_2386_ = v___x_2475_;
                                                v___y_2387_ = v_fst_2462_;
                                                v___y_2388_ = v_fst_2463_;
                                                v___y_2389_ = v___x_2482_;
                                                state = 24;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_2467_);
                                            leanh::lean_dec(v_snd_2464_);
                                            leanh::lean_dec(v_fst_2463_);
                                            leanh::lean_dec(v_fst_2462_);
                                            leanh::lean_dec(v_a_2383_);
                                            leanh::lean_dec(v_declName_2248_);
                                            leanh::lean_dec_ref(v_arg_2238_);
                                            leanh::lean_dec_ref(v_e_2199_);
                                            v_a_2483_ = leanh::lean_ctor_get(v___x_2479_, 0);
                                            v_isSharedCheck_2490_ =
                                                (!leanh::lean_is_exclusive(v___x_2479_))
                                                    as u8;
                                            if v_isSharedCheck_2490_ == 0 {
                                                v___x_2485_ = v___x_2479_;
                                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                                state = 36;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2483_);
                                                leanh::lean_dec(v___x_2479_);
                                                v___x_2485_ = leanh::lean_box(0);
                                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                                state = 36;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_2470_);
                                    leanh::lean_dec_ref(v_arg_2467_);
                                    leanh::lean_dec_ref(v_arg_2241_);
                                    leanh::lean_dec_ref(v_arg_2238_);
                                    v___y_2385_ = v_snd_2464_;
                                    v___y_2386_ = v___x_2475_;
                                    v___y_2387_ = v_fst_2462_;
                                    v___y_2388_ = v_fst_2463_;
                                    v___y_2389_ = v___x_2476_;
                                    state = 24;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            36 => {
                if v_isShared_2486_ == 0 {
                    v___x_2488_ = v___x_2485_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
                    v___x_2488_ = v_reuseFailAlloc_2489_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2488_;
            }
            38 => {
                v_trackZetaDelta_2515_ = leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2516_ = leanh::lean_ctor_get(v___y_2207_, 1);
                v_lctx_2517_ = leanh::lean_ctor_get(v___y_2207_, 2);
                v_localInstances_2518_ = leanh::lean_ctor_get(v___y_2207_, 3);
                v_defEqCtx_x3f_2519_ = leanh::lean_ctor_get(v___y_2207_, 4);
                v_synthPendingDepth_2520_ = leanh::lean_ctor_get(v___y_2207_, 5);
                v_canUnfold_x3f_2521_ = leanh::lean_ctor_get(v___y_2207_, 6);
                v_univApprox_2522_ = leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2523_ = leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2524_ = leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2525_ = 1;
                if v_isShared_2514_ == 0 {
                    v_config_2527_ = v___x_2513_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2549_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        0 as u32,
                        v_foApprox_2494_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        1 as u32,
                        v_ctxApprox_2495_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        2 as u32,
                        v_quasiPatternApprox_2496_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        3 as u32,
                        v_constApprox_2497_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        4 as u32,
                        v_isDefEqStuckEx_2498_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        5 as u32,
                        v_unificationHints_2499_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        6 as u32,
                        v_proofIrrelevance_2500_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        7 as u32,
                        v_assignSyntheticOpaque_2501_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        8 as u32,
                        v_offsetCnstrs_2502_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        10 as u32,
                        v_etaStruct_2503_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        11 as u32,
                        v_univApprox_2504_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        12 as u32,
                        v_iota_2505_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        13 as u32,
                        v_beta_2506_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        14 as u32,
                        v_proj_2507_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        15 as u32,
                        v_zeta_2508_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        16 as u32,
                        v_zetaDelta_2509_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        17 as u32,
                        v_zetaUnused_2510_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        18 as u32,
                        v_zetaHave_2511_,
                    );
                    v_config_2527_ = v_reuseFailAlloc_2549_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                leanh::lean_ctor_set_uint8(v_config_2527_, 9 as u32, v___x_2525_);
                v___x_2528_ = l_Lean_Meta_Context_configKey(v___y_2207_);
                v___x_2529_ = 3u64;
                v___x_2530_ = lean_uint64_shift_right(v___x_2528_, v___x_2529_);
                v___x_2531_ = leanh::lean_box(0);
                v___x_2532_ = 0;
                v___x_2533_ = lean_uint64_shift_left(v___x_2530_, v___x_2529_);
                v___x_2534_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once
                    ),
                    _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21,
                );
                v_key_2535_ = lean_uint64_lor(v___x_2533_, v___x_2534_);
                v___x_2536_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2536_, 0, v_config_2527_);
                leanh::lean_ctor_set_uint64(
                    v___x_2536_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2535_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2521_);
                leanh::lean_inc(v_synthPendingDepth_2520_);
                leanh::lean_inc(v_defEqCtx_x3f_2519_);
                leanh::lean_inc_ref(v_localInstances_2518_);
                leanh::lean_inc_ref(v_lctx_2517_);
                leanh::lean_inc(v_zetaDeltaSet_2516_);
                v___x_2537_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2537_, 0, v___x_2536_);
                leanh::lean_ctor_set(v___x_2537_, 1, v_zetaDeltaSet_2516_);
                leanh::lean_ctor_set(v___x_2537_, 2, v_lctx_2517_);
                leanh::lean_ctor_set(v___x_2537_, 3, v_localInstances_2518_);
                leanh::lean_ctor_set(v___x_2537_, 4, v_defEqCtx_x3f_2519_);
                leanh::lean_ctor_set(v___x_2537_, 5, v_synthPendingDepth_2520_);
                leanh::lean_ctor_set(v___x_2537_, 6, v_canUnfold_x3f_2521_);
                leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2515_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2522_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2523_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2524_,
                );
                v___x_2538_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_a_2492_,
                    v___x_2531_,
                    v___x_2532_,
                    v___x_2537_,
                    v___y_2208_,
                    v___y_2209_,
                    v___y_2210_,
                );
                leanh::lean_dec_ref_known(v___x_2537_, 7);
                if leanh::lean_obj_tag(v___x_2538_) == 0 {
                    v_a_2539_ = leanh::lean_ctor_get(v___x_2538_, 0);
                    leanh::lean_inc(v_a_2539_);
                    leanh::lean_dec_ref_known(v___x_2538_, 1);
                    v_a_2460_ = v_a_2539_;
                    state = 35;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_2538_) == 0 {
                        v_a_2540_ = leanh::lean_ctor_get(v___x_2538_, 0);
                        leanh::lean_inc(v_a_2540_);
                        leanh::lean_dec_ref_known(v___x_2538_, 1);
                        v_a_2460_ = v_a_2540_;
                        state = 35;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2383_);
                        leanh::lean_dec(v_declName_2248_);
                        leanh::lean_dec_ref(v_arg_2244_);
                        leanh::lean_dec_ref(v_arg_2241_);
                        leanh::lean_dec_ref(v_arg_2238_);
                        leanh::lean_dec_ref(v_e_2199_);
                        v_a_2541_ = leanh::lean_ctor_get(v___x_2538_, 0);
                        v_isSharedCheck_2548_ =
                            (!leanh::lean_is_exclusive(v___x_2538_)) as u8;
                        if v_isSharedCheck_2548_ == 0 {
                            v___x_2543_ = v___x_2538_;
                            v_isShared_2544_ = v_isSharedCheck_2548_;
                            state = 40;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2541_);
                            leanh::lean_dec(v___x_2538_);
                            v___x_2543_ = leanh::lean_box(0);
                            v_isShared_2544_ = v_isSharedCheck_2548_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            40 => {
                if v_isShared_2544_ == 0 {
                    v___x_2546_ = v___x_2543_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
                    v___x_2546_ = v_reuseFailAlloc_2547_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2546_;
            }
            42 => {
                if v_isShared_2554_ == 0 {
                    v___x_2556_ = v___x_2553_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2557_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
                    v___x_2556_ = v_reuseFailAlloc_2557_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_2556_;
            }
            44 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2565_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_2564_;
            }
            46 => {
                if v_isShared_2571_ == 0 {
                    v___x_2573_ = v___x_2570_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2573_;
            }
            48 => {
                if v_isShared_2579_ == 0 {
                    v___x_2581_ = v___x_2578_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2582_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_2581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(
    mut v_e_2584_: *mut leanh::LeanObject,
    mut v_thm_2585_: *mut leanh::LeanObject,
    mut v___y_2586_: *mut leanh::LeanObject,
    mut v___y_2587_: *mut leanh::LeanObject,
    mut v___y_2588_: *mut leanh::LeanObject,
    mut v___y_2589_: *mut leanh::LeanObject,
    mut v___y_2590_: *mut leanh::LeanObject,
    mut v___y_2591_: *mut leanh::LeanObject,
    mut v___y_2592_: *mut leanh::LeanObject,
    mut v___y_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(
        v_e_2584_,
        v_thm_2585_,
        v___y_2586_,
        v___y_2587_,
        v___y_2588_,
        v___y_2589_,
        v___y_2590_,
        v___y_2591_,
        v___y_2592_,
        v___y_2593_,
        v___y_2594_,
        v___y_2595_,
    );
    leanh::lean_dec(v___y_2595_);
    leanh::lean_dec_ref(v___y_2594_);
    leanh::lean_dec(v___y_2593_);
    leanh::lean_dec_ref(v___y_2592_);
    leanh::lean_dec(v___y_2591_);
    leanh::lean_dec_ref(v___y_2590_);
    leanh::lean_dec(v___y_2589_);
    leanh::lean_dec_ref(v___y_2588_);
    leanh::lean_dec(v___y_2587_);
    leanh::lean_dec(v___y_2586_);
    return v_res_2597_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem(
    mut v_thm_2598_: *mut leanh::LeanObject,
    mut v_e_2599_: *mut leanh::LeanObject,
    mut v_a_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
    mut v_a_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
    mut v_a_2607_: *mut leanh::LeanObject,
    mut v_a_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2611_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed as *mut core::ffi::c_void,
        13,
        2,
    );
    leanh::lean_closure_set(v___f_2611_, 0, v_e_2599_);
    leanh::lean_closure_set(v___f_2611_, 1, v_thm_2598_);
    v___x_2612_ = 0;
    v___x_2613_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_2611_, v___x_2612_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
    return v___x_2613_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___boxed(
    mut v_thm_2614_: *mut leanh::LeanObject,
    mut v_e_2615_: *mut leanh::LeanObject,
    mut v_a_2616_: *mut leanh::LeanObject,
    mut v_a_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
    mut v_a_2622_: *mut leanh::LeanObject,
    mut v_a_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
    mut v_a_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Lean_Meta_Grind_instantiateExtTheorem(
        v_thm_2614_,
        v_e_2615_,
        v_a_2616_,
        v_a_2617_,
        v_a_2618_,
        v_a_2619_,
        v_a_2620_,
        v_a_2621_,
        v_a_2622_,
        v_a_2623_,
        v_a_2624_,
        v_a_2625_,
    );
    leanh::lean_dec(v_a_2625_);
    leanh::lean_dec_ref(v_a_2624_);
    leanh::lean_dec(v_a_2623_);
    leanh::lean_dec_ref(v_a_2622_);
    leanh::lean_dec(v_a_2621_);
    leanh::lean_dec_ref(v_a_2620_);
    leanh::lean_dec(v_a_2619_);
    leanh::lean_dec_ref(v_a_2618_);
    leanh::lean_dec(v_a_2617_);
    leanh::lean_dec(v_a_2616_);
    return v_res_2627_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(
    mut v_mvarId_2628_: *mut leanh::LeanObject,
    mut v_val_2629_: *mut leanh::LeanObject,
    mut v___y_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
    mut v___y_2636_: *mut leanh::LeanObject,
    mut v___y_2637_: *mut leanh::LeanObject,
    mut v___y_2638_: *mut leanh::LeanObject,
    mut v___y_2639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(
            v_mvarId_2628_,
            v_val_2629_,
            v___y_2637_,
        );
    return v___x_2641_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(
    mut v_mvarId_2642_: *mut leanh::LeanObject,
    mut v_val_2643_: *mut leanh::LeanObject,
    mut v___y_2644_: *mut leanh::LeanObject,
    mut v___y_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
    mut v___y_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
    mut v___y_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(
        v_mvarId_2642_,
        v_val_2643_,
        v___y_2644_,
        v___y_2645_,
        v___y_2646_,
        v___y_2647_,
        v___y_2648_,
        v___y_2649_,
        v___y_2650_,
        v___y_2651_,
        v___y_2652_,
        v___y_2653_,
    );
    leanh::lean_dec(v___y_2653_);
    leanh::lean_dec_ref(v___y_2652_);
    leanh::lean_dec(v___y_2651_);
    leanh::lean_dec_ref(v___y_2650_);
    leanh::lean_dec(v___y_2649_);
    leanh::lean_dec_ref(v___y_2648_);
    leanh::lean_dec(v___y_2647_);
    leanh::lean_dec_ref(v___y_2646_);
    leanh::lean_dec(v___y_2645_);
    leanh::lean_dec(v___y_2644_);
    return v_res_2655_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(
    mut v_mvarId_2656_: *mut leanh::LeanObject,
    mut v___y_2657_: *mut leanh::LeanObject,
    mut v___y_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
    mut v___y_2665_: *mut leanh::LeanObject,
    mut v___y_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(
            v_mvarId_2656_,
            v___y_2664_,
        );
    return v___x_2668_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(
    mut v_mvarId_2669_: *mut leanh::LeanObject,
    mut v___y_2670_: *mut leanh::LeanObject,
    mut v___y_2671_: *mut leanh::LeanObject,
    mut v___y_2672_: *mut leanh::LeanObject,
    mut v___y_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
    mut v___y_2677_: *mut leanh::LeanObject,
    mut v___y_2678_: *mut leanh::LeanObject,
    mut v___y_2679_: *mut leanh::LeanObject,
    mut v___y_2680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2681_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(
        v_mvarId_2669_,
        v___y_2670_,
        v___y_2671_,
        v___y_2672_,
        v___y_2673_,
        v___y_2674_,
        v___y_2675_,
        v___y_2676_,
        v___y_2677_,
        v___y_2678_,
        v___y_2679_,
    );
    leanh::lean_dec(v___y_2679_);
    leanh::lean_dec_ref(v___y_2678_);
    leanh::lean_dec(v___y_2677_);
    leanh::lean_dec_ref(v___y_2676_);
    leanh::lean_dec(v___y_2675_);
    leanh::lean_dec_ref(v___y_2674_);
    leanh::lean_dec(v___y_2673_);
    leanh::lean_dec_ref(v___y_2672_);
    leanh::lean_dec(v___y_2671_);
    leanh::lean_dec(v___y_2670_);
    leanh::lean_dec(v_mvarId_2669_);
    return v_res_2681_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(
    mut v_cls_2682_: *mut leanh::LeanObject,
    mut v_msg_2683_: *mut leanh::LeanObject,
    mut v___y_2684_: *mut leanh::LeanObject,
    mut v___y_2685_: *mut leanh::LeanObject,
    mut v___y_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
    mut v___y_2689_: *mut leanh::LeanObject,
    mut v___y_2690_: *mut leanh::LeanObject,
    mut v___y_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
    mut v___y_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(
        v_cls_2682_,
        v_msg_2683_,
        v___y_2690_,
        v___y_2691_,
        v___y_2692_,
        v___y_2693_,
    );
    return v___x_2695_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(
    mut v_cls_2696_: *mut leanh::LeanObject,
    mut v_msg_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
    mut v___y_2700_: *mut leanh::LeanObject,
    mut v___y_2701_: *mut leanh::LeanObject,
    mut v___y_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
    mut v___y_2708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2709_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(
        v_cls_2696_,
        v_msg_2697_,
        v___y_2698_,
        v___y_2699_,
        v___y_2700_,
        v___y_2701_,
        v___y_2702_,
        v___y_2703_,
        v___y_2704_,
        v___y_2705_,
        v___y_2706_,
        v___y_2707_,
    );
    leanh::lean_dec(v___y_2707_);
    leanh::lean_dec_ref(v___y_2706_);
    leanh::lean_dec(v___y_2705_);
    leanh::lean_dec_ref(v___y_2704_);
    leanh::lean_dec(v___y_2703_);
    leanh::lean_dec_ref(v___y_2702_);
    leanh::lean_dec(v___y_2701_);
    leanh::lean_dec_ref(v___y_2700_);
    leanh::lean_dec(v___y_2699_);
    leanh::lean_dec(v___y_2698_);
    return v_res_2709_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(
    mut v_00_u03b2_2710_: *mut leanh::LeanObject,
    mut v_x_2711_: *mut leanh::LeanObject,
    mut v_x_2712_: *mut leanh::LeanObject,
    mut v_x_2713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_2711_, v_x_2712_, v_x_2713_);
    return v___x_2714_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(
    mut v_00_u03b2_2715_: *mut leanh::LeanObject,
    mut v_x_2716_: *mut leanh::LeanObject,
    mut v_x_2717_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2718_: u8 = 0;
    v___x_2718_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_2716_, v_x_2717_);
    return v___x_2718_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(
    mut v_00_u03b2_2719_: *mut leanh::LeanObject,
    mut v_x_2720_: *mut leanh::LeanObject,
    mut v_x_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2722_: u8 = 0;
    let mut v_r_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_2719_, v_x_2720_, v_x_2721_);
    leanh::lean_dec(v_x_2721_);
    leanh::lean_dec_ref(v_x_2720_);
    v_r_2723_ = leanh::lean_box((v_res_2722_) as usize);
    return v_r_2723_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(
    mut v_00_u03b2_2724_: *mut leanh::LeanObject,
    mut v_x_2725_: *mut leanh::LeanObject,
    mut v_x_2726_: usize,
    mut v_x_2727_: usize,
    mut v_x_2728_: *mut leanh::LeanObject,
    mut v_x_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_2725_, v_x_2726_, v_x_2727_, v_x_2728_, v_x_2729_);
    return v___x_2730_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_2731_: *mut leanh::LeanObject,
    mut v_x_2732_: *mut leanh::LeanObject,
    mut v_x_2733_: *mut leanh::LeanObject,
    mut v_x_2734_: *mut leanh::LeanObject,
    mut v_x_2735_: *mut leanh::LeanObject,
    mut v_x_2736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_217077__boxed_2737_: usize = 0;
    let mut v_x_217078__boxed_2738_: usize = 0;
    let mut v_res_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_217077__boxed_2737_ = leanh::lean_unbox_usize(v_x_2733_);
    leanh::lean_dec(v_x_2733_);
    v_x_217078__boxed_2738_ = leanh::lean_unbox_usize(v_x_2734_);
    leanh::lean_dec(v_x_2734_);
    v_res_2739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_2731_, v_x_2732_, v_x_217077__boxed_2737_, v_x_217078__boxed_2738_, v_x_2735_, v_x_2736_);
    return v_res_2739_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(
    mut v_00_u03b2_2740_: *mut leanh::LeanObject,
    mut v_x_2741_: *mut leanh::LeanObject,
    mut v_x_2742_: usize,
    mut v_x_2743_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2744_: u8 = 0;
    v___x_2744_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_2741_, v_x_2742_, v_x_2743_);
    return v___x_2744_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_2745_: *mut leanh::LeanObject,
    mut v_x_2746_: *mut leanh::LeanObject,
    mut v_x_2747_: *mut leanh::LeanObject,
    mut v_x_2748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_217094__boxed_2749_: usize = 0;
    let mut v_res_2750_: u8 = 0;
    let mut v_r_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_217094__boxed_2749_ = leanh::lean_unbox_usize(v_x_2747_);
    leanh::lean_dec(v_x_2747_);
    v_res_2750_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_2745_, v_x_2746_, v_x_217094__boxed_2749_, v_x_2748_);
    leanh::lean_dec(v_x_2748_);
    leanh::lean_dec_ref(v_x_2746_);
    v_r_2751_ = leanh::lean_box((v_res_2750_) as usize);
    return v_r_2751_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(
    mut v_00_u03b2_2752_: *mut leanh::LeanObject,
    mut v_n_2753_: *mut leanh::LeanObject,
    mut v_k_2754_: *mut leanh::LeanObject,
    mut v_v_2755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_2753_, v_k_2754_, v_v_2755_);
    return v___x_2756_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(
    mut v_00_u03b2_2757_: *mut leanh::LeanObject,
    mut v_depth_2758_: usize,
    mut v_keys_2759_: *mut leanh::LeanObject,
    mut v_vals_2760_: *mut leanh::LeanObject,
    mut v_heq_2761_: *mut leanh::LeanObject,
    mut v_i_2762_: *mut leanh::LeanObject,
    mut v_entries_2763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_2758_, v_keys_2759_, v_vals_2760_, v_i_2762_, v_entries_2763_);
    return v___x_2764_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(
    mut v_00_u03b2_2765_: *mut leanh::LeanObject,
    mut v_depth_2766_: *mut leanh::LeanObject,
    mut v_keys_2767_: *mut leanh::LeanObject,
    mut v_vals_2768_: *mut leanh::LeanObject,
    mut v_heq_2769_: *mut leanh::LeanObject,
    mut v_i_2770_: *mut leanh::LeanObject,
    mut v_entries_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2772_: usize = 0;
    let mut v_res_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2772_ = leanh::lean_unbox_usize(v_depth_2766_);
    leanh::lean_dec(v_depth_2766_);
    v_res_2773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2765_, v_depth_boxed_2772_, v_keys_2767_, v_vals_2768_, v_heq_2769_, v_i_2770_, v_entries_2771_);
    leanh::lean_dec_ref(v_vals_2768_);
    leanh::lean_dec_ref(v_keys_2767_);
    return v_res_2773_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(
    mut v_00_u03b2_2774_: *mut leanh::LeanObject,
    mut v_keys_2775_: *mut leanh::LeanObject,
    mut v_vals_2776_: *mut leanh::LeanObject,
    mut v_heq_2777_: *mut leanh::LeanObject,
    mut v_i_2778_: *mut leanh::LeanObject,
    mut v_k_2779_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2780_: u8 = 0;
    v___x_2780_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_2775_, v_i_2778_, v_k_2779_);
    return v___x_2780_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(
    mut v_00_u03b2_2781_: *mut leanh::LeanObject,
    mut v_keys_2782_: *mut leanh::LeanObject,
    mut v_vals_2783_: *mut leanh::LeanObject,
    mut v_heq_2784_: *mut leanh::LeanObject,
    mut v_i_2785_: *mut leanh::LeanObject,
    mut v_k_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2787_: u8 = 0;
    let mut v_r_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_2781_, v_keys_2782_, v_vals_2783_, v_heq_2784_, v_i_2785_, v_k_2786_);
    leanh::lean_dec(v_k_2786_);
    leanh::lean_dec_ref(v_vals_2783_);
    leanh::lean_dec_ref(v_keys_2782_);
    v_r_2788_ = leanh::lean_box((v_res_2787_) as usize);
    return v_r_2788_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(
    mut v_00_u03b2_2789_: *mut leanh::LeanObject,
    mut v_x_2790_: *mut leanh::LeanObject,
    mut v_x_2791_: *mut leanh::LeanObject,
    mut v_x_2792_: *mut leanh::LeanObject,
    mut v_x_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_2790_, v_x_2791_, v_x_2792_, v_x_2793_);
    return v___x_2794_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Ext(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Ext(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Ext(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
}