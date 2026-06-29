// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Ext
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.SynthInstance
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
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_infer_type;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1_value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 119, 104, 101, 110, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 110, 103, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 97, 108, 105, 116, 121, 32, 116, 104, 101, 111, 114, 101, 109, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [96, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12545347794981986237 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__16_value)
            as *mut crate::leanh::LeanObject,
        5647098122476602039 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20_value:
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
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21: u64 = 0;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(
    mut v_e_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_unused_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1401_ = l_Lean_Expr_hasMVar(v_e_1398_);
                if v___x_1401_ == 0 {
                    v___x_1402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1402_, 0, v_e_1398_);
                    return v___x_1402_;
                } else {
                    v___x_1403_ = lean_st_ref_get(v___y_1399_);
                    v_mctx_1404_ = crate::leanh::lean_ctor_get(v___x_1403_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1404_);
                    crate::leanh::lean_dec(v___x_1403_);
                    v___x_1405_ = l_Lean_instantiateMVarsCore(v_mctx_1404_, v_e_1398_);
                    v_fst_1406_ = crate::leanh::lean_ctor_get(v___x_1405_, 0);
                    crate::leanh::lean_inc(v_fst_1406_);
                    v_snd_1407_ = crate::leanh::lean_ctor_get(v___x_1405_, 1);
                    crate::leanh::lean_inc(v_snd_1407_);
                    crate::leanh::lean_dec_ref(v___x_1405_);
                    v___x_1408_ = lean_st_ref_take(v___y_1399_);
                    v_cache_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 1);
                    v_zetaDeltaFVarIds_1410_ = crate::leanh::lean_ctor_get(v___x_1408_, 2);
                    v_postponed_1411_ = crate::leanh::lean_ctor_get(v___x_1408_, 3);
                    v_diag_1412_ = crate::leanh::lean_ctor_get(v___x_1408_, 4);
                    v_isSharedCheck_1421_ = (!crate::leanh::lean_is_exclusive(v___x_1408_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v_unused_1422_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                        crate::leanh::lean_dec(v_unused_1422_);
                        v___x_1414_ = v___x_1408_;
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1412_);
                        crate::leanh::lean_inc(v_postponed_1411_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1410_);
                        crate::leanh::lean_inc(v_cache_1409_);
                        crate::leanh::lean_dec(v___x_1408_);
                        v___x_1414_ = crate::leanh::lean_box(0);
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1414_, 0, v_snd_1407_);
                    v___x_1417_ = v___x_1414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_snd_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_cache_1409_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1420_,
                        2,
                        v_zetaDeltaFVarIds_1410_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_postponed_1411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_diag_1412_);
                    v___x_1417_ = v_reuseFailAlloc_1420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1418_ = lean_st_ref_set(v___y_1399_, v___x_1417_);
                v___x_1419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1419_, 0, v_fst_1406_);
                return v___x_1419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(
    mut v_e_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(
            v_e_1423_,
            v___y_1424_,
        );
    crate::leanh::lean_dec(v___y_1424_);
    return v_res_1426_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(
    mut v_e_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(
            v_e_1427_,
            v___y_1435_,
        );
    return v___x_1439_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(
    mut v_e_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    crate::leanh::lean_dec(v___y_1448_);
    crate::leanh::lean_dec_ref(v___y_1447_);
    crate::leanh::lean_dec(v___y_1446_);
    crate::leanh::lean_dec_ref(v___y_1445_);
    crate::leanh::lean_dec(v___y_1444_);
    crate::leanh::lean_dec_ref(v___y_1443_);
    crate::leanh::lean_dec(v___y_1442_);
    crate::leanh::lean_dec(v___y_1441_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(
    mut v_k_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1459_);
    crate::leanh::lean_inc_ref(v___y_1458_);
    crate::leanh::lean_inc(v___y_1457_);
    crate::leanh::lean_inc_ref(v___y_1456_);
    crate::leanh::lean_inc(v___y_1455_);
    crate::leanh::lean_inc(v___y_1454_);
    v___x_1465_ = crate::leanh::lean_apply_11(
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
        crate::leanh::lean_box(0),
    );
    return v___x_1465_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(
    mut v_k_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(v_k_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
    crate::leanh::lean_dec(v___y_1472_);
    crate::leanh::lean_dec_ref(v___y_1471_);
    crate::leanh::lean_dec(v___y_1470_);
    crate::leanh::lean_dec_ref(v___y_1469_);
    crate::leanh::lean_dec(v___y_1468_);
    crate::leanh::lean_dec(v___y_1467_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(
    mut v_k_1479_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1480_: u8,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1486_);
                crate::leanh::lean_inc_ref(v___y_1485_);
                crate::leanh::lean_inc(v___y_1484_);
                crate::leanh::lean_inc_ref(v___y_1483_);
                crate::leanh::lean_inc(v___y_1482_);
                crate::leanh::lean_inc(v___y_1481_);
                v___f_1492_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 7);
                crate::leanh::lean_closure_set(v___f_1492_, 0, v_k_1479_);
                crate::leanh::lean_closure_set(v___f_1492_, 1, v___y_1481_);
                crate::leanh::lean_closure_set(v___f_1492_, 2, v___y_1482_);
                crate::leanh::lean_closure_set(v___f_1492_, 3, v___y_1483_);
                crate::leanh::lean_closure_set(v___f_1492_, 4, v___y_1484_);
                crate::leanh::lean_closure_set(v___f_1492_, 5, v___y_1485_);
                crate::leanh::lean_closure_set(v___f_1492_, 6, v___y_1486_);
                v___x_1493_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_1480_,
                    v___f_1492_,
                    v___y_1487_,
                    v___y_1488_,
                    v___y_1489_,
                    v___y_1490_,
                );
                if crate::leanh::lean_obj_tag(v___x_1493_) == 0 {
                    return v___x_1493_;
                } else {
                    v_a_1494_ = crate::leanh::lean_ctor_get(v___x_1493_, 0);
                    v_isSharedCheck_1501_ = (!crate::leanh::lean_is_exclusive(v___x_1493_)) as u8;
                    if v_isSharedCheck_1501_ == 0 {
                        v___x_1496_ = v___x_1493_;
                        v_isShared_1497_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1494_);
                        crate::leanh::lean_dec(v___x_1493_);
                        v___x_1496_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
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
    mut v_k_1502_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
    mut v___y_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
    mut v___y_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1515_: u8 = 0;
    let mut v_res_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1515_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_1503_) as u8);
    v_res_1516_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_1502_, v_allowLevelAssignments_boxed_1515_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
    crate::leanh::lean_dec(v___y_1513_);
    crate::leanh::lean_dec_ref(v___y_1512_);
    crate::leanh::lean_dec(v___y_1511_);
    crate::leanh::lean_dec_ref(v___y_1510_);
    crate::leanh::lean_dec(v___y_1509_);
    crate::leanh::lean_dec_ref(v___y_1508_);
    crate::leanh::lean_dec(v___y_1507_);
    crate::leanh::lean_dec_ref(v___y_1506_);
    crate::leanh::lean_dec(v___y_1505_);
    crate::leanh::lean_dec(v___y_1504_);
    return v_res_1516_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(
    mut v_00_u03b1_1517_: *mut crate::leanh::LeanObject,
    mut v_k_1518_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1519_: u8,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
    mut v___y_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_1518_, v_allowLevelAssignments_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
    return v___x_1531_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(
    mut v_00_u03b1_1532_: *mut crate::leanh::LeanObject,
    mut v_k_1533_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
    mut v___y_1544_: *mut crate::leanh::LeanObject,
    mut v___y_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1546_: u8 = 0;
    let mut v_res_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1546_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_1534_) as u8);
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
    crate::leanh::lean_dec(v___y_1544_);
    crate::leanh::lean_dec_ref(v___y_1543_);
    crate::leanh::lean_dec(v___y_1542_);
    crate::leanh::lean_dec_ref(v___y_1541_);
    crate::leanh::lean_dec(v___y_1540_);
    crate::leanh::lean_dec_ref(v___y_1539_);
    crate::leanh::lean_dec(v___y_1538_);
    crate::leanh::lean_dec_ref(v___y_1537_);
    crate::leanh::lean_dec(v___y_1536_);
    crate::leanh::lean_dec(v___y_1535_);
    return v_res_1547_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(
    mut v_x_1548_: *mut crate::leanh::LeanObject,
    mut v_x_1549_: *mut crate::leanh::LeanObject,
    mut v_x_1550_: *mut crate::leanh::LeanObject,
    mut v_x_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1552_ = crate::leanh::lean_ctor_get(v_x_1548_, 0);
                v_vs_1553_ = crate::leanh::lean_ctor_get(v_x_1548_, 1);
                v_isSharedCheck_1577_ = (!crate::leanh::lean_is_exclusive(v_x_1548_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1555_ = v_x_1548_;
                    v_isShared_1556_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1553_);
                    crate::leanh::lean_inc(v_ks_1552_);
                    crate::leanh::lean_dec(v_x_1548_);
                    v___x_1555_ = crate::leanh::lean_box(0);
                    v_isShared_1556_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1557_ = lean_array_get_size(v_ks_1552_);
                v___x_1558_ = lean_nat_dec_lt(v_x_1549_, v___x_1557_);
                if v___x_1558_ == 0 {
                    crate::leanh::lean_dec(v_x_1549_);
                    v___x_1559_ = lean_array_push(v_ks_1552_, v_x_1550_);
                    v___x_1560_ = lean_array_push(v_vs_1553_, v_x_1551_);
                    if v_isShared_1556_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1555_, 1, v___x_1560_);
                        crate::leanh::lean_ctor_set(v___x_1555_, 0, v___x_1559_);
                        v___x_1562_ = v___x_1555_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1563_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1559_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1560_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_ks_1552_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_vs_1553_);
                            v___x_1567_ = v_reuseFailAlloc_1571_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1572_ = lean_array_fset(v_ks_1552_, v_x_1549_, v_x_1550_);
                        v___x_1573_ = lean_array_fset(v_vs_1553_, v_x_1549_, v_x_1551_);
                        crate::leanh::lean_dec(v_x_1549_);
                        if v_isShared_1556_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1555_, 1, v___x_1573_);
                            crate::leanh::lean_ctor_set(v___x_1555_, 0, v___x_1572_);
                            v___x_1575_ = v___x_1555_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1576_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1572_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
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
                v___x_1568_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1569_ = lean_nat_add(v_x_1549_, v___x_1568_);
                crate::leanh::lean_dec(v_x_1549_);
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
    mut v_n_1578_: *mut crate::leanh::LeanObject,
    mut v_k_1579_: *mut crate::leanh::LeanObject,
    mut v_v_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_1587_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0);
    v___x_1588_ = lean_usize_sub(v___x_1587_, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(
    mut v_x_1590_: *mut crate::leanh::LeanObject,
    mut v_x_1591_: usize,
    mut v_x_1592_: usize,
    mut v_x_1593_: *mut crate::leanh::LeanObject,
    mut v_x_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: usize = 0;
    let mut v___x_1597_: usize = 0;
    let mut v___x_1598_: usize = 0;
    let mut v___x_1599_: usize = 0;
    let mut v_j_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v_v_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_node_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_unused_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1650_: u8 = 0;
    let mut v_ks_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: usize = 0;
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v_reuseFailAlloc_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1590_) == 0 {
                    v_es_1595_ = crate::leanh::lean_ctor_get(v_x_1590_, 0);
                    v___x_1596_ = 5usize;
                    v___x_1597_ = 1usize;
                    v___x_1598_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
                    v___x_1599_ = lean_usize_land(v_x_1591_, v___x_1598_);
                    v_j_1600_ = lean_usize_to_nat(v___x_1599_);
                    v___x_1601_ = lean_array_get_size(v_es_1595_);
                    v___x_1602_ = lean_nat_dec_lt(v_j_1600_, v___x_1601_);
                    if v___x_1602_ == 0 {
                        crate::leanh::lean_dec(v_j_1600_);
                        crate::leanh::lean_dec(v_x_1594_);
                        crate::leanh::lean_dec(v_x_1593_);
                        return v_x_1590_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1595_);
                        v_isSharedCheck_1639_ = (!crate::leanh::lean_is_exclusive(v_x_1590_)) as u8;
                        if v_isSharedCheck_1639_ == 0 {
                            v_unused_1640_ = crate::leanh::lean_ctor_get(v_x_1590_, 0);
                            crate::leanh::lean_dec(v_unused_1640_);
                            v___x_1604_ = v_x_1590_;
                            v_isShared_1605_ = v_isSharedCheck_1639_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1590_);
                            v___x_1604_ = crate::leanh::lean_box(0);
                            v_isShared_1605_ = v_isSharedCheck_1639_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1641_ = crate::leanh::lean_ctor_get(v_x_1590_, 0);
                    v_vs_1642_ = crate::leanh::lean_ctor_get(v_x_1590_, 1);
                    v_isSharedCheck_1662_ = (!crate::leanh::lean_is_exclusive(v_x_1590_)) as u8;
                    if v_isSharedCheck_1662_ == 0 {
                        v___x_1644_ = v_x_1590_;
                        v_isShared_1645_ = v_isSharedCheck_1662_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1642_);
                        crate::leanh::lean_inc(v_ks_1641_);
                        crate::leanh::lean_dec(v_x_1590_);
                        v___x_1644_ = crate::leanh::lean_box(0);
                        v_isShared_1645_ = v_isSharedCheck_1662_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1606_ = lean_array_fget(v_es_1595_, v_j_1600_);
                v___x_1607_ = crate::leanh::lean_box(0);
                v_xs_x27_1608_ = lean_array_fset(v_es_1595_, v_j_1600_, v___x_1607_);
                match crate::leanh::lean_obj_tag(v_v_1606_) {
                    0 => {
                        v_key_1615_ = crate::leanh::lean_ctor_get(v_v_1606_, 0);
                        v_val_1616_ = crate::leanh::lean_ctor_get(v_v_1606_, 1);
                        v_isSharedCheck_1626_ = (!crate::leanh::lean_is_exclusive(v_v_1606_)) as u8;
                        if v_isSharedCheck_1626_ == 0 {
                            v___x_1618_ = v_v_1606_;
                            v_isShared_1619_ = v_isSharedCheck_1626_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1616_);
                            crate::leanh::lean_inc(v_key_1615_);
                            crate::leanh::lean_dec(v_v_1606_);
                            v___x_1618_ = crate::leanh::lean_box(0);
                            v_isShared_1619_ = v_isSharedCheck_1626_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1627_ = crate::leanh::lean_ctor_get(v_v_1606_, 0);
                        v_isSharedCheck_1637_ = (!crate::leanh::lean_is_exclusive(v_v_1606_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1629_ = v_v_1606_;
                            v_isShared_1630_ = v_isSharedCheck_1637_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1627_);
                            crate::leanh::lean_dec(v_v_1606_);
                            v___x_1629_ = crate::leanh::lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1637_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1638_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1638_, 0, v_x_1593_);
                        crate::leanh::lean_ctor_set(v___x_1638_, 1, v_x_1594_);
                        v___y_1610_ = v___x_1638_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1611_ = lean_array_fset(v_xs_x27_1608_, v_j_1600_, v___y_1610_);
                crate::leanh::lean_dec(v_j_1600_);
                if v_isShared_1605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1611_);
                    v___x_1613_ = v___x_1604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
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
                    crate::leanh::lean_del_object(v___x_1618_);
                    v___x_1621_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1615_,
                        v_val_1616_,
                        v_x_1593_,
                        v_x_1594_,
                    );
                    v___x_1622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1622_, 0, v___x_1621_);
                    v___y_1610_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1616_);
                    crate::leanh::lean_dec(v_key_1615_);
                    if v_isShared_1619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1618_, 1, v_x_1594_);
                        crate::leanh::lean_ctor_set(v___x_1618_, 0, v_x_1593_);
                        v___x_1624_ = v___x_1618_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1625_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_x_1593_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_x_1594_);
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
                    crate::leanh::lean_ctor_set(v___x_1629_, 0, v___x_1633_);
                    v___x_1635_ = v___x_1629_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
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
                    v_reuseFailAlloc_1661_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_ks_1641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_vs_1642_);
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
                    v___x_1659_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1660_ = lean_nat_dec_lt(v___x_1658_, v___x_1659_);
                    crate::leanh::lean_dec(v___x_1658_);
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
                    v_ks_1651_ = crate::leanh::lean_ctor_get(v_newNode_1648_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1651_);
                    v_vs_1652_ = crate::leanh::lean_ctor_get(v_newNode_1648_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1652_);
                    crate::leanh::lean_dec_ref(v_newNode_1648_);
                    v___x_1653_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__2);
                    v___x_1655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_x_1592_, v_ks_1651_, v_vs_1652_, v___x_1653_, v___x_1654_);
                    crate::leanh::lean_dec_ref(v_vs_1652_);
                    crate::leanh::lean_dec_ref(v_ks_1651_);
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
    mut v_keys_1664_: *mut crate::leanh::LeanObject,
    mut v_vals_1665_: *mut crate::leanh::LeanObject,
    mut v_i_1666_: *mut crate::leanh::LeanObject,
    mut v_entries_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut v_k_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u64 = 0;
    let mut v_h_1673_: usize = 0;
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: usize = 0;
    let mut v___x_1677_: usize = 0;
    let mut v___x_1678_: usize = 0;
    let mut v_h_1679_: usize = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = lean_array_get_size(v_keys_1664_);
                v___x_1669_ = lean_nat_dec_lt(v_i_1666_, v___x_1668_);
                if v___x_1669_ == 0 {
                    crate::leanh::lean_dec(v_i_1666_);
                    return v_entries_1667_;
                } else {
                    v_k_1670_ = lean_array_fget_borrowed(v_keys_1664_, v_i_1666_);
                    v_v_1671_ = lean_array_fget_borrowed(v_vals_1665_, v_i_1666_);
                    v___x_1672_ = l_Lean_instHashableMVarId_hash(v_k_1670_);
                    v_h_1673_ = lean_uint64_to_usize(v___x_1672_);
                    v___x_1674_ = 5usize;
                    v___x_1675_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1676_ = 1usize;
                    v___x_1677_ = lean_usize_sub(v_depth_1663_, v___x_1676_);
                    v___x_1678_ = lean_usize_mul(v___x_1674_, v___x_1677_);
                    v_h_1679_ = lean_usize_shift_right(v_h_1673_, v___x_1678_);
                    v___x_1680_ = lean_nat_add(v_i_1666_, v___x_1675_);
                    crate::leanh::lean_dec(v_i_1666_);
                    crate::leanh::lean_inc(v_v_1671_);
                    crate::leanh::lean_inc(v_k_1670_);
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
    mut v_depth_1683_: *mut crate::leanh::LeanObject,
    mut v_keys_1684_: *mut crate::leanh::LeanObject,
    mut v_vals_1685_: *mut crate::leanh::LeanObject,
    mut v_i_1686_: *mut crate::leanh::LeanObject,
    mut v_entries_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1688_: usize = 0;
    let mut v_res_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1688_ = crate::leanh::lean_unbox_usize(v_depth_1683_);
    crate::leanh::lean_dec(v_depth_1683_);
    v_res_1689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_boxed_1688_, v_keys_1684_, v_vals_1685_, v_i_1686_, v_entries_1687_);
    crate::leanh::lean_dec_ref(v_vals_1685_);
    crate::leanh::lean_dec_ref(v_keys_1684_);
    return v_res_1689_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_x_1690_: *mut crate::leanh::LeanObject,
    mut v_x_1691_: *mut crate::leanh::LeanObject,
    mut v_x_1692_: *mut crate::leanh::LeanObject,
    mut v_x_1693_: *mut crate::leanh::LeanObject,
    mut v_x_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_215239__boxed_1695_: usize = 0;
    let mut v_x_215240__boxed_1696_: usize = 0;
    let mut v_res_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_215239__boxed_1695_ = crate::leanh::lean_unbox_usize(v_x_1691_);
    crate::leanh::lean_dec(v_x_1691_);
    v_x_215240__boxed_1696_ = crate::leanh::lean_unbox_usize(v_x_1692_);
    crate::leanh::lean_dec(v_x_1692_);
    v_res_1697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1690_, v_x_215239__boxed_1695_, v_x_215240__boxed_1696_, v_x_1693_, v_x_1694_);
    return v_res_1697_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(
    mut v_x_1698_: *mut crate::leanh::LeanObject,
    mut v_x_1699_: *mut crate::leanh::LeanObject,
    mut v_x_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: usize = 0;
    let mut v___x_1703_: usize = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_instHashableMVarId_hash(v_x_1699_);
    v___x_1702_ = lean_uint64_to_usize(v___x_1701_);
    v___x_1703_ = 1usize;
    v___x_1704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1698_, v___x_1702_, v___x_1703_, v_x_1699_, v_x_1700_);
    return v___x_1704_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(
    mut v_mvarId_1705_: *mut crate::leanh::LeanObject,
    mut v_val_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v_depth_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1709_ = lean_st_ref_take(v___y_1707_);
                v_mctx_1710_ = crate::leanh::lean_ctor_get(v___x_1709_, 0);
                v_cache_1711_ = crate::leanh::lean_ctor_get(v___x_1709_, 1);
                v_zetaDeltaFVarIds_1712_ = crate::leanh::lean_ctor_get(v___x_1709_, 2);
                v_postponed_1713_ = crate::leanh::lean_ctor_get(v___x_1709_, 3);
                v_diag_1714_ = crate::leanh::lean_ctor_get(v___x_1709_, 4);
                v_isSharedCheck_1742_ = (!crate::leanh::lean_is_exclusive(v___x_1709_)) as u8;
                if v_isSharedCheck_1742_ == 0 {
                    v___x_1716_ = v___x_1709_;
                    v_isShared_1717_ = v_isSharedCheck_1742_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1714_);
                    crate::leanh::lean_inc(v_postponed_1713_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1712_);
                    crate::leanh::lean_inc(v_cache_1711_);
                    crate::leanh::lean_inc(v_mctx_1710_);
                    crate::leanh::lean_dec(v___x_1709_);
                    v___x_1716_ = crate::leanh::lean_box(0);
                    v_isShared_1717_ = v_isSharedCheck_1742_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1718_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 0);
                v_levelAssignDepth_1719_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 1);
                v_lmvarCounter_1720_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 2);
                v_mvarCounter_1721_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 3);
                v_lDecls_1722_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 4);
                v_decls_1723_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 5);
                v_userNames_1724_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 6);
                v_lAssignment_1725_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 7);
                v_eAssignment_1726_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 8);
                v_dAssignment_1727_ = crate::leanh::lean_ctor_get(v_mctx_1710_, 9);
                v_isSharedCheck_1741_ = (!crate::leanh::lean_is_exclusive(v_mctx_1710_)) as u8;
                if v_isSharedCheck_1741_ == 0 {
                    v___x_1729_ = v_mctx_1710_;
                    v_isShared_1730_ = v_isSharedCheck_1741_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1727_);
                    crate::leanh::lean_inc(v_eAssignment_1726_);
                    crate::leanh::lean_inc(v_lAssignment_1725_);
                    crate::leanh::lean_inc(v_userNames_1724_);
                    crate::leanh::lean_inc(v_decls_1723_);
                    crate::leanh::lean_inc(v_lDecls_1722_);
                    crate::leanh::lean_inc(v_mvarCounter_1721_);
                    crate::leanh::lean_inc(v_lmvarCounter_1720_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1719_);
                    crate::leanh::lean_inc(v_depth_1718_);
                    crate::leanh::lean_dec(v_mctx_1710_);
                    v___x_1729_ = crate::leanh::lean_box(0);
                    v_isShared_1730_ = v_isSharedCheck_1741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1731_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_1726_, v_mvarId_1705_, v_val_1706_);
                if v_isShared_1730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1729_, 8, v___x_1731_);
                    v___x_1733_ = v___x_1729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_depth_1718_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1740_,
                        1,
                        v_levelAssignDepth_1719_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_lmvarCounter_1720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_mvarCounter_1721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_lDecls_1722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_decls_1723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_userNames_1724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_lAssignment_1725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 8, v___x_1731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 9, v_dAssignment_1727_);
                    v___x_1733_ = v_reuseFailAlloc_1740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1716_, 0, v___x_1733_);
                    v___x_1735_ = v___x_1716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_cache_1711_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1739_,
                        2,
                        v_zetaDeltaFVarIds_1712_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_postponed_1713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_diag_1714_);
                    v___x_1735_ = v_reuseFailAlloc_1739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1736_ = lean_st_ref_set(v___y_1707_, v___x_1735_);
                v___x_1737_ = crate::leanh::lean_box(0);
                v___x_1738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1737_);
                return v___x_1738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(
    mut v_mvarId_1743_: *mut crate::leanh::LeanObject,
    mut v_val_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(
            v_mvarId_1743_,
            v_val_1744_,
            v___y_1745_,
        );
    crate::leanh::lean_dec(v___y_1745_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(
    mut v___x_1748_: u8,
    mut v_p_1749_: *mut crate::leanh::LeanObject,
    mut v_e_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_unused_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec_ref(v_p_1749_);
                    v___x_1765_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_1764_, v_e_1750_, v___y_1758_);
                    v_isSharedCheck_1773_ = (!crate::leanh::lean_is_exclusive(v___x_1765_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v_unused_1774_ = crate::leanh::lean_ctor_get(v___x_1765_, 0);
                        crate::leanh::lean_dec(v_unused_1774_);
                        v___x_1767_ = v___x_1765_;
                        v_isShared_1768_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1765_);
                        v___x_1767_ = crate::leanh::lean_box(0);
                        v_isShared_1768_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1769_ = crate::leanh::lean_box((v___x_1748_) as usize);
                if v_isShared_1768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1767_, 0, v___x_1769_);
                    v___x_1771_ = v___x_1767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
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
    mut v___x_1775_: *mut crate::leanh::LeanObject,
    mut v_p_1776_: *mut crate::leanh::LeanObject,
    mut v_e_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_215458__boxed_1789_: u8 = 0;
    let mut v_res_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_215458__boxed_1789_ = (crate::leanh::lean_unbox(v___x_1775_) as u8);
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
    crate::leanh::lean_dec(v___y_1787_);
    crate::leanh::lean_dec_ref(v___y_1786_);
    crate::leanh::lean_dec(v___y_1785_);
    crate::leanh::lean_dec_ref(v___y_1784_);
    crate::leanh::lean_dec(v___y_1783_);
    crate::leanh::lean_dec_ref(v___y_1782_);
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    crate::leanh::lean_dec(v___y_1779_);
    crate::leanh::lean_dec(v___y_1778_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(
    mut v_msgData_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1797_ = lean_st_ref_get(v___y_1795_);
    v_env_1798_ = crate::leanh::lean_ctor_get(v___x_1797_, 0);
    crate::leanh::lean_inc_ref(v_env_1798_);
    crate::leanh::lean_dec(v___x_1797_);
    v___x_1799_ = lean_st_ref_get(v___y_1793_);
    v_mctx_1800_ = crate::leanh::lean_ctor_get(v___x_1799_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1800_);
    crate::leanh::lean_dec(v___x_1799_);
    v_lctx_1801_ = crate::leanh::lean_ctor_get(v___y_1792_, 2);
    v_options_1802_ = crate::leanh::lean_ctor_get(v___y_1794_, 2);
    crate::leanh::lean_inc_ref(v_options_1802_);
    crate::leanh::lean_inc_ref(v_lctx_1801_);
    v___x_1803_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1803_, 0, v_env_1798_);
    crate::leanh::lean_ctor_set(v___x_1803_, 1, v_mctx_1800_);
    crate::leanh::lean_ctor_set(v___x_1803_, 2, v_lctx_1801_);
    crate::leanh::lean_ctor_set(v___x_1803_, 3, v_options_1802_);
    v___x_1804_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 1, v_msgData_1791_);
    v___x_1805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(
    mut v_msgData_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
    crate::leanh::lean_dec(v___y_1810_);
    crate::leanh::lean_dec_ref(v___y_1809_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    return v_res_1812_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0()
-> f64 {
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: f64 = 0.0;
    v___x_1813_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1814_ = lean_float_of_nat(v___x_1813_);
    return v___x_1814_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(
    mut v_cls_1818_: *mut crate::leanh::LeanObject,
    mut v_msg_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v_tid_1844_: u64 = 0;
    let mut v_traces_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: f64 = 0.0;
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1825_ = crate::leanh::lean_ctor_get(v___y_1822_, 5);
                v___x_1826_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
                v_a_1827_ = crate::leanh::lean_ctor_get(v___x_1826_, 0);
                v_isSharedCheck_1871_ = (!crate::leanh::lean_is_exclusive(v___x_1826_)) as u8;
                if v_isSharedCheck_1871_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    v_isShared_1830_ = v_isSharedCheck_1871_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1827_);
                    crate::leanh::lean_dec(v___x_1826_);
                    v___x_1829_ = crate::leanh::lean_box(0);
                    v_isShared_1830_ = v_isSharedCheck_1871_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1831_ = lean_st_ref_take(v___y_1823_);
                v_traceState_1832_ = crate::leanh::lean_ctor_get(v___x_1831_, 4);
                v_env_1833_ = crate::leanh::lean_ctor_get(v___x_1831_, 0);
                v_nextMacroScope_1834_ = crate::leanh::lean_ctor_get(v___x_1831_, 1);
                v_ngen_1835_ = crate::leanh::lean_ctor_get(v___x_1831_, 2);
                v_auxDeclNGen_1836_ = crate::leanh::lean_ctor_get(v___x_1831_, 3);
                v_cache_1837_ = crate::leanh::lean_ctor_get(v___x_1831_, 5);
                v_messages_1838_ = crate::leanh::lean_ctor_get(v___x_1831_, 6);
                v_infoState_1839_ = crate::leanh::lean_ctor_get(v___x_1831_, 7);
                v_snapshotTasks_1840_ = crate::leanh::lean_ctor_get(v___x_1831_, 8);
                v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v___x_1831_)) as u8;
                if v_isSharedCheck_1870_ == 0 {
                    v___x_1842_ = v___x_1831_;
                    v_isShared_1843_ = v_isSharedCheck_1870_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1840_);
                    crate::leanh::lean_inc(v_infoState_1839_);
                    crate::leanh::lean_inc(v_messages_1838_);
                    crate::leanh::lean_inc(v_cache_1837_);
                    crate::leanh::lean_inc(v_traceState_1832_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1836_);
                    crate::leanh::lean_inc(v_ngen_1835_);
                    crate::leanh::lean_inc(v_nextMacroScope_1834_);
                    crate::leanh::lean_inc(v_env_1833_);
                    crate::leanh::lean_dec(v___x_1831_);
                    v___x_1842_ = crate::leanh::lean_box(0);
                    v_isShared_1843_ = v_isSharedCheck_1870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1844_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1832_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1845_ = crate::leanh::lean_ctor_get(v_traceState_1832_, 0);
                v_isSharedCheck_1869_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1832_)) as u8;
                if v_isSharedCheck_1869_ == 0 {
                    v___x_1847_ = v_traceState_1832_;
                    v_isShared_1848_ = v_isSharedCheck_1869_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1845_);
                    crate::leanh::lean_dec(v_traceState_1832_);
                    v___x_1847_ = crate::leanh::lean_box(0);
                    v_isShared_1848_ = v_isSharedCheck_1869_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1849_ = crate::leanh::lean_box(0);
                v___x_1850_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
                v___x_1851_ = 0;
                v___x_1852_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1;
                v___x_1853_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1853_, 0, v_cls_1818_);
                crate::leanh::lean_ctor_set(v___x_1853_, 1, v___x_1849_);
                crate::leanh::lean_ctor_set(v___x_1853_, 2, v___x_1852_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1853_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1850_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1853_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1850_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1853_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1851_,
                );
                v___x_1854_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2;
                v___x_1855_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1855_, 0, v___x_1853_);
                crate::leanh::lean_ctor_set(v___x_1855_, 1, v_a_1827_);
                crate::leanh::lean_ctor_set(v___x_1855_, 2, v___x_1854_);
                crate::leanh::lean_inc(v_ref_1825_);
                v___x_1856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1856_, 0, v_ref_1825_);
                crate::leanh::lean_ctor_set(v___x_1856_, 1, v___x_1855_);
                v___x_1857_ = l_Lean_PersistentArray_push___redArg(v_traces_1845_, v___x_1856_);
                if v_isShared_1848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1847_, 0, v___x_1857_);
                    v___x_1859_ = v___x_1847_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1857_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1868_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1844_,
                    );
                    v___x_1859_ = v_reuseFailAlloc_1868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1842_, 4, v___x_1859_);
                    v___x_1861_ = v___x_1842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_env_1833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 4, v___x_1859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 5, v_cache_1837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_messages_1838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_infoState_1839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_snapshotTasks_1840_);
                    v___x_1861_ = v_reuseFailAlloc_1867_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1862_ = lean_st_ref_set(v___y_1823_, v___x_1861_);
                v___x_1863_ = crate::leanh::lean_box(0);
                if v_isShared_1830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1863_);
                    v___x_1865_ = v___x_1829_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
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
    mut v_cls_1872_: *mut crate::leanh::LeanObject,
    mut v_msg_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1879_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(
        v_cls_1872_,
        v_msg_1873_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
        v___y_1877_,
    );
    crate::leanh::lean_dec(v___y_1877_);
    crate::leanh::lean_dec_ref(v___y_1876_);
    crate::leanh::lean_dec(v___y_1875_);
    crate::leanh::lean_dec_ref(v___y_1874_);
    return v_res_1879_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(
    mut v_keys_1880_: *mut crate::leanh::LeanObject,
    mut v_i_1881_: *mut crate::leanh::LeanObject,
    mut v_k_1882_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: u8 = 0;
    let mut v_k_x27_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = lean_array_get_size(v_keys_1880_);
                v___x_1884_ = lean_nat_dec_lt(v_i_1881_, v___x_1883_);
                if v___x_1884_ == 0 {
                    crate::leanh::lean_dec(v_i_1881_);
                    return v___x_1884_;
                } else {
                    v_k_x27_1885_ = lean_array_fget_borrowed(v_keys_1880_, v_i_1881_);
                    v___x_1886_ = l_Lean_instBEqMVarId_beq(v_k_1882_, v_k_x27_1885_);
                    if v___x_1886_ == 0 {
                        v___x_1887_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1888_ = lean_nat_add(v_i_1881_, v___x_1887_);
                        crate::leanh::lean_dec(v_i_1881_);
                        v_i_1881_ = v___x_1888_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1881_);
                        return v___x_1886_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(
    mut v_keys_1890_: *mut crate::leanh::LeanObject,
    mut v_i_1891_: *mut crate::leanh::LeanObject,
    mut v_k_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1893_: u8 = 0;
    let mut v_r_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1890_, v_i_1891_, v_k_1892_);
    crate::leanh::lean_dec(v_k_1892_);
    crate::leanh::lean_dec_ref(v_keys_1890_);
    v_r_1894_ = crate::leanh::lean_box((v_res_1893_) as usize);
    return v_r_1894_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(
    mut v_x_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: usize,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v_j_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: u8 = 0;
    let mut v_node_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: usize = 0;
    let mut v___x_1910_: u8 = 0;
    let mut v_ks_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1895_) == 0 {
                    v_es_1898_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
                    v___x_1899_ = crate::leanh::lean_box(2);
                    v___x_1900_ = 5usize;
                    v___x_1901_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__1);
                    v___x_1902_ = lean_usize_land(v_x_1896_, v___x_1901_);
                    v_j_1903_ = lean_usize_to_nat(v___x_1902_);
                    v___x_1904_ = lean_array_get_borrowed(v___x_1899_, v_es_1898_, v_j_1903_);
                    crate::leanh::lean_dec(v_j_1903_);
                    match crate::leanh::lean_obj_tag(v___x_1904_) {
                        0 => {
                            v_key_1905_ = crate::leanh::lean_ctor_get(v___x_1904_, 0);
                            v___x_1906_ = l_Lean_instBEqMVarId_beq(v_x_1897_, v_key_1905_);
                            return v___x_1906_;
                        }
                        1 => {
                            v_node_1907_ = crate::leanh::lean_ctor_get(v___x_1904_, 0);
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
                    v_ks_1911_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
                    v___x_1912_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1913_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_1911_, v___x_1912_, v_x_1897_);
                    return v___x_1913_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_x_1914_: *mut crate::leanh::LeanObject,
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_215667__boxed_1917_: usize = 0;
    let mut v_res_1918_: u8 = 0;
    let mut v_r_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_215667__boxed_1917_ = crate::leanh::lean_unbox_usize(v_x_1915_);
    crate::leanh::lean_dec(v_x_1915_);
    v_res_1918_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1914_, v_x_215667__boxed_1917_, v_x_1916_);
    crate::leanh::lean_dec(v_x_1916_);
    crate::leanh::lean_dec_ref(v_x_1914_);
    v_r_1919_ = crate::leanh::lean_box((v_res_1918_) as usize);
    return v_r_1919_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(
    mut v_x_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
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
    mut v_x_1925_: *mut crate::leanh::LeanObject,
    mut v_x_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1927_: u8 = 0;
    let mut v_r_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1925_, v_x_1926_);
    crate::leanh::lean_dec(v_x_1926_);
    crate::leanh::lean_dec_ref(v_x_1925_);
    v_r_1928_ = crate::leanh::lean_box((v_res_1927_) as usize);
    return v_r_1928_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(
    mut v_mvarId_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = lean_st_ref_get(v___y_1930_);
    v_mctx_1933_ = crate::leanh::lean_ctor_get(v___x_1932_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1933_);
    crate::leanh::lean_dec(v___x_1932_);
    v_eAssignment_1934_ = crate::leanh::lean_ctor_get(v_mctx_1933_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_1934_);
    crate::leanh::lean_dec_ref(v_mctx_1933_);
    v___x_1935_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_1934_, v_mvarId_1929_);
    crate::leanh::lean_dec_ref(v_eAssignment_1934_);
    v___x_1936_ = crate::leanh::lean_box((v___x_1935_) as usize);
    v___x_1937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(
    mut v_mvarId_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1941_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(
            v_mvarId_1938_,
            v___y_1939_,
        );
    crate::leanh::lean_dec(v___y_1939_);
    crate::leanh::lean_dec(v_mvarId_1938_);
    return v_res_1941_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(
    mut v_as_1942_: *mut crate::leanh::LeanObject,
    mut v_i_1943_: usize,
    mut v_stop_1944_: usize,
    mut v_b_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v_a_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v_a_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = lean_usize_dec_eq(v_i_1943_, v_stop_1944_);
                if v___x_1962_ == 0 {
                    v___x_1963_ = lean_array_uget_borrowed(v_as_1942_, v_i_1943_);
                    v___x_1966_ = l_Lean_Expr_mvarId_x21(v___x_1963_);
                    v___x_1967_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_1966_, v___y_1953_);
                    crate::leanh::lean_dec(v___x_1966_);
                    if crate::leanh::lean_obj_tag(v___x_1967_) == 0 {
                        v_a_1968_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                        crate::leanh::lean_inc(v_a_1968_);
                        crate::leanh::lean_dec_ref_known(v___x_1967_, 1);
                        v___x_1969_ = (crate::leanh::lean_unbox(v_a_1968_) as u8);
                        crate::leanh::lean_dec(v_a_1968_);
                        if v___x_1969_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1958_ = v_b_1945_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1967_) == 0 {
                            v_a_1970_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                            crate::leanh::lean_inc(v_a_1970_);
                            crate::leanh::lean_dec_ref_known(v___x_1967_, 1);
                            v___x_1971_ = (crate::leanh::lean_unbox(v_a_1970_) as u8);
                            crate::leanh::lean_dec(v_a_1970_);
                            if v___x_1971_ == 0 {
                                v_a_1958_ = v_b_1945_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_1945_);
                            v_a_1972_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_1979_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_1979_ == 0 {
                                v___x_1974_ = v___x_1967_;
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1972_);
                                crate::leanh::lean_dec(v___x_1967_);
                                v___x_1974_ = crate::leanh::lean_box(0);
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1980_, 0, v_b_1945_);
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
                crate::leanh::lean_inc(v___x_1963_);
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
                    v_reuseFailAlloc_1978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
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
    mut v_as_1981_: *mut crate::leanh::LeanObject,
    mut v_i_1982_: *mut crate::leanh::LeanObject,
    mut v_stop_1983_: *mut crate::leanh::LeanObject,
    mut v_b_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1996_: usize = 0;
    let mut v_stop_boxed_1997_: usize = 0;
    let mut v_res_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1996_ = crate::leanh::lean_unbox_usize(v_i_1982_);
    crate::leanh::lean_dec(v_i_1982_);
    v_stop_boxed_1997_ = crate::leanh::lean_unbox_usize(v_stop_1983_);
    crate::leanh::lean_dec(v_stop_1983_);
    v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_1981_, v_i_boxed_1996_, v_stop_boxed_1997_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    crate::leanh::lean_dec(v___y_1992_);
    crate::leanh::lean_dec_ref(v___y_1991_);
    crate::leanh::lean_dec(v___y_1990_);
    crate::leanh::lean_dec_ref(v___y_1989_);
    crate::leanh::lean_dec(v___y_1988_);
    crate::leanh::lean_dec_ref(v___y_1987_);
    crate::leanh::lean_dec(v___y_1986_);
    crate::leanh::lean_dec(v___y_1985_);
    crate::leanh::lean_dec_ref(v_as_1981_);
    return v_res_1998_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1;
    v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
    return v___x_2003_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3;
    v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
    return v___x_2006_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(
    mut v___x_2007_: *mut crate::leanh::LeanObject,
    mut v_e_2008_: *mut crate::leanh::LeanObject,
    mut v_as_2009_: *mut crate::leanh::LeanObject,
    mut v_sz_2010_: usize,
    mut v_i_2011_: usize,
    mut v_b_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
    mut v___y_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: usize = 0;
    let mut v___x_2027_: usize = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v_array_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v_a_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_a_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_a_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2119_: u8 = 0;
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut v_reuseFailAlloc_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_a_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut v_unused_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v_unused_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2029_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
                if v___x_2029_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2008_);
                    crate::leanh::lean_dec(v___x_2007_);
                    v___x_2030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2030_, 0, v_b_2012_);
                    return v___x_2030_;
                } else {
                    v_snd_2031_ = crate::leanh::lean_ctor_get(v_b_2012_, 1);
                    v_isSharedCheck_2137_ = (!crate::leanh::lean_is_exclusive(v_b_2012_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v_unused_2138_ = crate::leanh::lean_ctor_get(v_b_2012_, 0);
                        crate::leanh::lean_dec(v_unused_2138_);
                        v___x_2033_ = v_b_2012_;
                        v_isShared_2034_ = v_isSharedCheck_2137_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2031_);
                        crate::leanh::lean_dec(v_b_2012_);
                        v___x_2033_ = crate::leanh::lean_box(0);
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
                v_array_2035_ = crate::leanh::lean_ctor_get(v_snd_2031_, 0);
                v_start_2036_ = crate::leanh::lean_ctor_get(v_snd_2031_, 1);
                v_stop_2037_ = crate::leanh::lean_ctor_get(v_snd_2031_, 2);
                v___x_2038_ = crate::leanh::lean_box(0);
                v___x_2039_ = lean_nat_dec_lt(v_start_2036_, v_stop_2037_);
                if v___x_2039_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2008_);
                    crate::leanh::lean_dec(v___x_2007_);
                    if v_isShared_2034_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2038_);
                        v___x_2041_ = v___x_2033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2038_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_snd_2031_);
                        v___x_2041_ = v_reuseFailAlloc_2043_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_2037_);
                    crate::leanh::lean_inc(v_start_2036_);
                    crate::leanh::lean_inc_ref(v_array_2035_);
                    v_isSharedCheck_2133_ = (!crate::leanh::lean_is_exclusive(v_snd_2031_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v_unused_2134_ = crate::leanh::lean_ctor_get(v_snd_2031_, 2);
                        crate::leanh::lean_dec(v_unused_2134_);
                        v_unused_2135_ = crate::leanh::lean_ctor_get(v_snd_2031_, 1);
                        crate::leanh::lean_dec(v_unused_2135_);
                        v_unused_2136_ = crate::leanh::lean_ctor_get(v_snd_2031_, 0);
                        crate::leanh::lean_dec(v_unused_2136_);
                        v___x_2045_ = v_snd_2031_;
                        v_isShared_2046_ = v_isSharedCheck_2133_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2031_);
                        v___x_2045_ = crate::leanh::lean_box(0);
                        v_isShared_2046_ = v_isSharedCheck_2133_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2042_, 0, v___x_2041_);
                return v___x_2042_;
            }
            4 => {
                v_a_2047_ = lean_array_uget_borrowed(v_as_2009_, v_i_2011_);
                v___x_2048_ = l_Lean_Expr_mvarId_x21(v_a_2047_);
                v___x_2049_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_2048_, v___y_2020_);
                crate::leanh::lean_dec(v___x_2048_);
                if crate::leanh::lean_obj_tag(v___x_2049_) == 0 {
                    v_a_2050_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                    v_isSharedCheck_2124_ = (!crate::leanh::lean_is_exclusive(v___x_2049_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2052_ = v___x_2049_;
                        v_isShared_2053_ = v_isSharedCheck_2124_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2050_);
                        crate::leanh::lean_dec(v___x_2049_);
                        v___x_2052_ = crate::leanh::lean_box(0);
                        v_isShared_2053_ = v_isSharedCheck_2124_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2045_);
                    crate::leanh::lean_dec(v_stop_2037_);
                    crate::leanh::lean_dec(v_start_2036_);
                    crate::leanh::lean_dec_ref(v_array_2035_);
                    crate::leanh::lean_del_object(v___x_2033_);
                    crate::leanh::lean_dec_ref(v_e_2008_);
                    crate::leanh::lean_dec(v___x_2007_);
                    v_a_2125_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                    v_isSharedCheck_2132_ = (!crate::leanh::lean_is_exclusive(v___x_2049_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v___x_2127_ = v___x_2049_;
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2125_);
                        crate::leanh::lean_dec(v___x_2049_);
                        v___x_2127_ = crate::leanh::lean_box(0);
                        v_isShared_2128_ = v_isSharedCheck_2132_;
                        state = 20;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2054_ = lean_array_fget(v_array_2035_, v_start_2036_);
                v___x_2055_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2056_ = lean_nat_add(v_start_2036_, v___x_2055_);
                crate::leanh::lean_dec(v_start_2036_);
                if v_isShared_2046_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2045_, 1, v___x_2056_);
                    v___x_2058_ = v___x_2045_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_array_2035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_stop_2037_);
                    v___x_2058_ = v_reuseFailAlloc_2123_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2120_ = (crate::leanh::lean_unbox(v___x_2054_) as u8);
                crate::leanh::lean_dec(v___x_2054_);
                v___x_2121_ = l_Lean_BinderInfo_isInstImplicit(v___x_2120_);
                if v___x_2121_ == 0 {
                    crate::leanh::lean_dec(v_a_2050_);
                    v___y_2070_ = v___x_2121_;
                    state = 11;
                    continue;
                } else {
                    v___x_2122_ = (crate::leanh::lean_unbox(v_a_2050_) as u8);
                    crate::leanh::lean_dec(v_a_2050_);
                    if v___x_2122_ == 0 {
                        v___y_2070_ = v___x_2121_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2052_);
                        crate::leanh::lean_del_object(v___x_2033_);
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0;
                if v_isShared_2034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2033_, 1, v___x_2058_);
                    crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2060_);
                    v___x_2062_ = v___x_2033_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2058_);
                    v___x_2062_ = v_reuseFailAlloc_2066_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2062_);
                    v___x_2064_ = v___x_2052_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2064_;
            }
            10 => {
                v___x_2068_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2068_, 0, v___x_2038_);
                crate::leanh::lean_ctor_set(v___x_2068_, 1, v___x_2058_);
                v_a_2025_ = v___x_2068_;
                state = 1;
                continue;
            }
            11 => {
                if v___y_2070_ == 0 {
                    crate::leanh::lean_del_object(v___x_2052_);
                    crate::leanh::lean_del_object(v___x_2033_);
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___y_2022_);
                    crate::leanh::lean_inc_ref(v___y_2021_);
                    crate::leanh::lean_inc(v___y_2020_);
                    crate::leanh::lean_inc_ref(v___y_2019_);
                    crate::leanh::lean_inc(v_a_2047_);
                    v___x_2071_ = lean_infer_type(
                        v_a_2047_,
                        v___y_2019_,
                        v___y_2020_,
                        v___y_2021_,
                        v___y_2022_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2071_) == 0 {
                        v_a_2072_ = crate::leanh::lean_ctor_get(v___x_2071_, 0);
                        crate::leanh::lean_inc(v_a_2072_);
                        crate::leanh::lean_dec_ref_known(v___x_2071_, 1);
                        crate::leanh::lean_inc(v_a_2047_);
                        v___x_2073_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(
                            v_a_2047_,
                            v_a_2072_,
                            v___y_2019_,
                            v___y_2020_,
                            v___y_2021_,
                            v___y_2022_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2073_) == 0 {
                            v_a_2074_ = crate::leanh::lean_ctor_get(v___x_2073_, 0);
                            crate::leanh::lean_inc(v_a_2074_);
                            crate::leanh::lean_dec_ref_known(v___x_2073_, 1);
                            v___x_2075_ = (crate::leanh::lean_unbox(v_a_2074_) as u8);
                            crate::leanh::lean_dec(v_a_2074_);
                            if v___x_2075_ == 0 {
                                v___x_2076_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_2017_);
                                if crate::leanh::lean_obj_tag(v___x_2076_) == 0 {
                                    v_a_2077_ = crate::leanh::lean_ctor_get(v___x_2076_, 0);
                                    crate::leanh::lean_inc(v_a_2077_);
                                    crate::leanh::lean_dec_ref_known(v___x_2076_, 1);
                                    v___x_2078_ = (crate::leanh::lean_unbox(v_a_2077_) as u8);
                                    crate::leanh::lean_dec(v_a_2077_);
                                    if v___x_2078_ == 0 {
                                        crate::leanh::lean_dec_ref(v_e_2008_);
                                        crate::leanh::lean_dec(v___x_2007_);
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_2079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
                                        v___x_2080_ = l_Lean_MessageData_ofName(v___x_2007_);
                                        v___x_2081_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2081_, 0, v___x_2079_);
                                        crate::leanh::lean_ctor_set(v___x_2081_, 1, v___x_2080_);
                                        v___x_2082_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
                                        v___x_2083_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2083_, 0, v___x_2081_);
                                        crate::leanh::lean_ctor_set(v___x_2083_, 1, v___x_2082_);
                                        v___x_2084_ = l_Lean_indentExpr(v_e_2008_);
                                        v___x_2085_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2083_);
                                        crate::leanh::lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                                        v___x_2086_ = l_Lean_Meta_Sym_reportIssue(
                                            v___x_2085_,
                                            v___y_2017_,
                                            v___y_2018_,
                                            v___y_2019_,
                                            v___y_2020_,
                                            v___y_2021_,
                                            v___y_2022_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2086_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_2086_, 1);
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2058_);
                                            crate::leanh::lean_del_object(v___x_2052_);
                                            crate::leanh::lean_del_object(v___x_2033_);
                                            v_a_2087_ = crate::leanh::lean_ctor_get(v___x_2086_, 0);
                                            v_isSharedCheck_2094_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2086_))
                                                    as u8;
                                            if v_isSharedCheck_2094_ == 0 {
                                                v___x_2089_ = v___x_2086_;
                                                v_isShared_2090_ = v_isSharedCheck_2094_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2087_);
                                                crate::leanh::lean_dec(v___x_2086_);
                                                v___x_2089_ = crate::leanh::lean_box(0);
                                                v_isShared_2090_ = v_isSharedCheck_2094_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2058_);
                                    crate::leanh::lean_del_object(v___x_2052_);
                                    crate::leanh::lean_del_object(v___x_2033_);
                                    crate::leanh::lean_dec_ref(v_e_2008_);
                                    crate::leanh::lean_dec(v___x_2007_);
                                    v_a_2095_ = crate::leanh::lean_ctor_get(v___x_2076_, 0);
                                    v_isSharedCheck_2102_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2076_)) as u8;
                                    if v_isSharedCheck_2102_ == 0 {
                                        v___x_2097_ = v___x_2076_;
                                        v_isShared_2098_ = v_isSharedCheck_2102_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2095_);
                                        crate::leanh::lean_dec(v___x_2076_);
                                        v___x_2097_ = crate::leanh::lean_box(0);
                                        v_isShared_2098_ = v_isSharedCheck_2102_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2052_);
                                crate::leanh::lean_del_object(v___x_2033_);
                                v___x_2103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2038_);
                                crate::leanh::lean_ctor_set(v___x_2103_, 1, v___x_2058_);
                                v_a_2025_ = v___x_2103_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2058_);
                            crate::leanh::lean_del_object(v___x_2052_);
                            crate::leanh::lean_del_object(v___x_2033_);
                            crate::leanh::lean_dec_ref(v_e_2008_);
                            crate::leanh::lean_dec(v___x_2007_);
                            v_a_2104_ = crate::leanh::lean_ctor_get(v___x_2073_, 0);
                            v_isSharedCheck_2111_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2073_)) as u8;
                            if v_isSharedCheck_2111_ == 0 {
                                v___x_2106_ = v___x_2073_;
                                v_isShared_2107_ = v_isSharedCheck_2111_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2104_);
                                crate::leanh::lean_dec(v___x_2073_);
                                v___x_2106_ = crate::leanh::lean_box(0);
                                v_isShared_2107_ = v_isSharedCheck_2111_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2058_);
                        crate::leanh::lean_del_object(v___x_2052_);
                        crate::leanh::lean_del_object(v___x_2033_);
                        crate::leanh::lean_dec_ref(v_e_2008_);
                        crate::leanh::lean_dec(v___x_2007_);
                        v_a_2112_ = crate::leanh::lean_ctor_get(v___x_2071_, 0);
                        v_isSharedCheck_2119_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2071_)) as u8;
                        if v_isSharedCheck_2119_ == 0 {
                            v___x_2114_ = v___x_2071_;
                            v_isShared_2115_ = v_isSharedCheck_2119_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2112_);
                            crate::leanh::lean_dec(v___x_2071_);
                            v___x_2114_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
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
                    v_reuseFailAlloc_2101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
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
                    v_reuseFailAlloc_2110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
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
                    v_reuseFailAlloc_2118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
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
                    v_reuseFailAlloc_2131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_e_2140_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_2141_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_2142_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_2143_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_2144_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2145_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2146_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2147_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2148_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2149_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2150_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2151_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2152_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2153_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2154_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2155_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_2156_: usize = 0;
    let mut v_i_boxed_2157_: usize = 0;
    let mut v_res_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2156_ = crate::leanh::lean_unbox_usize(v_sz_2142_);
    crate::leanh::lean_dec(v_sz_2142_);
    v_i_boxed_2157_ = crate::leanh::lean_unbox_usize(v_i_2143_);
    crate::leanh::lean_dec(v_i_2143_);
    v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_2139_, v_e_2140_, v_as_2141_, v_sz_boxed_2156_, v_i_boxed_2157_, v_b_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
    crate::leanh::lean_dec(v___y_2154_);
    crate::leanh::lean_dec_ref(v___y_2153_);
    crate::leanh::lean_dec(v___y_2152_);
    crate::leanh::lean_dec_ref(v___y_2151_);
    crate::leanh::lean_dec(v___y_2150_);
    crate::leanh::lean_dec_ref(v___y_2149_);
    crate::leanh::lean_dec(v___y_2148_);
    crate::leanh::lean_dec_ref(v___y_2147_);
    crate::leanh::lean_dec(v___y_2146_);
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v_as_2141_);
    return v_res_2158_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2170_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4;
    v___x_2171_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6;
    v___x_2172_ = l_Lean_Name_append(v___x_2171_, v___x_2170_);
    return v___x_2172_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2174_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8;
    v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
    return v___x_2175_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10;
    v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12;
    v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14;
    v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
    return v___x_2184_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_2199_: *mut crate::leanh::LeanObject,
    mut v_thm_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v_arg_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v_arg_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v_arg_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v_declName_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v___y_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: u8 = 0;
    let mut v_options_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2282_: u8 = 0;
    let mut v_inheritedTraceOptions_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v___y_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2316_: u8 = 0;
    let mut v_a_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: u8 = 0;
    let mut v_a_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut v_a_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2339_: u8 = 0;
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v___y_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: u8 = 0;
    let mut v___y_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2356_: u8 = 0;
    let mut v___y_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: u8 = 0;
    let mut v___y_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2397_: usize = 0;
    let mut v___x_2398_: usize = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v_fst_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u8 = 0;
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: usize = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: usize = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut v_val_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_a_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut v_a_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2454_: u8 = 0;
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: u8 = 0;
    let mut v_arg_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: u8 = 0;
    let mut v_arg_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v_arg_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v_trackZetaDelta_2515_: u8 = 0;
    let mut v_zetaDeltaSet_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2522_: u8 = 0;
    let mut v_inTypeClassResolution_2523_: u8 = 0;
    let mut v_cacheInferType_2524_: u8 = 0;
    let mut v___x_2525_: u8 = 0;
    let mut v_config_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u64 = 0;
    let mut v___x_2529_: u64 = 0;
    let mut v___x_2530_: u64 = 0;
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: u64 = 0;
    let mut v___x_2534_: u64 = 0;
    let mut v_key_2535_: u64 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2544_: u8 = 0;
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v_reuseFailAlloc_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_a_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_a_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2224_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_2199_, v___y_2201_);
                if crate::leanh::lean_obj_tag(v___x_2224_) == 0 {
                    v_a_2225_ = crate::leanh::lean_ctor_get(v___x_2224_, 0);
                    crate::leanh::lean_inc(v_a_2225_);
                    crate::leanh::lean_dec_ref_known(v___x_2224_, 1);
                    v___x_2226_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_2203_);
                    if crate::leanh::lean_obj_tag(v___x_2226_) == 0 {
                        v_a_2227_ = crate::leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2567_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2567_ == 0 {
                            v___x_2229_ = v___x_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2567_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2227_);
                            crate::leanh::lean_dec(v___x_2226_);
                            v___x_2229_ = crate::leanh::lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2567_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2225_);
                        crate::leanh::lean_dec_ref(v_thm_2200_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        v_a_2568_ = crate::leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2575_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2575_ == 0 {
                            v___x_2570_ = v___x_2226_;
                            v_isShared_2571_ = v_isSharedCheck_2575_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2568_);
                            crate::leanh::lean_dec(v___x_2226_);
                            v___x_2570_ = crate::leanh::lean_box(0);
                            v_isShared_2571_ = v_isSharedCheck_2575_;
                            state = 46;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_thm_2200_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v_a_2576_ = crate::leanh::lean_ctor_get(v___x_2224_, 0);
                    v_isSharedCheck_2583_ = (!crate::leanh::lean_is_exclusive(v___x_2224_)) as u8;
                    if v_isSharedCheck_2583_ == 0 {
                        v___x_2578_ = v___x_2224_;
                        v_isShared_2579_ = v_isSharedCheck_2583_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2576_);
                        crate::leanh::lean_dec(v___x_2224_);
                        v___x_2578_ = crate::leanh::lean_box(0);
                        v_isShared_2579_ = v_isSharedCheck_2583_;
                        state = 48;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2213_ = crate::leanh::lean_box(0);
                v___x_2214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2214_, 0, v___x_2213_);
                return v___x_2214_;
            }
            2 => {
                v___x_2216_ = crate::leanh::lean_box(0);
                v___x_2217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2217_, 0, v___x_2216_);
                return v___x_2217_;
            }
            3 => {
                v___x_2219_ = crate::leanh::lean_box(0);
                v___x_2220_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
                return v___x_2220_;
            }
            4 => {
                v___x_2222_ = crate::leanh::lean_box(0);
                v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2223_, 0, v___x_2222_);
                return v___x_2223_;
            }
            5 => {
                v___x_2231_ = lean_nat_dec_lt(v_a_2225_, v_a_2227_);
                crate::leanh::lean_dec(v_a_2227_);
                crate::leanh::lean_dec(v_a_2225_);
                if v___x_2231_ == 0 {
                    crate::leanh::lean_dec_ref(v_thm_2200_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v___x_2232_ = crate::leanh::lean_box(0);
                    if v_isShared_2230_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2232_);
                        v___x_2234_ = v___x_2229_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
                        v___x_2234_ = v_reuseFailAlloc_2235_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2229_);
                    crate::leanh::lean_inc_ref(v_e_2199_);
                    v___x_2236_ = l_Lean_Expr_cleanupAnnotations(v_e_2199_);
                    v___x_2237_ = l_Lean_Expr_isApp(v___x_2236_);
                    if v___x_2237_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2236_);
                        crate::leanh::lean_dec_ref(v_thm_2200_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        state = 4;
                        continue;
                    } else {
                        v_arg_2238_ = crate::leanh::lean_ctor_get(v___x_2236_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2238_);
                        v___x_2239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2236_);
                        v___x_2240_ = l_Lean_Expr_isApp(v___x_2239_);
                        if v___x_2240_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2239_);
                            crate::leanh::lean_dec_ref(v_arg_2238_);
                            crate::leanh::lean_dec_ref(v_thm_2200_);
                            crate::leanh::lean_dec_ref(v_e_2199_);
                            state = 4;
                            continue;
                        } else {
                            v_arg_2241_ = crate::leanh::lean_ctor_get(v___x_2239_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2241_);
                            v___x_2242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2239_);
                            v___x_2243_ = l_Lean_Expr_isApp(v___x_2242_);
                            if v___x_2243_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2242_);
                                crate::leanh::lean_dec_ref(v_arg_2241_);
                                crate::leanh::lean_dec_ref(v_arg_2238_);
                                crate::leanh::lean_dec_ref(v_thm_2200_);
                                crate::leanh::lean_dec_ref(v_e_2199_);
                                state = 4;
                                continue;
                            } else {
                                v_arg_2244_ = crate::leanh::lean_ctor_get(v___x_2242_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2244_);
                                v___x_2245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2242_);
                                v___x_2246_ =
                                    l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1;
                                v___x_2247_ = l_Lean_Expr_isConstOf(v___x_2245_, v___x_2246_);
                                crate::leanh::lean_dec_ref(v___x_2245_);
                                if v___x_2247_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_2244_);
                                    crate::leanh::lean_dec_ref(v_arg_2241_);
                                    crate::leanh::lean_dec_ref(v_arg_2238_);
                                    crate::leanh::lean_dec_ref(v_thm_2200_);
                                    crate::leanh::lean_dec_ref(v_e_2199_);
                                    state = 4;
                                    continue;
                                } else {
                                    v_declName_2248_ = crate::leanh::lean_ctor_get(v_thm_2200_, 0);
                                    crate::leanh::lean_inc_n(v_declName_2248_, 2);
                                    crate::leanh::lean_dec_ref(v_thm_2200_);
                                    v___x_2382_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                                        v_declName_2248_,
                                        v___y_2207_,
                                        v___y_2208_,
                                        v___y_2209_,
                                        v___y_2210_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2382_) == 0 {
                                        v_a_2383_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                                        crate::leanh::lean_inc_n(v_a_2383_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_2382_, 1);
                                        crate::leanh::lean_inc(v___y_2210_);
                                        crate::leanh::lean_inc_ref(v___y_2209_);
                                        crate::leanh::lean_inc(v___y_2208_);
                                        crate::leanh::lean_inc_ref(v___y_2207_);
                                        v___x_2491_ = lean_infer_type(
                                            v_a_2383_,
                                            v___y_2207_,
                                            v___y_2208_,
                                            v___y_2209_,
                                            v___y_2210_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2491_) == 0 {
                                            v_a_2492_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                                            crate::leanh::lean_inc(v_a_2492_);
                                            crate::leanh::lean_dec_ref_known(v___x_2491_, 1);
                                            v___x_2493_ = l_Lean_Meta_Context_config(v___y_2207_);
                                            v_foApprox_2494_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                0 as u32,
                                            );
                                            v_ctxApprox_2495_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                1 as u32,
                                            );
                                            v_quasiPatternApprox_2496_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    2 as u32,
                                                );
                                            v_constApprox_2497_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                3 as u32,
                                            );
                                            v_isDefEqStuckEx_2498_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    4 as u32,
                                                );
                                            v_unificationHints_2499_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    5 as u32,
                                                );
                                            v_proofIrrelevance_2500_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    6 as u32,
                                                );
                                            v_assignSyntheticOpaque_2501_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    7 as u32,
                                                );
                                            v_offsetCnstrs_2502_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v___x_2493_,
                                                    8 as u32,
                                                );
                                            v_etaStruct_2503_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                10 as u32,
                                            );
                                            v_univApprox_2504_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                11 as u32,
                                            );
                                            v_iota_2505_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                12 as u32,
                                            );
                                            v_beta_2506_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                13 as u32,
                                            );
                                            v_proj_2507_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                14 as u32,
                                            );
                                            v_zeta_2508_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                15 as u32,
                                            );
                                            v_zetaDelta_2509_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                16 as u32,
                                            );
                                            v_zetaUnused_2510_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                17 as u32,
                                            );
                                            v_zetaHave_2511_ = crate::leanh::lean_ctor_get_uint8(
                                                v___x_2493_,
                                                18 as u32,
                                            );
                                            v_isSharedCheck_2550_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2493_))
                                                    as u8;
                                            if v_isSharedCheck_2550_ == 0 {
                                                v___x_2513_ = v___x_2493_;
                                                v_isShared_2514_ = v_isSharedCheck_2550_;
                                                state = 38;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_2493_);
                                                v___x_2513_ = crate::leanh::lean_box(0);
                                                v_isShared_2514_ = v_isSharedCheck_2550_;
                                                state = 38;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_2383_);
                                            crate::leanh::lean_dec(v_declName_2248_);
                                            crate::leanh::lean_dec_ref(v_arg_2244_);
                                            crate::leanh::lean_dec_ref(v_arg_2241_);
                                            crate::leanh::lean_dec_ref(v_arg_2238_);
                                            crate::leanh::lean_dec_ref(v_e_2199_);
                                            v_a_2551_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                                            v_isSharedCheck_2558_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2491_))
                                                    as u8;
                                            if v_isSharedCheck_2558_ == 0 {
                                                v___x_2553_ = v___x_2491_;
                                                v_isShared_2554_ = v_isSharedCheck_2558_;
                                                state = 42;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2551_);
                                                crate::leanh::lean_dec(v___x_2491_);
                                                v___x_2553_ = crate::leanh::lean_box(0);
                                                v_isShared_2554_ = v_isSharedCheck_2558_;
                                                state = 42;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_declName_2248_);
                                        crate::leanh::lean_dec_ref(v_arg_2244_);
                                        crate::leanh::lean_dec_ref(v_arg_2241_);
                                        crate::leanh::lean_dec_ref(v_arg_2238_);
                                        crate::leanh::lean_dec_ref(v_e_2199_);
                                        v_a_2559_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                                        v_isSharedCheck_2566_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                                        if v_isSharedCheck_2566_ == 0 {
                                            v___x_2561_ = v___x_2382_;
                                            v_isShared_2562_ = v_isSharedCheck_2566_;
                                            state = 44;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2559_);
                                            crate::leanh::lean_dec(v___x_2382_);
                                            v___x_2561_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v_e_2199_);
                if crate::leanh::lean_obj_tag(v___x_2262_) == 0 {
                    v_a_2263_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                    crate::leanh::lean_inc(v_a_2263_);
                    crate::leanh::lean_dec_ref_known(v___x_2262_, 1);
                    v___x_2264_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2265_ = lean_nat_add(v_a_2263_, v___x_2264_);
                    crate::leanh::lean_dec(v_a_2263_);
                    v___x_2266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2266_, 0, v_declName_2248_);
                    v___x_2267_ = crate::leanh::lean_box(1);
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
                    crate::leanh::lean_dec_ref(v___y_2251_);
                    crate::leanh::lean_dec_ref(v___y_2250_);
                    crate::leanh::lean_dec(v_declName_2248_);
                    v_a_2269_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                    v_isSharedCheck_2276_ = (!crate::leanh::lean_is_exclusive(v___x_2262_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v___x_2271_ = v___x_2262_;
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2269_);
                        crate::leanh::lean_dec(v___x_2262_);
                        v___x_2271_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
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
                    v_options_2281_ = crate::leanh::lean_ctor_get(v___y_2209_, 2);
                    v_hasTrace_2282_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2281_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                            crate::leanh::lean_ctor_get(v___y_2209_, 13);
                        v___x_2284_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4;
                        v___x_2285_ = crate::leanh::lean_obj_once(
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
                            crate::leanh::lean_inc(v_declName_2248_);
                            v___x_2287_ = l_Lean_MessageData_ofName(v_declName_2248_);
                            v___x_2288_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
                            v___x_2289_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2287_);
                            crate::leanh::lean_ctor_set(v___x_2289_, 1, v___x_2288_);
                            crate::leanh::lean_inc_ref(v___y_2279_);
                            v___x_2290_ = l_Lean_MessageData_ofExpr(v___y_2279_);
                            v___x_2291_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2291_, 0, v___x_2289_);
                            crate::leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
                            v___x_2292_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_2284_, v___x_2291_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                            if crate::leanh::lean_obj_tag(v___x_2292_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2292_, 1);
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
                                crate::leanh::lean_dec_ref(v___y_2279_);
                                crate::leanh::lean_dec_ref(v___y_2278_);
                                crate::leanh::lean_dec(v_declName_2248_);
                                crate::leanh::lean_dec_ref(v_e_2199_);
                                return v___x_2292_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2279_);
                    crate::leanh::lean_dec_ref(v___y_2278_);
                    v___x_2293_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_2205_);
                    if crate::leanh::lean_obj_tag(v___x_2293_) == 0 {
                        v_a_2294_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                        crate::leanh::lean_inc(v_a_2294_);
                        crate::leanh::lean_dec_ref_known(v___x_2293_, 1);
                        v___x_2295_ = (crate::leanh::lean_unbox(v_a_2294_) as u8);
                        crate::leanh::lean_dec(v_a_2294_);
                        if v___x_2295_ == 0 {
                            crate::leanh::lean_dec(v_declName_2248_);
                            crate::leanh::lean_dec_ref(v_e_2199_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2296_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
                            v___x_2297_ = l_Lean_MessageData_ofName(v_declName_2248_);
                            v___x_2298_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                            crate::leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
                            v___x_2299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
                            v___x_2300_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2298_);
                            crate::leanh::lean_ctor_set(v___x_2300_, 1, v___x_2299_);
                            v___x_2301_ = l_Lean_indentExpr(v_e_2199_);
                            v___x_2302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2302_, 0, v___x_2300_);
                            crate::leanh::lean_ctor_set(v___x_2302_, 1, v___x_2301_);
                            v___x_2303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
                            v___x_2304_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2304_, 0, v___x_2302_);
                            crate::leanh::lean_ctor_set(v___x_2304_, 1, v___x_2303_);
                            v___x_2305_ = l_Lean_Meta_Sym_reportIssue(
                                v___x_2304_,
                                v___y_2205_,
                                v___y_2206_,
                                v___y_2207_,
                                v___y_2208_,
                                v___y_2209_,
                                v___y_2210_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2305_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2305_, 1);
                                state = 1;
                                continue;
                            } else {
                                return v___x_2305_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_2248_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        v_a_2306_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                        v_isSharedCheck_2313_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2293_)) as u8;
                        if v_isSharedCheck_2313_ == 0 {
                            v___x_2308_ = v___x_2293_;
                            v_isShared_2309_ = v_isSharedCheck_2313_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2306_);
                            crate::leanh::lean_dec(v___x_2293_);
                            v___x_2308_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
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
                crate::leanh::lean_dec_ref(v_a_2317_);
                if crate::leanh::lean_obj_tag(v___x_2320_) == 0 {
                    v_a_2321_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                    crate::leanh::lean_inc(v_a_2321_);
                    crate::leanh::lean_dec_ref_known(v___x_2320_, 1);
                    v___x_2322_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_2321_, v___y_2208_);
                    v_a_2323_ = crate::leanh::lean_ctor_get(v___x_2322_, 0);
                    crate::leanh::lean_inc_n(v_a_2323_, 2);
                    crate::leanh::lean_dec_ref(v___x_2322_);
                    crate::leanh::lean_inc(v___y_2210_);
                    crate::leanh::lean_inc_ref(v___y_2209_);
                    crate::leanh::lean_inc(v___y_2208_);
                    crate::leanh::lean_inc_ref(v___y_2207_);
                    v___x_2324_ = lean_infer_type(
                        v_a_2323_,
                        v___y_2207_,
                        v___y_2208_,
                        v___y_2209_,
                        v___y_2210_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2324_) == 0 {
                        v_a_2325_ = crate::leanh::lean_ctor_get(v___x_2324_, 0);
                        crate::leanh::lean_inc(v_a_2325_);
                        crate::leanh::lean_dec_ref_known(v___x_2324_, 1);
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
                        crate::leanh::lean_dec(v_a_2323_);
                        crate::leanh::lean_dec(v_declName_2248_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        v_a_2328_ = crate::leanh::lean_ctor_get(v___x_2324_, 0);
                        v_isSharedCheck_2335_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2324_)) as u8;
                        if v_isSharedCheck_2335_ == 0 {
                            v___x_2330_ = v___x_2324_;
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2328_);
                            crate::leanh::lean_dec(v___x_2324_);
                            v___x_2330_ = crate::leanh::lean_box(0);
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2248_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v_a_2336_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                    v_isSharedCheck_2343_ = (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2343_ == 0 {
                        v___x_2338_ = v___x_2320_;
                        v_isShared_2339_ = v_isSharedCheck_2343_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2336_);
                        crate::leanh::lean_dec(v___x_2320_);
                        v___x_2338_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
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
                    v_reuseFailAlloc_2342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2341_;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v___y_2347_) == 0 {
                    v_a_2348_ = crate::leanh::lean_ctor_get(v___y_2347_, 0);
                    crate::leanh::lean_inc(v_a_2348_);
                    crate::leanh::lean_dec_ref_known(v___y_2347_, 1);
                    v___y_2315_ = v___y_2345_;
                    v___y_2316_ = v___y_2346_;
                    v_a_2317_ = v_a_2348_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2345_);
                    crate::leanh::lean_dec(v_declName_2248_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v_a_2349_ = crate::leanh::lean_ctor_get(v___y_2347_, 0);
                    v_isSharedCheck_2356_ = (!crate::leanh::lean_is_exclusive(v___y_2347_)) as u8;
                    if v_isSharedCheck_2356_ == 0 {
                        v___x_2351_ = v___y_2347_;
                        v_isShared_2352_ = v_isSharedCheck_2356_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2349_);
                        crate::leanh::lean_dec(v___y_2347_);
                        v___x_2351_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
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
                if crate::leanh::lean_obj_tag(v___x_2359_) == 0 {
                    v_a_2360_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
                    crate::leanh::lean_inc(v_a_2360_);
                    crate::leanh::lean_dec_ref_known(v___x_2359_, 1);
                    v___x_2361_ = (crate::leanh::lean_unbox(v_a_2360_) as u8);
                    crate::leanh::lean_dec(v_a_2360_);
                    if v___x_2361_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_2358_);
                        crate::leanh::lean_dec(v_declName_2248_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2362_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once
                            ),
                            _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11,
                        );
                        v___x_2363_ = l_Lean_MessageData_ofName(v_declName_2248_);
                        v___x_2364_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2364_, 0, v___x_2362_);
                        crate::leanh::lean_ctor_set(v___x_2364_, 1, v___x_2363_);
                        v___x_2365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
                        v___x_2366_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2366_, 0, v___x_2364_);
                        crate::leanh::lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                        v___x_2367_ = l_Lean_indentExpr(v_e_2199_);
                        v___x_2368_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2368_, 0, v___x_2366_);
                        crate::leanh::lean_ctor_set(v___x_2368_, 1, v___x_2367_);
                        v___x_2369_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once
                            ),
                            _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15,
                        );
                        v___x_2370_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2370_, 0, v___x_2368_);
                        crate::leanh::lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                        v___x_2371_ = l_Lean_indentExpr(v___y_2358_);
                        v___x_2372_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2372_, 0, v___x_2370_);
                        crate::leanh::lean_ctor_set(v___x_2372_, 1, v___x_2371_);
                        v___x_2373_ = l_Lean_Meta_Sym_reportIssue(
                            v___x_2372_,
                            v___y_2205_,
                            v___y_2206_,
                            v___y_2207_,
                            v___y_2208_,
                            v___y_2209_,
                            v___y_2210_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2373_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2373_, 1);
                            state = 2;
                            continue;
                        } else {
                            return v___x_2373_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2358_);
                    crate::leanh::lean_dec(v_declName_2248_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v_a_2374_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
                    v_isSharedCheck_2381_ = (!crate::leanh::lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2376_ = v___x_2359_;
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2374_);
                        crate::leanh::lean_dec(v___x_2359_);
                        v___x_2376_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2379_;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v___y_2389_) == 0 {
                    v_a_2390_ = crate::leanh::lean_ctor_get(v___y_2389_, 0);
                    crate::leanh::lean_inc(v_a_2390_);
                    crate::leanh::lean_dec_ref_known(v___y_2389_, 1);
                    v___x_2391_ = (crate::leanh::lean_unbox(v_a_2390_) as u8);
                    crate::leanh::lean_dec(v_a_2390_);
                    if v___x_2391_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_2388_);
                        crate::leanh::lean_dec_ref(v___y_2387_);
                        crate::leanh::lean_dec(v_a_2383_);
                        v___y_2358_ = v___y_2385_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2385_);
                        v___x_2392_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2393_ = lean_array_get_size(v___y_2388_);
                        v___x_2394_ =
                            l_Array_toSubarray___redArg(v___y_2388_, v___x_2392_, v___x_2393_);
                        v___x_2395_ = crate::leanh::lean_box(0);
                        v___x_2396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2395_);
                        crate::leanh::lean_ctor_set(v___x_2396_, 1, v___x_2394_);
                        v_sz_2397_ = lean_array_size(v___y_2387_);
                        v___x_2398_ = 0usize;
                        crate::leanh::lean_inc_ref(v_e_2199_);
                        crate::leanh::lean_inc(v_declName_2248_);
                        v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_2248_, v_e_2199_, v___y_2387_, v_sz_2397_, v___x_2398_, v___x_2396_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                        if crate::leanh::lean_obj_tag(v___x_2399_) == 0 {
                            v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                            v_isSharedCheck_2442_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2399_)) as u8;
                            if v_isSharedCheck_2442_ == 0 {
                                v___x_2402_ = v___x_2399_;
                                v_isShared_2403_ = v_isSharedCheck_2442_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2400_);
                                crate::leanh::lean_dec(v___x_2399_);
                                v___x_2402_ = crate::leanh::lean_box(0);
                                v_isShared_2403_ = v_isSharedCheck_2442_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_2387_);
                            crate::leanh::lean_dec(v_a_2383_);
                            crate::leanh::lean_dec(v_declName_2248_);
                            crate::leanh::lean_dec_ref(v_e_2199_);
                            v_a_2443_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                            v_isSharedCheck_2450_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2399_)) as u8;
                            if v_isSharedCheck_2450_ == 0 {
                                v___x_2445_ = v___x_2399_;
                                v_isShared_2446_ = v_isSharedCheck_2450_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2443_);
                                crate::leanh::lean_dec(v___x_2399_);
                                v___x_2445_ = crate::leanh::lean_box(0);
                                v_isShared_2446_ = v_isSharedCheck_2450_;
                                state = 31;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2388_);
                    crate::leanh::lean_dec_ref(v___y_2387_);
                    crate::leanh::lean_dec_ref(v___y_2385_);
                    crate::leanh::lean_dec(v_a_2383_);
                    crate::leanh::lean_dec(v_declName_2248_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v_a_2451_ = crate::leanh::lean_ctor_get(v___y_2389_, 0);
                    v_isSharedCheck_2458_ = (!crate::leanh::lean_is_exclusive(v___y_2389_)) as u8;
                    if v_isSharedCheck_2458_ == 0 {
                        v___x_2453_ = v___y_2389_;
                        v_isShared_2454_ = v_isSharedCheck_2458_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2451_);
                        crate::leanh::lean_dec(v___y_2389_);
                        v___x_2453_ = crate::leanh::lean_box(0);
                        v_isShared_2454_ = v_isSharedCheck_2458_;
                        state = 33;
                        continue;
                    }
                }
            }
            25 => {
                v_fst_2404_ = crate::leanh::lean_ctor_get(v_a_2400_, 0);
                crate::leanh::lean_inc(v_fst_2404_);
                crate::leanh::lean_dec(v_a_2400_);
                if crate::leanh::lean_obj_tag(v_fst_2404_) == 0 {
                    crate::leanh::lean_del_object(v___x_2402_);
                    v___x_2405_ = l_Lean_mkAppN(v_a_2383_, v___y_2387_);
                    v___x_2406_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_2405_, v___y_2208_);
                    v_a_2407_ = crate::leanh::lean_ctor_get(v___x_2406_, 0);
                    crate::leanh::lean_inc(v_a_2407_);
                    crate::leanh::lean_dec_ref(v___x_2406_);
                    crate::leanh::lean_inc_ref(v_e_2199_);
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
                    if crate::leanh::lean_obj_tag(v___x_2408_) == 0 {
                        v_a_2409_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                        crate::leanh::lean_inc(v_a_2409_);
                        crate::leanh::lean_dec_ref_known(v___x_2408_, 1);
                        v___x_2410_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_2205_);
                        if crate::leanh::lean_obj_tag(v___x_2410_) == 0 {
                            v_a_2411_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                            crate::leanh::lean_inc(v_a_2411_);
                            crate::leanh::lean_dec_ref_known(v___x_2410_, 1);
                            v___x_2412_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once), _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
                            crate::leanh::lean_inc_ref(v_e_2199_);
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
                                crate::leanh::lean_dec_ref(v___y_2387_);
                                v___y_2315_ = v___x_2413_;
                                v___y_2316_ = v___y_2386_;
                                v_a_2317_ = v___x_2415_;
                                state = 13;
                                continue;
                            } else {
                                v___x_2417_ = lean_nat_dec_le(v___x_2414_, v___x_2414_);
                                if v___x_2417_ == 0 {
                                    if v___x_2416_ == 0 {
                                        crate::leanh::lean_dec_ref(v___y_2387_);
                                        v___y_2315_ = v___x_2413_;
                                        v___y_2316_ = v___y_2386_;
                                        v_a_2317_ = v___x_2415_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___x_2418_ = lean_usize_of_nat(v___x_2414_);
                                        v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_2387_, v___x_2398_, v___x_2418_, v___x_2415_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                                        crate::leanh::lean_dec_ref(v___y_2387_);
                                        v___y_2345_ = v___x_2413_;
                                        v___y_2346_ = v___y_2386_;
                                        v___y_2347_ = v___x_2419_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_2420_ = lean_usize_of_nat(v___x_2414_);
                                    v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_2387_, v___x_2398_, v___x_2420_, v___x_2415_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                                    crate::leanh::lean_dec_ref(v___y_2387_);
                                    v___y_2345_ = v___x_2413_;
                                    v___y_2346_ = v___y_2386_;
                                    v___y_2347_ = v___x_2421_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2409_);
                            crate::leanh::lean_dec(v_a_2407_);
                            crate::leanh::lean_dec_ref(v___y_2387_);
                            crate::leanh::lean_dec(v_declName_2248_);
                            crate::leanh::lean_dec_ref(v_e_2199_);
                            v_a_2422_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                            v_isSharedCheck_2429_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2429_ == 0 {
                                v___x_2424_ = v___x_2410_;
                                v_isShared_2425_ = v_isSharedCheck_2429_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2422_);
                                crate::leanh::lean_dec(v___x_2410_);
                                v___x_2424_ = crate::leanh::lean_box(0);
                                v_isShared_2425_ = v_isSharedCheck_2429_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2407_);
                        crate::leanh::lean_dec_ref(v___y_2387_);
                        crate::leanh::lean_dec(v_declName_2248_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        v_a_2430_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                        v_isSharedCheck_2437_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2408_)) as u8;
                        if v_isSharedCheck_2437_ == 0 {
                            v___x_2432_ = v___x_2408_;
                            v_isShared_2433_ = v_isSharedCheck_2437_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2430_);
                            crate::leanh::lean_dec(v___x_2408_);
                            v___x_2432_ = crate::leanh::lean_box(0);
                            v_isShared_2433_ = v_isSharedCheck_2437_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2387_);
                    crate::leanh::lean_dec(v_a_2383_);
                    crate::leanh::lean_dec(v_declName_2248_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    v_val_2438_ = crate::leanh::lean_ctor_get(v_fst_2404_, 0);
                    crate::leanh::lean_inc(v_val_2438_);
                    crate::leanh::lean_dec_ref_known(v_fst_2404_, 1);
                    if v_isShared_2403_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2402_, 0, v_val_2438_);
                        v___x_2440_ = v___x_2402_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_2441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_val_2438_);
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
                    v_reuseFailAlloc_2428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
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
                    v_reuseFailAlloc_2436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
                    v_reuseFailAlloc_2449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
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
                    v_reuseFailAlloc_2457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
                    v___x_2456_ = v_reuseFailAlloc_2457_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2456_;
            }
            35 => {
                v_snd_2461_ = crate::leanh::lean_ctor_get(v_a_2460_, 1);
                crate::leanh::lean_inc(v_snd_2461_);
                v_fst_2462_ = crate::leanh::lean_ctor_get(v_a_2460_, 0);
                crate::leanh::lean_inc(v_fst_2462_);
                crate::leanh::lean_dec_ref(v_a_2460_);
                v_fst_2463_ = crate::leanh::lean_ctor_get(v_snd_2461_, 0);
                crate::leanh::lean_inc(v_fst_2463_);
                v_snd_2464_ = crate::leanh::lean_ctor_get(v_snd_2461_, 1);
                crate::leanh::lean_inc_n(v_snd_2464_, 2);
                crate::leanh::lean_dec(v_snd_2461_);
                v___x_2465_ = l_Lean_Expr_cleanupAnnotations(v_snd_2464_);
                v___x_2466_ = l_Lean_Expr_isApp(v___x_2465_);
                if v___x_2466_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2465_);
                    crate::leanh::lean_dec(v_snd_2464_);
                    crate::leanh::lean_dec(v_fst_2463_);
                    crate::leanh::lean_dec(v_fst_2462_);
                    crate::leanh::lean_dec(v_a_2383_);
                    crate::leanh::lean_dec(v_declName_2248_);
                    crate::leanh::lean_dec_ref(v_arg_2244_);
                    crate::leanh::lean_dec_ref(v_arg_2241_);
                    crate::leanh::lean_dec_ref(v_arg_2238_);
                    crate::leanh::lean_dec_ref(v_e_2199_);
                    state = 3;
                    continue;
                } else {
                    v_arg_2467_ = crate::leanh::lean_ctor_get(v___x_2465_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2467_);
                    v___x_2468_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2465_);
                    v___x_2469_ = l_Lean_Expr_isApp(v___x_2468_);
                    if v___x_2469_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2468_);
                        crate::leanh::lean_dec_ref(v_arg_2467_);
                        crate::leanh::lean_dec(v_snd_2464_);
                        crate::leanh::lean_dec(v_fst_2463_);
                        crate::leanh::lean_dec(v_fst_2462_);
                        crate::leanh::lean_dec(v_a_2383_);
                        crate::leanh::lean_dec(v_declName_2248_);
                        crate::leanh::lean_dec_ref(v_arg_2244_);
                        crate::leanh::lean_dec_ref(v_arg_2241_);
                        crate::leanh::lean_dec_ref(v_arg_2238_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_2470_ = crate::leanh::lean_ctor_get(v___x_2468_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2470_);
                        v___x_2471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2468_);
                        v___x_2472_ = l_Lean_Expr_isApp(v___x_2471_);
                        if v___x_2472_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2471_);
                            crate::leanh::lean_dec_ref(v_arg_2470_);
                            crate::leanh::lean_dec_ref(v_arg_2467_);
                            crate::leanh::lean_dec(v_snd_2464_);
                            crate::leanh::lean_dec(v_fst_2463_);
                            crate::leanh::lean_dec(v_fst_2462_);
                            crate::leanh::lean_dec(v_a_2383_);
                            crate::leanh::lean_dec(v_declName_2248_);
                            crate::leanh::lean_dec_ref(v_arg_2244_);
                            crate::leanh::lean_dec_ref(v_arg_2241_);
                            crate::leanh::lean_dec_ref(v_arg_2238_);
                            crate::leanh::lean_dec_ref(v_e_2199_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_2473_ = crate::leanh::lean_ctor_get(v___x_2471_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2473_);
                            v___x_2474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2471_);
                            v___x_2475_ = l_Lean_Expr_isConstOf(v___x_2474_, v___x_2246_);
                            crate::leanh::lean_dec_ref(v___x_2474_);
                            if v___x_2475_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2473_);
                                crate::leanh::lean_dec_ref(v_arg_2470_);
                                crate::leanh::lean_dec_ref(v_arg_2467_);
                                crate::leanh::lean_dec(v_snd_2464_);
                                crate::leanh::lean_dec(v_fst_2463_);
                                crate::leanh::lean_dec(v_fst_2462_);
                                crate::leanh::lean_dec(v_a_2383_);
                                crate::leanh::lean_dec(v_declName_2248_);
                                crate::leanh::lean_dec_ref(v_arg_2244_);
                                crate::leanh::lean_dec_ref(v_arg_2241_);
                                crate::leanh::lean_dec_ref(v_arg_2238_);
                                crate::leanh::lean_dec_ref(v_e_2199_);
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
                                if crate::leanh::lean_obj_tag(v___x_2476_) == 0 {
                                    v_a_2477_ = crate::leanh::lean_ctor_get(v___x_2476_, 0);
                                    crate::leanh::lean_inc(v_a_2477_);
                                    v___x_2478_ = (crate::leanh::lean_unbox(v_a_2477_) as u8);
                                    crate::leanh::lean_dec(v_a_2477_);
                                    if v___x_2478_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_2470_);
                                        crate::leanh::lean_dec_ref(v_arg_2467_);
                                        crate::leanh::lean_dec_ref(v_arg_2241_);
                                        crate::leanh::lean_dec_ref(v_arg_2238_);
                                        v___y_2385_ = v_snd_2464_;
                                        v___y_2386_ = v___x_2475_;
                                        v___y_2387_ = v_fst_2462_;
                                        v___y_2388_ = v_fst_2463_;
                                        v___y_2389_ = v___x_2476_;
                                        state = 24;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_2476_, 1);
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
                                        if crate::leanh::lean_obj_tag(v___x_2479_) == 0 {
                                            v_a_2480_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                                            crate::leanh::lean_inc(v_a_2480_);
                                            crate::leanh::lean_dec_ref_known(v___x_2479_, 1);
                                            v___x_2481_ =
                                                (crate::leanh::lean_unbox(v_a_2480_) as u8);
                                            crate::leanh::lean_dec(v_a_2480_);
                                            if v___x_2481_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_2467_);
                                                crate::leanh::lean_dec(v_fst_2463_);
                                                crate::leanh::lean_dec(v_fst_2462_);
                                                crate::leanh::lean_dec(v_a_2383_);
                                                crate::leanh::lean_dec_ref(v_arg_2238_);
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
                                            crate::leanh::lean_dec_ref(v_arg_2467_);
                                            crate::leanh::lean_dec(v_snd_2464_);
                                            crate::leanh::lean_dec(v_fst_2463_);
                                            crate::leanh::lean_dec(v_fst_2462_);
                                            crate::leanh::lean_dec(v_a_2383_);
                                            crate::leanh::lean_dec(v_declName_2248_);
                                            crate::leanh::lean_dec_ref(v_arg_2238_);
                                            crate::leanh::lean_dec_ref(v_e_2199_);
                                            v_a_2483_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                                            v_isSharedCheck_2490_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2479_))
                                                    as u8;
                                            if v_isSharedCheck_2490_ == 0 {
                                                v___x_2485_ = v___x_2479_;
                                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                                state = 36;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2483_);
                                                crate::leanh::lean_dec(v___x_2479_);
                                                v___x_2485_ = crate::leanh::lean_box(0);
                                                v_isShared_2486_ = v_isSharedCheck_2490_;
                                                state = 36;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2470_);
                                    crate::leanh::lean_dec_ref(v_arg_2467_);
                                    crate::leanh::lean_dec_ref(v_arg_2241_);
                                    crate::leanh::lean_dec_ref(v_arg_2238_);
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
                    v_reuseFailAlloc_2489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
                    v___x_2488_ = v_reuseFailAlloc_2489_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2488_;
            }
            38 => {
                v_trackZetaDelta_2515_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2516_ = crate::leanh::lean_ctor_get(v___y_2207_, 1);
                v_lctx_2517_ = crate::leanh::lean_ctor_get(v___y_2207_, 2);
                v_localInstances_2518_ = crate::leanh::lean_ctor_get(v___y_2207_, 3);
                v_defEqCtx_x3f_2519_ = crate::leanh::lean_ctor_get(v___y_2207_, 4);
                v_synthPendingDepth_2520_ = crate::leanh::lean_ctor_get(v___y_2207_, 5);
                v_canUnfold_x3f_2521_ = crate::leanh::lean_ctor_get(v___y_2207_, 6);
                v_univApprox_2522_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2523_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2524_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2525_ = 1;
                if v_isShared_2514_ == 0 {
                    v_config_2527_ = v___x_2513_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2549_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        0 as u32,
                        v_foApprox_2494_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        1 as u32,
                        v_ctxApprox_2495_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        2 as u32,
                        v_quasiPatternApprox_2496_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        3 as u32,
                        v_constApprox_2497_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        4 as u32,
                        v_isDefEqStuckEx_2498_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        5 as u32,
                        v_unificationHints_2499_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        6 as u32,
                        v_proofIrrelevance_2500_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        7 as u32,
                        v_assignSyntheticOpaque_2501_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        8 as u32,
                        v_offsetCnstrs_2502_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        10 as u32,
                        v_etaStruct_2503_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        11 as u32,
                        v_univApprox_2504_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        12 as u32,
                        v_iota_2505_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        13 as u32,
                        v_beta_2506_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        14 as u32,
                        v_proj_2507_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        15 as u32,
                        v_zeta_2508_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        16 as u32,
                        v_zetaDelta_2509_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2549_,
                        17 as u32,
                        v_zetaUnused_2510_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
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
                crate::leanh::lean_ctor_set_uint8(v_config_2527_, 9 as u32, v___x_2525_);
                v___x_2528_ = l_Lean_Meta_Context_configKey(v___y_2207_);
                v___x_2529_ = 3u64;
                v___x_2530_ = lean_uint64_shift_right(v___x_2528_, v___x_2529_);
                v___x_2531_ = crate::leanh::lean_box(0);
                v___x_2532_ = 0;
                v___x_2533_ = lean_uint64_shift_left(v___x_2530_, v___x_2529_);
                v___x_2534_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once
                    ),
                    _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21,
                );
                v_key_2535_ = lean_uint64_lor(v___x_2533_, v___x_2534_);
                v___x_2536_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2536_, 0, v_config_2527_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2536_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2535_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2521_);
                crate::leanh::lean_inc(v_synthPendingDepth_2520_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2519_);
                crate::leanh::lean_inc_ref(v_localInstances_2518_);
                crate::leanh::lean_inc_ref(v_lctx_2517_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2516_);
                v___x_2537_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2536_);
                crate::leanh::lean_ctor_set(v___x_2537_, 1, v_zetaDeltaSet_2516_);
                crate::leanh::lean_ctor_set(v___x_2537_, 2, v_lctx_2517_);
                crate::leanh::lean_ctor_set(v___x_2537_, 3, v_localInstances_2518_);
                crate::leanh::lean_ctor_set(v___x_2537_, 4, v_defEqCtx_x3f_2519_);
                crate::leanh::lean_ctor_set(v___x_2537_, 5, v_synthPendingDepth_2520_);
                crate::leanh::lean_ctor_set(v___x_2537_, 6, v_canUnfold_x3f_2521_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2515_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2522_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2523_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
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
                crate::leanh::lean_dec_ref_known(v___x_2537_, 7);
                if crate::leanh::lean_obj_tag(v___x_2538_) == 0 {
                    v_a_2539_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
                    crate::leanh::lean_inc(v_a_2539_);
                    crate::leanh::lean_dec_ref_known(v___x_2538_, 1);
                    v_a_2460_ = v_a_2539_;
                    state = 35;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2538_) == 0 {
                        v_a_2540_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
                        crate::leanh::lean_inc(v_a_2540_);
                        crate::leanh::lean_dec_ref_known(v___x_2538_, 1);
                        v_a_2460_ = v_a_2540_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2383_);
                        crate::leanh::lean_dec(v_declName_2248_);
                        crate::leanh::lean_dec_ref(v_arg_2244_);
                        crate::leanh::lean_dec_ref(v_arg_2241_);
                        crate::leanh::lean_dec_ref(v_arg_2238_);
                        crate::leanh::lean_dec_ref(v_e_2199_);
                        v_a_2541_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
                        v_isSharedCheck_2548_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2538_)) as u8;
                        if v_isSharedCheck_2548_ == 0 {
                            v___x_2543_ = v___x_2538_;
                            v_isShared_2544_ = v_isSharedCheck_2548_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2541_);
                            crate::leanh::lean_dec(v___x_2538_);
                            v___x_2543_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
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
                    v_reuseFailAlloc_2557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
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
                    v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
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
                    v_reuseFailAlloc_2574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
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
                    v_reuseFailAlloc_2582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
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
    mut v_e_2584_: *mut crate::leanh::LeanObject,
    mut v_thm_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2595_);
    crate::leanh::lean_dec_ref(v___y_2594_);
    crate::leanh::lean_dec(v___y_2593_);
    crate::leanh::lean_dec_ref(v___y_2592_);
    crate::leanh::lean_dec(v___y_2591_);
    crate::leanh::lean_dec_ref(v___y_2590_);
    crate::leanh::lean_dec(v___y_2589_);
    crate::leanh::lean_dec_ref(v___y_2588_);
    crate::leanh::lean_dec(v___y_2587_);
    crate::leanh::lean_dec(v___y_2586_);
    return v_res_2597_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem(
    mut v_thm_2598_: *mut crate::leanh::LeanObject,
    mut v_e_2599_: *mut crate::leanh::LeanObject,
    mut v_a_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_a_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2611_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed as *mut core::ffi::c_void,
        13,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2611_, 0, v_e_2599_);
    crate::leanh::lean_closure_set(v___f_2611_, 1, v_thm_2598_);
    v___x_2612_ = 0;
    v___x_2613_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_2611_, v___x_2612_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
    return v___x_2613_;
}
pub unsafe fn l_Lean_Meta_Grind_instantiateExtTheorem___boxed(
    mut v_thm_2614_: *mut crate::leanh::LeanObject,
    mut v_e_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2625_);
    crate::leanh::lean_dec_ref(v_a_2624_);
    crate::leanh::lean_dec(v_a_2623_);
    crate::leanh::lean_dec_ref(v_a_2622_);
    crate::leanh::lean_dec(v_a_2621_);
    crate::leanh::lean_dec_ref(v_a_2620_);
    crate::leanh::lean_dec(v_a_2619_);
    crate::leanh::lean_dec_ref(v_a_2618_);
    crate::leanh::lean_dec(v_a_2617_);
    crate::leanh::lean_dec(v_a_2616_);
    return v_res_2627_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(
    mut v_mvarId_2628_: *mut crate::leanh::LeanObject,
    mut v_val_2629_: *mut crate::leanh::LeanObject,
    mut v___y_2630_: *mut crate::leanh::LeanObject,
    mut v___y_2631_: *mut crate::leanh::LeanObject,
    mut v___y_2632_: *mut crate::leanh::LeanObject,
    mut v___y_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
    mut v___y_2639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ =
        l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(
            v_mvarId_2628_,
            v_val_2629_,
            v___y_2637_,
        );
    return v___x_2641_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(
    mut v_mvarId_2642_: *mut crate::leanh::LeanObject,
    mut v_val_2643_: *mut crate::leanh::LeanObject,
    mut v___y_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
    mut v___y_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2653_);
    crate::leanh::lean_dec_ref(v___y_2652_);
    crate::leanh::lean_dec(v___y_2651_);
    crate::leanh::lean_dec_ref(v___y_2650_);
    crate::leanh::lean_dec(v___y_2649_);
    crate::leanh::lean_dec_ref(v___y_2648_);
    crate::leanh::lean_dec(v___y_2647_);
    crate::leanh::lean_dec_ref(v___y_2646_);
    crate::leanh::lean_dec(v___y_2645_);
    crate::leanh::lean_dec(v___y_2644_);
    return v_res_2655_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(
    mut v_mvarId_2656_: *mut crate::leanh::LeanObject,
    mut v___y_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(
            v_mvarId_2656_,
            v___y_2664_,
        );
    return v___x_2668_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(
    mut v_mvarId_2669_: *mut crate::leanh::LeanObject,
    mut v___y_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
    mut v___y_2673_: *mut crate::leanh::LeanObject,
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
    mut v___y_2678_: *mut crate::leanh::LeanObject,
    mut v___y_2679_: *mut crate::leanh::LeanObject,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2679_);
    crate::leanh::lean_dec_ref(v___y_2678_);
    crate::leanh::lean_dec(v___y_2677_);
    crate::leanh::lean_dec_ref(v___y_2676_);
    crate::leanh::lean_dec(v___y_2675_);
    crate::leanh::lean_dec_ref(v___y_2674_);
    crate::leanh::lean_dec(v___y_2673_);
    crate::leanh::lean_dec_ref(v___y_2672_);
    crate::leanh::lean_dec(v___y_2671_);
    crate::leanh::lean_dec(v___y_2670_);
    crate::leanh::lean_dec(v_mvarId_2669_);
    return v_res_2681_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(
    mut v_cls_2682_: *mut crate::leanh::LeanObject,
    mut v_msg_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
    mut v___y_2688_: *mut crate::leanh::LeanObject,
    mut v___y_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cls_2696_: *mut crate::leanh::LeanObject,
    mut v_msg_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
    mut v___y_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2707_);
    crate::leanh::lean_dec_ref(v___y_2706_);
    crate::leanh::lean_dec(v___y_2705_);
    crate::leanh::lean_dec_ref(v___y_2704_);
    crate::leanh::lean_dec(v___y_2703_);
    crate::leanh::lean_dec_ref(v___y_2702_);
    crate::leanh::lean_dec(v___y_2701_);
    crate::leanh::lean_dec_ref(v___y_2700_);
    crate::leanh::lean_dec(v___y_2699_);
    crate::leanh::lean_dec(v___y_2698_);
    return v_res_2709_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(
    mut v_00_u03b2_2710_: *mut crate::leanh::LeanObject,
    mut v_x_2711_: *mut crate::leanh::LeanObject,
    mut v_x_2712_: *mut crate::leanh::LeanObject,
    mut v_x_2713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_2711_, v_x_2712_, v_x_2713_);
    return v___x_2714_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(
    mut v_00_u03b2_2715_: *mut crate::leanh::LeanObject,
    mut v_x_2716_: *mut crate::leanh::LeanObject,
    mut v_x_2717_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2718_: u8 = 0;
    v___x_2718_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_2716_, v_x_2717_);
    return v___x_2718_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(
    mut v_00_u03b2_2719_: *mut crate::leanh::LeanObject,
    mut v_x_2720_: *mut crate::leanh::LeanObject,
    mut v_x_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2722_: u8 = 0;
    let mut v_r_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_2719_, v_x_2720_, v_x_2721_);
    crate::leanh::lean_dec(v_x_2721_);
    crate::leanh::lean_dec_ref(v_x_2720_);
    v_r_2723_ = crate::leanh::lean_box((v_res_2722_) as usize);
    return v_r_2723_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(
    mut v_00_u03b2_2724_: *mut crate::leanh::LeanObject,
    mut v_x_2725_: *mut crate::leanh::LeanObject,
    mut v_x_2726_: usize,
    mut v_x_2727_: usize,
    mut v_x_2728_: *mut crate::leanh::LeanObject,
    mut v_x_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_2725_, v_x_2726_, v_x_2727_, v_x_2728_, v_x_2729_);
    return v___x_2730_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_2731_: *mut crate::leanh::LeanObject,
    mut v_x_2732_: *mut crate::leanh::LeanObject,
    mut v_x_2733_: *mut crate::leanh::LeanObject,
    mut v_x_2734_: *mut crate::leanh::LeanObject,
    mut v_x_2735_: *mut crate::leanh::LeanObject,
    mut v_x_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_217077__boxed_2737_: usize = 0;
    let mut v_x_217078__boxed_2738_: usize = 0;
    let mut v_res_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_217077__boxed_2737_ = crate::leanh::lean_unbox_usize(v_x_2733_);
    crate::leanh::lean_dec(v_x_2733_);
    v_x_217078__boxed_2738_ = crate::leanh::lean_unbox_usize(v_x_2734_);
    crate::leanh::lean_dec(v_x_2734_);
    v_res_2739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_2731_, v_x_2732_, v_x_217077__boxed_2737_, v_x_217078__boxed_2738_, v_x_2735_, v_x_2736_);
    return v_res_2739_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(
    mut v_00_u03b2_2740_: *mut crate::leanh::LeanObject,
    mut v_x_2741_: *mut crate::leanh::LeanObject,
    mut v_x_2742_: usize,
    mut v_x_2743_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2744_: u8 = 0;
    v___x_2744_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_2741_, v_x_2742_, v_x_2743_);
    return v___x_2744_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_2745_: *mut crate::leanh::LeanObject,
    mut v_x_2746_: *mut crate::leanh::LeanObject,
    mut v_x_2747_: *mut crate::leanh::LeanObject,
    mut v_x_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_217094__boxed_2749_: usize = 0;
    let mut v_res_2750_: u8 = 0;
    let mut v_r_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_217094__boxed_2749_ = crate::leanh::lean_unbox_usize(v_x_2747_);
    crate::leanh::lean_dec(v_x_2747_);
    v_res_2750_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_2745_, v_x_2746_, v_x_217094__boxed_2749_, v_x_2748_);
    crate::leanh::lean_dec(v_x_2748_);
    crate::leanh::lean_dec_ref(v_x_2746_);
    v_r_2751_ = crate::leanh::lean_box((v_res_2750_) as usize);
    return v_r_2751_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(
    mut v_00_u03b2_2752_: *mut crate::leanh::LeanObject,
    mut v_n_2753_: *mut crate::leanh::LeanObject,
    mut v_k_2754_: *mut crate::leanh::LeanObject,
    mut v_v_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_2753_, v_k_2754_, v_v_2755_);
    return v___x_2756_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(
    mut v_00_u03b2_2757_: *mut crate::leanh::LeanObject,
    mut v_depth_2758_: usize,
    mut v_keys_2759_: *mut crate::leanh::LeanObject,
    mut v_vals_2760_: *mut crate::leanh::LeanObject,
    mut v_heq_2761_: *mut crate::leanh::LeanObject,
    mut v_i_2762_: *mut crate::leanh::LeanObject,
    mut v_entries_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_2758_, v_keys_2759_, v_vals_2760_, v_i_2762_, v_entries_2763_);
    return v___x_2764_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(
    mut v_00_u03b2_2765_: *mut crate::leanh::LeanObject,
    mut v_depth_2766_: *mut crate::leanh::LeanObject,
    mut v_keys_2767_: *mut crate::leanh::LeanObject,
    mut v_vals_2768_: *mut crate::leanh::LeanObject,
    mut v_heq_2769_: *mut crate::leanh::LeanObject,
    mut v_i_2770_: *mut crate::leanh::LeanObject,
    mut v_entries_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2772_: usize = 0;
    let mut v_res_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2772_ = crate::leanh::lean_unbox_usize(v_depth_2766_);
    crate::leanh::lean_dec(v_depth_2766_);
    v_res_2773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2765_, v_depth_boxed_2772_, v_keys_2767_, v_vals_2768_, v_heq_2769_, v_i_2770_, v_entries_2771_);
    crate::leanh::lean_dec_ref(v_vals_2768_);
    crate::leanh::lean_dec_ref(v_keys_2767_);
    return v_res_2773_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(
    mut v_00_u03b2_2774_: *mut crate::leanh::LeanObject,
    mut v_keys_2775_: *mut crate::leanh::LeanObject,
    mut v_vals_2776_: *mut crate::leanh::LeanObject,
    mut v_heq_2777_: *mut crate::leanh::LeanObject,
    mut v_i_2778_: *mut crate::leanh::LeanObject,
    mut v_k_2779_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2780_: u8 = 0;
    v___x_2780_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_2775_, v_i_2778_, v_k_2779_);
    return v___x_2780_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(
    mut v_00_u03b2_2781_: *mut crate::leanh::LeanObject,
    mut v_keys_2782_: *mut crate::leanh::LeanObject,
    mut v_vals_2783_: *mut crate::leanh::LeanObject,
    mut v_heq_2784_: *mut crate::leanh::LeanObject,
    mut v_i_2785_: *mut crate::leanh::LeanObject,
    mut v_k_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2787_: u8 = 0;
    let mut v_r_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_2781_, v_keys_2782_, v_vals_2783_, v_heq_2784_, v_i_2785_, v_k_2786_);
    crate::leanh::lean_dec(v_k_2786_);
    crate::leanh::lean_dec_ref(v_vals_2783_);
    crate::leanh::lean_dec_ref(v_keys_2782_);
    v_r_2788_ = crate::leanh::lean_box((v_res_2787_) as usize);
    return v_r_2788_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(
    mut v_00_u03b2_2789_: *mut crate::leanh::LeanObject,
    mut v_x_2790_: *mut crate::leanh::LeanObject,
    mut v_x_2791_: *mut crate::leanh::LeanObject,
    mut v_x_2792_: *mut crate::leanh::LeanObject,
    mut v_x_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_2790_, v_x_2791_, v_x_2792_, v_x_2793_);
    return v___x_2794_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Ext(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Ext(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Ext(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
}
